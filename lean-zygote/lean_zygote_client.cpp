#include <cerrno>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <limits.h>
#include <signal.h>
#include <string>
#include <sys/socket.h>
#include <sys/un.h>
#include <unistd.h>
#include <vector>

namespace {

constexpr uint32_t kProtoMagic = 0x4C5A5947u; // "LZYG"

void fallback_exec(char** argv) {
    const char* lean_bin = std::getenv("LEAN_BIN");
    if (!lean_bin || !*lean_bin) lean_bin = "lean";
    execvp(lean_bin, argv);
    _exit(127);
}

void append_u32(std::vector<uint8_t>& buf, uint32_t v) {
    const uint8_t* p = reinterpret_cast<const uint8_t*>(&v);
    buf.insert(buf.end(), p, p + sizeof(v));
}

void append_str(std::vector<uint8_t>& buf, const std::string& s) {
    append_u32(buf, static_cast<uint32_t>(s.size()));
    buf.insert(buf.end(), s.begin(), s.end());
}

bool read_exact(int fd, void* dst, size_t n) {
    uint8_t* p = static_cast<uint8_t*>(dst);
    size_t got = 0;
    while (got < n) {
        ssize_t r = recv(fd, p + got, n - got, 0);
        if (r == 0) return false;
        if (r < 0) {
            if (errno == EINTR) continue;
            return false;
        }
        got += static_cast<size_t>(r);
    }
    return true;
}

std::string env_or_empty(const char* name) {
    const char* v = std::getenv(name);
    return v ? std::string(v) : std::string();
}

} // namespace

int main(int argc, char** argv) {
    signal(SIGPIPE, SIG_IGN);

    const char* disable = std::getenv("LEAN_ZYGOTE_DISABLE");
    if (disable && std::strcmp(disable, "1") == 0) {
        fallback_exec(argv);
    }

    const char* sock_env = std::getenv("LEAN_ZYGOTE_SOCK");
    std::string sock_path = (sock_env && *sock_env) ? std::string(sock_env) : std::string("/tmp/lean-zygote.sock");
    if (sock_path.size() >= sizeof(sockaddr_un::sun_path)) {
        fallback_exec(argv);
    }

    int fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (fd < 0) fallback_exec(argv);

    struct sockaddr_un addr {};
    addr.sun_family = AF_UNIX;
    std::strncpy(addr.sun_path, sock_path.c_str(), sizeof(addr.sun_path) - 1);
    if (connect(fd, reinterpret_cast<struct sockaddr*>(&addr), sizeof(addr)) < 0) {
        close(fd);
        fallback_exec(argv);
    }

    char cwd_buf[PATH_MAX];
    std::string cwd = getcwd(cwd_buf, sizeof(cwd_buf)) ? std::string(cwd_buf) : std::string();

    std::vector<uint8_t> payload;
    payload.reserve(4096);
    append_u32(payload, kProtoMagic);
    append_u32(payload, static_cast<uint32_t>(argc > 1 ? argc - 1 : 0));
    append_str(payload, cwd);
    append_str(payload, env_or_empty("LEAN_PATH"));
    append_str(payload, env_or_empty("LEAN_SRC_PATH"));
    append_str(payload, env_or_empty("LEAN_NUM_THREADS"));
    append_str(payload, env_or_empty("LEAN_THREAD_STACK_SIZE"));
    for (int i = 1; i < argc; ++i) {
        append_str(payload, argv[i]);
    }

    int fds[2] = {STDOUT_FILENO, STDERR_FILENO};
    char cmsg_buf[CMSG_SPACE(sizeof(fds))] {};
    struct iovec iov {};
    iov.iov_base = payload.data();
    iov.iov_len = payload.size();

    struct msghdr msg {};
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    msg.msg_control = cmsg_buf;
    msg.msg_controllen = sizeof(cmsg_buf);

    struct cmsghdr* cmsg = CMSG_FIRSTHDR(&msg);
    cmsg->cmsg_level = SOL_SOCKET;
    cmsg->cmsg_type = SCM_RIGHTS;
    cmsg->cmsg_len = CMSG_LEN(sizeof(fds));
    std::memcpy(CMSG_DATA(cmsg), fds, sizeof(fds));

    ssize_t sent;
    do {
        sent = sendmsg(fd, &msg, MSG_NOSIGNAL);
    } while (sent < 0 && errno == EINTR);
    if (sent <= 0) {
        close(fd);
        fallback_exec(argv);
    }

    size_t offset = static_cast<size_t>(sent);
    while (offset < payload.size()) {
        ssize_t w = send(fd, payload.data() + offset, payload.size() - offset, MSG_NOSIGNAL);
        if (w < 0) {
            if (errno == EINTR) continue;
            close(fd);
            fallback_exec(argv);
        }
        offset += static_cast<size_t>(w);
    }

    uint8_t status = 0;
    if (!read_exact(fd, &status, 1) || status == 'F') {
        close(fd);
        fallback_exec(argv);
    }
    if (status != 'R') {
        close(fd);
        fallback_exec(argv);
    }

    uint8_t resp[5] = {};
    if (!read_exact(fd, resp, sizeof(resp)) || resp[0] != 'X') {
        close(fd);
        return 1;
    }

    int32_t rc = 1;
    std::memcpy(&rc, resp + 1, sizeof(rc));
    close(fd);
    return rc;
}
