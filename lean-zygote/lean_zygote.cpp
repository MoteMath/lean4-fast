#include <lean/lean.h>

#include <algorithm>
#include <arpa/inet.h>
#include <cerrno>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <dlfcn.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <string>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <thread>
#include <unistd.h>
#include <vector>

extern "C" {
void lean_initialize(void);
void lean_initialize_thread(void);
void lean_finalize_thread(void);
lean_object* initialize_LeanZygoteShim(uint8_t builtin);

lean_object* lean_zygote_preload(
    lean_object* sysroot,
    lean_object* imports_csv,
    lean_object* header_file_opt,
    lean_object* setup_file_opt,
    uint8_t is_module);

lean_object* lean_zygote_select_snapshot(
    lean_object* snaps,
    lean_object* cwd,
    lean_object* lean_path,
    lean_object* argv);

lean_object* lean_zygote_select_snapshot_meta(
    lean_object* metas,
    lean_object* cwd,
    lean_object* lean_path,
    lean_object* argv);

lean_object* lean_zygote_snapshot_meta_json(lean_object* snap);

lean_object* lean_zygote_parse_snapshot_metas(lean_object* jsons);

lean_object* lean_zygote_can_reuse(
    lean_object* snap,
    lean_object* cwd,
    lean_object* lean_path,
    lean_object* argv);

lean_object* lean_zygote_can_run_clean(
    lean_object* cwd,
    lean_object* lean_path,
    lean_object* argv);

lean_object* lean_zygote_run_child(
    lean_object* snap,
    lean_object* sysroot,
    lean_object* lean_path,
    lean_object* argv);

lean_object* lean_zygote_run_clean_child(
    lean_object* sysroot,
    lean_object* lean_path,
    lean_object* argv);

lean_object* lean_zygote_snapshot_summary(lean_object* snap);
}

namespace {

constexpr uint32_t kProtoMagic = 0x4C5A5947u;       // "LZYG"
constexpr uint32_t kHelperProtoMagic = 0x4C5A4831u; // "LZH1"
constexpr uint32_t kNoSnapshot = 0xFFFFFFFFu;
volatile sig_atomic_t g_stop_requested = 0;
std::string g_sock_path;

void handle_sigterm(int) {
    g_stop_requested = 1;
}

void handle_sigchld(int) {
    int saved = errno;
    while (waitpid(-1, nullptr, WNOHANG) > 0) {}
    errno = saved;
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

bool write_exact(int fd, const void* src, size_t n) {
    const uint8_t* p = static_cast<const uint8_t*>(src);
    size_t sent = 0;
    while (sent < n) {
        ssize_t w = send(fd, p + sent, n - sent, MSG_NOSIGNAL);
        if (w < 0) {
            if (errno == EINTR) continue;
            return false;
        }
        sent += static_cast<size_t>(w);
    }
    return true;
}

void append_u32(std::vector<uint8_t>& buf, uint32_t v) {
    const uint8_t* p = reinterpret_cast<const uint8_t*>(&v);
    buf.insert(buf.end(), p, p + sizeof(v));
}

void append_str(std::vector<uint8_t>& buf, const std::string& s) {
    append_u32(buf, static_cast<uint32_t>(s.size()));
    buf.insert(buf.end(), s.begin(), s.end());
}

struct CompileRequest {
    std::string cwd;
    std::string lean_path;
    std::string lean_src_path;
    std::string lean_num_threads;
    std::string lean_tstack;
    std::vector<std::string> argv;
    int stdout_fd = -1;
    int stderr_fd = -1;

    ~CompileRequest() {
        if (stdout_fd >= 0) close(stdout_fd);
        if (stderr_fd >= 0) close(stderr_fd);
    }
};

bool recv_string(int fd, std::string& out, uint32_t max_len = 16 * 1024 * 1024) {
    uint32_t len = 0;
    if (!read_exact(fd, &len, sizeof(len))) return false;
    if (len > max_len) return false;
    out.resize(len);
    if (len > 0 && !read_exact(fd, &out[0], len)) return false;
    return true;
}

bool recv_request_body(int fd, uint32_t argc, CompileRequest& req) {
    if (argc > 4096) return false;
    if (!recv_string(fd, req.cwd)) return false;
    if (!recv_string(fd, req.lean_path)) return false;
    if (!recv_string(fd, req.lean_src_path)) return false;
    if (!recv_string(fd, req.lean_num_threads)) return false;
    if (!recv_string(fd, req.lean_tstack)) return false;

    req.argv.resize(argc);
    for (uint32_t i = 0; i < argc; ++i) {
        if (!recv_string(fd, req.argv[i])) return false;
    }
    return true;
}

bool recv_initial_request(int fd, CompileRequest& req) {
    uint32_t header[2] = {0, 0};
    struct iovec iov {};
    iov.iov_base = header;
    iov.iov_len = sizeof(header);

    char cmsg_buf[CMSG_SPACE(sizeof(int) * 2)] {};
    struct msghdr msg {};
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    msg.msg_control = cmsg_buf;
    msg.msg_controllen = sizeof(cmsg_buf);

    ssize_t r;
    do {
        r = recvmsg(fd, &msg, 0);
    } while (r < 0 && errno == EINTR);
    if (r <= 0) return false;

    for (struct cmsghdr* cmsg = CMSG_FIRSTHDR(&msg); cmsg != nullptr; cmsg = CMSG_NXTHDR(&msg, cmsg)) {
        if (cmsg->cmsg_level == SOL_SOCKET && cmsg->cmsg_type == SCM_RIGHTS) {
            size_t data_len = cmsg->cmsg_len - CMSG_LEN(0);
            if (data_len >= sizeof(int) * 2) {
                int fds[2];
                std::memcpy(fds, CMSG_DATA(cmsg), sizeof(fds));
                req.stdout_fd = fds[0];
                req.stderr_fd = fds[1];
            }
        }
    }
    if (req.stdout_fd < 0 || req.stderr_fd < 0) return false;

    size_t got = static_cast<size_t>(r);
    if (got < sizeof(header)) {
        if (!read_exact(fd, reinterpret_cast<uint8_t*>(header) + got, sizeof(header) - got)) {
            return false;
        }
    }

    if (header[0] != kProtoMagic) return false;
    return recv_request_body(fd, header[1], req);
}

bool send_helper_request(int helper_fd, int conn_fd, const CompileRequest& req) {
    std::vector<uint8_t> payload;
    payload.reserve(4096);
    append_u32(payload, kHelperProtoMagic);
    append_u32(payload, static_cast<uint32_t>(req.argv.size()));
    append_str(payload, req.cwd);
    append_str(payload, req.lean_path);
    append_str(payload, req.lean_src_path);
    append_str(payload, req.lean_num_threads);
    append_str(payload, req.lean_tstack);
    for (const auto& a : req.argv) {
        append_str(payload, a);
    }

    int fds[3] = {conn_fd, req.stdout_fd, req.stderr_fd};
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
        sent = sendmsg(helper_fd, &msg, MSG_NOSIGNAL);
    } while (sent < 0 && errno == EINTR);
    if (sent <= 0) return false;

    size_t offset = static_cast<size_t>(sent);
    if (offset < payload.size()) {
        if (!write_exact(helper_fd, payload.data() + offset, payload.size() - offset)) {
            return false;
        }
    }
    return true;
}

bool recv_helper_request(int helper_fd, int& conn_fd, CompileRequest& req, bool& eof) {
    eof = false;
    conn_fd = -1;
    uint32_t header[2] = {0, 0};
    struct iovec iov {};
    iov.iov_base = header;
    iov.iov_len = sizeof(header);

    char cmsg_buf[CMSG_SPACE(sizeof(int) * 3)] {};
    struct msghdr msg {};
    msg.msg_iov = &iov;
    msg.msg_iovlen = 1;
    msg.msg_control = cmsg_buf;
    msg.msg_controllen = sizeof(cmsg_buf);

    ssize_t r;
    do {
        r = recvmsg(helper_fd, &msg, 0);
    } while (r < 0 && errno == EINTR);
    if (r == 0) {
        eof = true;
        return false;
    }
    if (r < 0) return false;

    for (struct cmsghdr* cmsg = CMSG_FIRSTHDR(&msg); cmsg != nullptr; cmsg = CMSG_NXTHDR(&msg, cmsg)) {
        if (cmsg->cmsg_level == SOL_SOCKET && cmsg->cmsg_type == SCM_RIGHTS) {
            size_t data_len = cmsg->cmsg_len - CMSG_LEN(0);
            if (data_len >= sizeof(int) * 3) {
                int fds[3];
                std::memcpy(fds, CMSG_DATA(cmsg), sizeof(fds));
                conn_fd = fds[0];
                req.stdout_fd = fds[1];
                req.stderr_fd = fds[2];
            }
        }
    }
    if (conn_fd < 0 || req.stdout_fd < 0 || req.stderr_fd < 0) {
        if (conn_fd >= 0) {
            close(conn_fd);
            conn_fd = -1;
        }
        return false;
    }

    size_t got = static_cast<size_t>(r);
    if (got < sizeof(header)) {
        if (!read_exact(helper_fd, reinterpret_cast<uint8_t*>(header) + got, sizeof(header) - got)) {
            close(conn_fd);
            conn_fd = -1;
            return false;
        }
    }

    if (header[0] != kHelperProtoMagic || !recv_request_body(helper_fd, header[1], req)) {
        close(conn_fd);
        conn_fd = -1;
        return false;
    }
    return true;
}

lean_object* make_lean_string_array(const std::vector<std::string>& items) {
    lean_object* arr = lean_mk_empty_array();
    for (const auto& s : items) {
        arr = lean_array_push(arr, lean_mk_string(s.c_str()));
    }
    return arr;
}

unsigned parse_child_workers(const CompileRequest& req) {
    for (size_t i = 0; i < req.argv.size(); ++i) {
        const std::string& a = req.argv[i];
        if ((a == "-j" || a == "--threads") && i + 1 < req.argv.size()) {
            return static_cast<unsigned>(std::max(0, std::atoi(req.argv[i + 1].c_str())));
        }
        if (a.rfind("--threads=", 0) == 0) {
            return static_cast<unsigned>(std::max(0, std::atoi(a.c_str() + 10)));
        }
        if (a.size() > 2 && a.rfind("-j", 0) == 0 && a[2] >= '0' && a[2] <= '9') {
            return static_cast<unsigned>(std::max(0, std::atoi(a.c_str() + 2)));
        }
    }
    if (!req.lean_num_threads.empty()) {
        return static_cast<unsigned>(std::max(0, std::atoi(req.lean_num_threads.c_str())));
    }
    unsigned hc = std::thread::hardware_concurrency();
    return hc > 0 ? hc : 1;
}

size_t parse_child_stack_bytes(const CompileRequest& req) {
    size_t stack_kb = 128 * 1024; // 128 MB default matching Lean worker stack
    if (!req.lean_tstack.empty()) {
        long v = std::atol(req.lean_tstack.c_str());
        if (v > 0) stack_kb = static_cast<size_t>(v);
    }
    for (size_t i = 0; i < req.argv.size(); ++i) {
        const std::string& a = req.argv[i];
        if ((a == "-s" || a == "--tstack") && i + 1 < req.argv.size()) {
            long v = std::atol(req.argv[i + 1].c_str());
            if (v > 0) stack_kb = static_cast<size_t>(v);
        } else if (a.rfind("--tstack=", 0) == 0) {
            long v = std::atol(a.c_str() + 9);
            if (v > 0) stack_kb = static_cast<size_t>(v);
        }
    }
    return std::max<size_t>(64ULL * 1024ULL * 1024ULL, stack_kb * 1024ULL);
}

struct WorkerArgs {
    lean_object* snap; // nullptr => clean runtime CoW worker (no preloaded snapshot)
    std::string sysroot;
    CompileRequest* req;
    int32_t rc;
};

void* child_worker_thread(void* p) {
    lean_initialize_thread();
    auto* wa = static_cast<WorkerArgs*>(p);
    lean_object* sysroot_obj = lean_mk_string(wa->sysroot.c_str());
    lean_object* lp_obj = lean_mk_string(wa->req->lean_path.c_str());
    lean_object* argv_obj = make_lean_string_array(wa->req->argv);
    lean_object* res = nullptr;
    if (wa->snap != nullptr) {
        lean_inc(wa->snap);
        res = lean_zygote_run_child(wa->snap, sysroot_obj, lp_obj, argv_obj);
    } else {
        res = lean_zygote_run_clean_child(sysroot_obj, lp_obj, argv_obj);
    }
    if (lean_io_result_is_error(res)) {
        lean_io_result_show_error(res);
        wa->rc = 1;
    } else {
        wa->rc = static_cast<int32_t>(lean_unbox_uint32(lean_io_result_get_value(res)));
    }
    lean_dec_ref(res);
    lean_finalize_thread();
    return nullptr;
}

void reset_child_signals_and_libuv() {
    struct sigaction sa_dfl {};
    sa_dfl.sa_handler = SIG_DFL;
    sigemptyset(&sa_dfl.sa_mask);
    sa_dfl.sa_flags = 0;
    sigaction(SIGCHLD, &sa_dfl, nullptr);
    sigaction(SIGINT, &sa_dfl, nullptr);
    sigaction(SIGTERM, &sa_dfl, nullptr);
    sigaction(SIGPIPE, &sa_dfl, nullptr);
    sigprocmask(SIG_SETMASK, &sa_dfl.sa_mask, nullptr);

    using UvDefaultLoopFn = void* (*)();
    using UvLoopForkFn = int (*)(void*);
    if (auto fn_default = reinterpret_cast<UvDefaultLoopFn>(dlsym(RTLD_DEFAULT, "uv_default_loop"))) {
        if (auto fn_fork = reinterpret_cast<UvLoopForkFn>(dlsym(RTLD_DEFAULT, "uv_loop_fork"))) {
            if (void* loop = fn_default()) {
                (void)fn_fork(loop);
            }
        }
    }
}

bool run_child_in_fork(
    const std::vector<int>& close_fds,
    int conn_fd,
    CompileRequest& req,
    lean_object* snap,
    const std::string& sysroot) {
    pid_t pid = fork();
    if (pid < 0) return false;
    if (pid > 0) return true;

    for (int fd : close_fds) {
        if (fd >= 0) close(fd);
    }

    reset_child_signals_and_libuv();

    uint8_t ack = 'R';
    if (!write_exact(conn_fd, &ack, 1)) {
        _exit(1);
    }

    if (dup2(req.stdout_fd, STDOUT_FILENO) < 0 || dup2(req.stderr_fd, STDERR_FILENO) < 0) {
        _exit(1);
    }
    close(req.stdout_fd);
    close(req.stderr_fd);
    req.stdout_fd = -1;
    req.stderr_fd = -1;

    if (!req.cwd.empty() && chdir(req.cwd.c_str()) != 0) {
        std::fprintf(stderr, "lean-zygote: failed to chdir to %s\n", req.cwd.c_str());
        uint8_t resp[5] = {'X', 0, 0, 0, 0};
        int32_t rc = 1;
        std::memcpy(resp + 1, &rc, 4);
        write_exact(conn_fd, resp, sizeof(resp));
        close(conn_fd);
        _exit(1);
    }

    if (!req.lean_path.empty()) setenv("LEAN_PATH", req.lean_path.c_str(), 1);
    else unsetenv("LEAN_PATH");

    if (!req.lean_src_path.empty()) setenv("LEAN_SRC_PATH", req.lean_src_path.c_str(), 1);
    else unsetenv("LEAN_SRC_PATH");

    if (!req.lean_num_threads.empty()) setenv("LEAN_NUM_THREADS", req.lean_num_threads.c_str(), 1);
    else unsetenv("LEAN_NUM_THREADS");

    if (!req.lean_tstack.empty()) setenv("LEAN_THREAD_STACK_SIZE", req.lean_tstack.c_str(), 1);
    else unsetenv("LEAN_THREAD_STACK_SIZE");

    unsigned workers = parse_child_workers(req);
    lean_after_fork_restart_workers(workers);

    size_t stack_bytes = parse_child_stack_bytes(req);
    WorkerArgs wa { snap, sysroot, &req, 1 };
    pthread_attr_t attr;
    pthread_attr_init(&attr);
    pthread_attr_setstacksize(&attr, stack_bytes);
    pthread_t th {};
    if (pthread_create(&th, &attr, child_worker_thread, &wa) == 0) {
        pthread_join(th, nullptr);
    } else {
        child_worker_thread(&wa);
    }
    pthread_attr_destroy(&attr);

    std::fflush(stdout);
    std::fflush(stderr);
    close(STDOUT_FILENO);
    close(STDERR_FILENO);

    uint8_t resp[5] = {'X', 0, 0, 0, 0};
    std::memcpy(resp + 1, &wa.rc, sizeof(wa.rc));
    write_exact(conn_fd, resp, sizeof(resp));
    close(conn_fd);
    _exit(wa.rc);
}

struct HelperProc {
    pid_t pid = -1;
    int fd = -1;
};

void shutdown_helper(HelperProc& hp) {
    if (hp.fd >= 0) {
        close(hp.fd);
        hp.fd = -1;
    }
    if (hp.pid > 0) {
        for (int attempt = 0; attempt < 40; ++attempt) {
            pid_t w = waitpid(hp.pid, nullptr, WNOHANG);
            if (w != 0) {
                hp.pid = -1;
                return;
            }
            usleep(25000);
        }
        if (waitpid(hp.pid, nullptr, WNOHANG) == 0) {
            kill(hp.pid, SIGTERM);
            usleep(50000);
            if (waitpid(hp.pid, nullptr, WNOHANG) == 0) {
                kill(hp.pid, SIGKILL);
            }
            waitpid(hp.pid, nullptr, 0);
        }
        hp.pid = -1;
    }
}

void close_all_helpers(HelperProc& clean_helper, std::vector<HelperProc>& snap_helpers) {
    shutdown_helper(clean_helper);
    for (auto& hp : snap_helpers) {
        shutdown_helper(hp);
    }
}

std::vector<int> collect_helper_fds(const HelperProc& clean_helper, const std::vector<HelperProc>& snap_helpers, int extra_fd = -1) {
    std::vector<int> fds;
    if (extra_fd >= 0) fds.push_back(extra_fd);
    if (clean_helper.fd >= 0) fds.push_back(clean_helper.fd);
    for (const auto& hp : snap_helpers) {
        if (hp.fd >= 0) fds.push_back(hp.fd);
    }
    return fds;
}

[[noreturn]] void run_cow_helper_loop(int helper_fd, lean_object* snap, const std::string& sysroot) {
    struct sigaction sa_chld {};
    sa_chld.sa_handler = handle_sigchld;
    sigemptyset(&sa_chld.sa_mask);
    sa_chld.sa_flags = SA_RESTART | SA_NOCLDSTOP;
    sigaction(SIGCHLD, &sa_chld, nullptr);

    struct sigaction sa_term {};
    sa_term.sa_handler = handle_sigterm;
    sigemptyset(&sa_term.sa_mask);
    sigaction(SIGINT, &sa_term, nullptr);
    sigaction(SIGTERM, &sa_term, nullptr);

    std::vector<int> close_fds { helper_fd };
    while (!g_stop_requested) {
        while (waitpid(-1, nullptr, WNOHANG) > 0) {}

        struct pollfd pfd {};
        pfd.fd = helper_fd;
        pfd.events = POLLIN;
        int prc = poll(&pfd, 1, 200);
        if (prc < 0) {
            if (errno == EINTR) continue;
            break;
        }
        if (prc == 0) continue;

        int conn_fd = -1;
        CompileRequest req;
        bool eof = false;
        if (!recv_helper_request(helper_fd, conn_fd, req, eof)) {
            if (eof) break;
            if (conn_fd >= 0) {
                uint8_t fb = 'F';
                write_exact(conn_fd, &fb, 1);
                close(conn_fd);
            }
            continue;
        }

        if (!run_child_in_fork(close_fds, conn_fd, req, snap, sysroot)) {
            uint8_t fb = 'F';
            write_exact(conn_fd, &fb, 1);
        }
        close(conn_fd);
    }

    close(helper_fd);
    while (waitpid(-1, nullptr, WNOHANG) > 0) {}
    _exit(0);
}

struct PreloadProfile {
    std::string imports_csv;
    std::string header_file;
    std::string setup_file;
    uint8_t is_module = 0;
    bool explicit_module = false;
};

bool preload_profile_in_process(
    const PreloadProfile& p,
    const std::string& sysroot,
    lean_object*& snap_out,
    std::string& meta_json_out,
    std::string& summary_out) {
    snap_out = nullptr;
    lean_after_fork_restart_workers(1);
    lean_object* preload_res = lean_zygote_preload(
        lean_mk_string(sysroot.c_str()),
        lean_mk_string(p.imports_csv.c_str()),
        lean_mk_string(p.header_file.c_str()),
        lean_mk_string(p.setup_file.c_str()),
        p.is_module);
    if (lean_io_result_is_error(preload_res)) {
        lean_io_result_show_error(preload_res);
        lean_dec_ref(preload_res);
        lean_before_fork_stop_workers();
        return false;
    }
    lean_object* snap = lean_io_result_get_value(preload_res);
    lean_inc(snap);
    lean_dec_ref(preload_res);
    lean_before_fork_stop_workers();
    lean_mark_persistent(snap);

    lean_inc(snap);
    lean_object* meta_obj = lean_zygote_snapshot_meta_json(snap);
    meta_json_out.assign(lean_string_cstr(meta_obj));
    lean_dec_ref(meta_obj);

    lean_inc(snap);
    lean_object* summary_obj = lean_zygote_snapshot_summary(snap);
    summary_out.assign(lean_string_cstr(summary_obj));
    lean_dec_ref(summary_obj);

    snap_out = snap;
    return true;
}

PreloadProfile parse_profile_spec(const std::string& raw_spec) {
    PreloadProfile prof;
    std::string rest = raw_spec;
    if (rest.rfind("module:", 0) == 0) {
        prof.is_module = 1;
        prof.explicit_module = true;
        rest = rest.substr(7);
    } else if (rest.rfind("nonmodule:", 0) == 0) {
        prof.is_module = 0;
        prof.explicit_module = true;
        rest = rest.substr(10);
    } else if (rest.rfind("private:", 0) == 0) {
        prof.is_module = 0;
        prof.explicit_module = true;
        rest = rest.substr(8);
    }
    if (rest.rfind("setup:", 0) == 0) {
        prof.setup_file = rest.substr(6);
    } else if (rest.rfind("from:", 0) == 0) {
        prof.header_file = rest.substr(5);
    } else {
        prof.imports_csv = rest;
    }
    return prof;
}

void print_usage(const char* prog) {
    std::fprintf(stderr,
        "Usage: %s [OPTIONS]\n"
        "Linux CoW Persistent Import Fork-Server for Lean 4.\n\n"
        "Options:\n"
        "  --socket <path>        Unix socket path (default: $LEAN_ZYGOTE_SOCK or /tmp/lean-zygote.sock)\n"
        "  --profile <spec>       Repeatable snapshot profile (<Mod1,Mod2>, module:<Mod>, setup:<json>, from:<lean>, none)\n"
        "  --import <Mod1,Mod2>   Comma-separated modules to preload persistently\n"
        "  --imports-from <file>  Preload header imports from a template .lean file\n"
        "  --setup <setup.json>   Preload imports & artifacts from a Lake .setup.json\n"
        "  --module               Preload profiles without explicit mode prefix in Lean module (.exported) mode\n"
        "  --fork-any             Fork a clean-runtime CoW helper before preloading to handle heterogeneous builds\n"
        "  --no-preload           Skip snapshot preloading (useful with --fork-any)\n"
        "  --sysroot <dir>        Lean toolchain sysroot (default: inferred from binary/LEAN_SYSROOT)\n"
        "  --pidfile <path>       Write daemon PID to <path>\n"
        "  --help                 Display this help\n",
        prog);
}

std::string infer_default_sysroot(const char* argv0) {
    if (const char* env = std::getenv("LEAN_SYSROOT")) {
        if (*env) return env;
    }
    char resolved[4096];
    ssize_t n = readlink("/proc/self/exe", resolved, sizeof(resolved) - 1);
    std::string exe = (n > 0) ? std::string(resolved, static_cast<size_t>(n)) : std::string(argv0 ? argv0 : "");
    auto slash1 = exe.rfind('/');
    if (slash1 != std::string::npos) {
        std::string bin_dir = exe.substr(0, slash1);
        auto slash2 = bin_dir.rfind('/');
        if (slash2 != std::string::npos) {
            std::string cand = bin_dir.substr(0, slash2);
            std::string probe = cand + "/lib/lean/Init.olean";
            if (access(probe.c_str(), F_OK) == 0) {
                return cand;
            }
        }
    }
    if (const char* lean_bin = std::getenv("LEAN_BIN")) {
        std::string lb(lean_bin);
        auto s1 = lb.rfind('/');
        if (s1 != std::string::npos) {
            std::string bd = lb.substr(0, s1);
            auto s2 = bd.rfind('/');
            if (s2 != std::string::npos) {
                return bd.substr(0, s2);
            }
        }
    }
    return ".";
}

} // namespace

int main(int argc, char** argv) {
    signal(SIGPIPE, SIG_IGN);

    g_sock_path = std::getenv("LEAN_ZYGOTE_SOCK") ? std::getenv("LEAN_ZYGOTE_SOCK") : "/tmp/lean-zygote.sock";
    if (g_sock_path.empty()) g_sock_path = "/tmp/lean-zygote.sock";

    PreloadProfile legacy_profile;
    bool has_legacy_profile = false;
    std::vector<PreloadProfile> profiles;
    std::string sysroot = infer_default_sysroot(argv[0]);
    std::string pidfile = "";
    uint8_t global_is_module = 0;
    bool fork_any = false;
    bool no_preload = false;

    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--help" || a == "-h") {
            print_usage(argv[0]);
            return 0;
        } else if (a == "--socket" && i + 1 < argc) {
            g_sock_path = argv[++i];
        } else if (a.rfind("--socket=", 0) == 0) {
            g_sock_path = a.substr(9);
        } else if (a == "--profile" && i + 1 < argc) {
            std::string spec = argv[++i];
            if (spec == "none") no_preload = true;
            else profiles.push_back(parse_profile_spec(spec));
        } else if (a.rfind("--profile=", 0) == 0) {
            std::string spec = a.substr(10);
            if (spec == "none") no_preload = true;
            else profiles.push_back(parse_profile_spec(spec));
        } else if ((a == "--import" || a == "--imports") && i + 1 < argc) {
            legacy_profile.imports_csv = argv[++i];
            has_legacy_profile = true;
        } else if (a == "--imports-from" && i + 1 < argc) {
            legacy_profile.header_file = argv[++i];
            has_legacy_profile = true;
        } else if (a == "--setup" && i + 1 < argc) {
            legacy_profile.setup_file = argv[++i];
            has_legacy_profile = true;
        } else if (a == "--sysroot" && i + 1 < argc) {
            sysroot = argv[++i];
        } else if (a == "--pidfile" && i + 1 < argc) {
            pidfile = argv[++i];
        } else if (a == "--module") {
            global_is_module = 1;
        } else if (a == "--fork-any") {
            fork_any = true;
        } else if (a == "--no-preload") {
            no_preload = true;
        } else {
            std::fprintf(stderr, "lean-zygote: unknown argument: %s\n", a.c_str());
            print_usage(argv[0]);
            return 1;
        }
    }

    if (g_sock_path.size() >= sizeof(sockaddr_un::sun_path)) {
        std::fprintf(stderr, "lean-zygote: socket path too long: %s\n", g_sock_path.c_str());
        return 1;
    }

    if (has_legacy_profile) {
        if (legacy_profile.imports_csv == "none" && legacy_profile.header_file.empty() &&
            legacy_profile.setup_file.empty()) {
            no_preload = true;
        } else {
            profiles.push_back(std::move(legacy_profile));
        }
    }
    if (profiles.empty() && !no_preload) {
        profiles.push_back(PreloadProfile{"Init", "", "", global_is_module, false});
    }
    for (auto& p : profiles) {
        if (!p.explicit_module) {
            p.is_module = global_is_module;
        }
    }

    // Force single-threaded runtime during preload so no extra worker threads are active.
    setenv("LEAN_NUM_THREADS", "1", 1);

    lean_initialize();
    lean_object* shim_res = initialize_LeanZygoteShim(1);
    if (lean_io_result_is_error(shim_res)) {
        lean_io_result_show_error(shim_res);
        return 1;
    }
    lean_dec_ref(shim_res);
    lean_io_mark_end_initialization();
    lean_before_fork_stop_workers();

    HelperProc clean_helper;
    if (fork_any) {
        int helper_sv[2] = {-1, -1};
        if (socketpair(AF_UNIX, SOCK_STREAM, 0, helper_sv) != 0) {
            std::perror("lean-zygote: socketpair");
            return 1;
        }
        clean_helper.pid = fork();
        if (clean_helper.pid < 0) {
            std::perror("lean-zygote: fork clean helper");
            close(helper_sv[0]);
            close(helper_sv[1]);
            return 1;
        }
        if (clean_helper.pid == 0) {
            close(helper_sv[0]);
            run_cow_helper_loop(helper_sv[1], nullptr, sysroot);
        }
        close(helper_sv[1]);
        clean_helper.fd = helper_sv[0];
    }

    // Isolate each preload profile in its own Lean runtime process forked before
    // any snapshot is loaded, so [init] initializers and EnvExtensions from one
    // profile cannot mutate the runtime state used by another profile.
    std::vector<HelperProc> snap_helpers(profiles.size());
    for (size_t i = 1; i < profiles.size(); ++i) {
        int sv[2] = {-1, -1};
        if (socketpair(AF_UNIX, SOCK_STREAM, 0, sv) != 0) {
            std::perror("lean-zygote: socketpair");
            close_all_helpers(clean_helper, snap_helpers);
            return 1;
        }
        pid_t pid = fork();
        if (pid < 0) {
            std::perror("lean-zygote: fork profile helper");
            close(sv[0]);
            close(sv[1]);
            close_all_helpers(clean_helper, snap_helpers);
            return 1;
        }
        if (pid == 0) {
            close(sv[0]);
            if (clean_helper.fd >= 0) close(clean_helper.fd);
            for (size_t j = 1; j < i; ++j) {
                if (snap_helpers[j].fd >= 0) close(snap_helpers[j].fd);
            }
            lean_object* snap_i = nullptr;
            std::string meta_json_i;
            std::string summary_i;
            if (!preload_profile_in_process(profiles[i], sysroot, snap_i, meta_json_i, summary_i)) {
                uint8_t err_tag = 'E';
                write_exact(sv[1], &err_tag, 1);
                close(sv[1]);
                _exit(1);
            }
            std::vector<uint8_t> init_msg;
            init_msg.push_back('M');
            append_str(init_msg, meta_json_i);
            append_str(init_msg, summary_i);
            if (!write_exact(sv[1], init_msg.data(), init_msg.size())) {
                close(sv[1]);
                _exit(1);
            }
            run_cow_helper_loop(sv[1], snap_i, sysroot);
        }
        close(sv[1]);
        snap_helpers[i] = HelperProc{ pid, sv[0] };
    }

    lean_object* snap0 = nullptr;
    std::vector<std::string> meta_jsons(profiles.size());
    std::vector<std::string> summary_parts(profiles.size());
    if (!profiles.empty()) {
        if (!preload_profile_in_process(profiles[0], sysroot, snap0, meta_jsons[0], summary_parts[0])) {
            close_all_helpers(clean_helper, snap_helpers);
            return 1;
        }
        for (size_t i = 1; i < profiles.size(); ++i) {
            uint8_t tag = 0;
            if (!read_exact(snap_helpers[i].fd, &tag, 1) || tag != 'M' ||
                !recv_string(snap_helpers[i].fd, meta_jsons[i]) ||
                !recv_string(snap_helpers[i].fd, summary_parts[i])) {
                std::fprintf(stderr, "lean-zygote: failed to preload profile [%zu]\n", i);
                close_all_helpers(clean_helper, snap_helpers);
                return 1;
            }
        }
    }

    std::string summaries;
    for (size_t i = 0; i < profiles.size(); ++i) {
        if (!summaries.empty()) summaries += "; ";
        summaries += "[" + std::to_string(i) + "] " + summary_parts[i];
    }
    if (profiles.empty()) {
        summaries = "none";
    }

    lean_object* metas = lean_mk_empty_array();
    if (!meta_jsons.empty()) {
        lean_object* parse_res = lean_zygote_parse_snapshot_metas(make_lean_string_array(meta_jsons));
        if (lean_io_result_is_error(parse_res)) {
            lean_io_result_show_error(parse_res);
            lean_dec_ref(parse_res);
            close_all_helpers(clean_helper, snap_helpers);
            return 1;
        }
        metas = lean_io_result_get_value(parse_res);
        lean_inc(metas);
        lean_dec_ref(parse_res);
    }
    lean_mark_persistent(metas);

    struct sigaction sa_chld {};
    sa_chld.sa_handler = handle_sigchld;
    sigemptyset(&sa_chld.sa_mask);
    sa_chld.sa_flags = SA_RESTART | SA_NOCLDSTOP;
    sigaction(SIGCHLD, &sa_chld, nullptr);

    struct sigaction sa_term {};
    sa_term.sa_handler = handle_sigterm;
    sigemptyset(&sa_term.sa_mask);
    sigaction(SIGINT, &sa_term, nullptr);
    sigaction(SIGTERM, &sa_term, nullptr);

    unlink(g_sock_path.c_str());
    int listen_fd = socket(AF_UNIX, SOCK_STREAM, 0);
    if (listen_fd < 0) {
        std::perror("lean-zygote: socket");
        close_all_helpers(clean_helper, snap_helpers);
        return 1;
    }

    struct sockaddr_un addr {};
    addr.sun_family = AF_UNIX;
    std::strncpy(addr.sun_path, g_sock_path.c_str(), sizeof(addr.sun_path) - 1);
    if (bind(listen_fd, reinterpret_cast<struct sockaddr*>(&addr), sizeof(addr)) < 0) {
        std::perror("lean-zygote: bind");
        close(listen_fd);
        close_all_helpers(clean_helper, snap_helpers);
        return 1;
    }
    chmod(g_sock_path.c_str(), 0600);
    if (listen(listen_fd, 512) < 0) {
        std::perror("lean-zygote: listen");
        close(listen_fd);
        unlink(g_sock_path.c_str());
        close_all_helpers(clean_helper, snap_helpers);
        return 1;
    }

    if (!pidfile.empty()) {
        if (FILE* pf = std::fopen(pidfile.c_str(), "w")) {
            std::fprintf(pf, "%d\n", static_cast<int>(getpid()));
            std::fclose(pf);
        }
    }

    std::fprintf(stderr, "lean-zygote: listening on %s (profiles=%zu: %s, fork-any=%s, persistent CoW ready)\n",
        g_sock_path.c_str(),
        profiles.size(),
        summaries.c_str(),
        fork_any ? "on" : "off");
    std::fflush(stderr);

    uint64_t snapshot_hits = 0;
    uint64_t clean_cow_hits = 0;
    uint64_t fallbacks = 0;

    while (!g_stop_requested) {
        while (waitpid(-1, nullptr, WNOHANG) > 0) {}

        struct pollfd pfd {};
        pfd.fd = listen_fd;
        pfd.events = POLLIN;
        int prc = poll(&pfd, 1, 200);
        if (prc < 0) {
            if (errno == EINTR) continue;
            break;
        }
        if (prc == 0) continue;

        int conn_fd = accept(listen_fd, nullptr, nullptr);
        if (conn_fd < 0) {
            if (errno == EINTR || errno == EAGAIN || errno == EWOULDBLOCK) continue;
            break;
        }

        CompileRequest req;
        if (!recv_initial_request(conn_fd, req)) {
            uint8_t fb = 'F';
            write_exact(conn_fd, &fb, 1);
            close(conn_fd);
            ++fallbacks;
            continue;
        }

        uint32_t snap_idx = kNoSnapshot;
        if (!profiles.empty()) {
            lean_inc(metas);
            lean_object* sel_res = lean_zygote_select_snapshot_meta(
                metas,
                lean_mk_string(req.cwd.c_str()),
                lean_mk_string(req.lean_path.c_str()),
                make_lean_string_array(req.argv));
            if (lean_io_result_is_error(sel_res)) {
                lean_dec_ref(sel_res);
            } else {
                snap_idx = lean_unbox_uint32(lean_io_result_get_value(sel_res));
                lean_dec_ref(sel_res);
            }
        }

        if (snap_idx == 0 && snap0 != nullptr) {
            std::vector<int> close_fds = collect_helper_fds(clean_helper, snap_helpers, listen_fd);
            if (run_child_in_fork(close_fds, conn_fd, req, snap0, sysroot)) {
                ++snapshot_hits;
            } else {
                uint8_t fb = 'F';
                write_exact(conn_fd, &fb, 1);
                ++fallbacks;
            }
            close(conn_fd);
            continue;
        }

        if (snap_idx != kNoSnapshot && snap_idx >= 1 && snap_idx < snap_helpers.size() && snap_helpers[snap_idx].fd >= 0) {
            if (send_helper_request(snap_helpers[snap_idx].fd, conn_fd, req)) {
                ++snapshot_hits;
                close(conn_fd);
                continue;
            }
            close(snap_helpers[snap_idx].fd);
            snap_helpers[snap_idx].fd = -1;
        }

        if (clean_helper.fd >= 0) {
            lean_object* clean_res = lean_zygote_can_run_clean(
                lean_mk_string(req.cwd.c_str()),
                lean_mk_string(req.lean_path.c_str()),
                make_lean_string_array(req.argv));
            bool can_clean = false;
            if (lean_io_result_is_error(clean_res)) {
                lean_dec_ref(clean_res);
            } else {
                can_clean = (lean_unbox(lean_io_result_get_value(clean_res)) != 0);
                lean_dec_ref(clean_res);
            }
            if (can_clean) {
                if (send_helper_request(clean_helper.fd, conn_fd, req)) {
                    ++clean_cow_hits;
                    close(conn_fd);
                    continue;
                }
                close(clean_helper.fd);
                clean_helper.fd = -1;
            }
        }

        uint8_t fb = 'F';
        write_exact(conn_fd, &fb, 1);
        close(conn_fd);
        ++fallbacks;
    }

    std::fprintf(stderr, "lean-zygote: shutdown stats snapshot_hits=%llu clean_cow_hits=%llu fallbacks=%llu\n",
        static_cast<unsigned long long>(snapshot_hits),
        static_cast<unsigned long long>(clean_cow_hits),
        static_cast<unsigned long long>(fallbacks));
    std::fflush(stderr);

    close_all_helpers(clean_helper, snap_helpers);

    close(listen_fd);
    unlink(g_sock_path.c_str());
    if (!pidfile.empty()) unlink(pidfile.c_str());
    return 0;
}
