/*
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Markus Himmel, Sofia Rodrigues
 */
#include <memory>
#include <mutex>
#ifndef LEAN_WINDOWS
#include <unistd.h>
#endif
#include "runtime/libuv.h"
#include "runtime/object.h"

#ifndef LEAN_EMSCRIPTEN
#include <uv.h>
#endif

namespace lean {

#ifndef LEAN_EMSCRIPTEN

static std::mutex g_ev_lifecycle_mtx;
static std::unique_ptr<lthread> g_ev_thread;
#ifndef LEAN_WINDOWS
static pid_t g_ev_pre_fork_pid = 0;
#endif

void ensure_libuv_started() {
    std::lock_guard<std::mutex> lk(g_ev_lifecycle_mtx);
    if (!global_ev.loop) {
        global_ev.loop = uv_default_loop();
        int r = uv_async_init(global_ev.loop, &global_ev.async, NULL);
        if (r != 0) {
            std::string msg = std::string("Failed to initialize async: ") + uv_strerror(r);
            lean_internal_panic(msg.c_str());
        }
    }
    if (!g_ev_thread) {
        global_ev.stop_requested.store(false, std::memory_order_release);
        g_ev_thread = std::make_unique<lthread>([]() { event_loop_run_loop(&global_ev); });
    }
    global_ev.initialized.store(true, std::memory_order_release);
}

void lean_libuv_before_fork() {
    std::unique_ptr<lthread> to_join;
    {
        std::lock_guard<std::mutex> lk(g_ev_lifecycle_mtx);
#ifndef LEAN_WINDOWS
        g_ev_pre_fork_pid = getpid();
#endif
        if (!g_ev_thread)
            return;
        to_join = std::move(g_ev_thread);
    }
    global_ev.stop_requested.store(true, std::memory_order_release);
    event_loop_lock(&global_ev);
    global_ev.stop_requested.store(true, std::memory_order_release);
    event_loop_unlock(&global_ev);
    to_join->join();
}

void lean_libuv_after_fork() {
    std::lock_guard<std::mutex> lk(g_ev_lifecycle_mtx);
    if (!global_ev.initialized.load(std::memory_order_acquire) || !global_ev.loop)
        return;
#ifndef LEAN_WINDOWS
    if (g_ev_pre_fork_pid != 0 && getpid() != g_ev_pre_fork_pid) {
        uv_loop_fork(global_ev.loop);
    }
#endif
    global_ev.n_waiters = 0;
    global_ev.stop_requested.store(false, std::memory_order_release);
    if (!g_ev_thread) {
        g_ev_thread = std::make_unique<lthread>([]() { event_loop_run_loop(&global_ev); });
    }
}

extern "C" void initialize_libuv() {
    initialize_libuv_timer();
    initialize_libuv_tcp_socket();
    initialize_libuv_udp_socket();
    initialize_libuv_signal();
    initialize_libuv_loop();
}

extern "C" LEAN_EXPORT char ** lean_setup_args(int argc, char ** argv) {
    return uv_setup_args(argc, argv);
}

/* Lean.libUVVersionFn : Unit → Nat */
extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_unsigned_to_nat(uv_version());
}

#else

extern "C" void initialize_libuv() {}
void ensure_libuv_started() {}
void lean_libuv_before_fork() {}
void lean_libuv_after_fork() {}

extern "C" LEAN_EXPORT lean_obj_res lean_libuv_version(lean_obj_arg o) {
    return lean_box(0);
}

extern "C" LEAN_EXPORT char ** lean_setup_args(int argc, char ** argv) {
    return argv;
}


#endif
}
