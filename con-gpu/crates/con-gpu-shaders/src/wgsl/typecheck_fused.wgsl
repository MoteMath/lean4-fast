// Parameterized persistent-register VM compute kernel template for Lean 4 arena typechecking.
// Specialized at pipeline creation time for VM_MY_K in {K_INFER, K_WHNF, K_DEFEQ, K_LEVEL, K_SUBST}.

const VM_MY_K: u32 = 0u;

@compute @workgroup_size(64, 1, 1)
fn main(
    @builtin(local_invocation_id) lid: vec3<u32>,
    @builtin(global_invocation_id) gid: vec3<u32>,
) {
    let tid = gid.x;
    if tid >= ctl.in_count {
        return;
    }

    let pair = active_in[tid];
    let job_idx = pair.x;
    let state_slot = pair.y;

    p_wg_base = (state_slot >> 6u) * hdr.scratch_wg_stride;
    p_lane = state_slot & 63u;
    p_lds_base = lid.x * 64u;
    p_scratch_base = hdr.max_stack_frames * 8u;

    let want_tag = job_idx + 1u;
    let want_epoch = select(hdr.batch_epoch, 1u, hdr.batch_epoch == 0u);
    let already_init = (s_read(VM_JOB_EPOCH) == want_epoch) && (s_read(VM_JOB_TAG) == want_tag);

    var q_rem: u32 = 0u;
    if !already_init {
        if VM_MY_K != K_INFER || ctl.is_first_quantum != 1u {
            return;
        }
        s_write(VM_JOB_TAG, want_tag);
        s_write(VM_JOB_EPOCH, want_epoch);
        s_write(VM_Q_IDX, 1u);
        for (var i = 0u; i < 64u; i = i + 1u) {
            lds_cache[p_lds_base + i] = NONE_U32;
            s_write(VM_LDS_OFF + i, NONE_U32);
        }
        let job = jobs[job_idx];
        vm_load_job(job);
        p_sp = 0u;
        p_sptr = SCRATCH_ALLOC_START;
        p_steps = 0u;
        p_res0 = 0u;
        p_res1 = 0u;
        p_status = STATUS_DELEGATE;
        p_reason = REASON_OK;
        p_halt = 0u;
        p_subst_gen = 1u;
        p_job_epoch = want_epoch;
        p_defeq_depth = 0u;
        p_defeq_sptr = SCRATCH_ALLOC_START;
        p_do_pop = false;
        p_req_op = 0u;
        p_nat_ok = false;
        p_bool_ok = false;
        if check_decl_top_guards(job) {
            p_nat_ok = nat_consts_ok();
            p_bool_ok = bool_consts_ok();
            let _ok = push_frame(OP_JOB_FINISH, 0u, 0u, 0u, 0u, 0u, 0u, 0u);
        }
        q_rem = ctl.quantum_steps;
    } else {
        if s_read(VM_HALT) != 0u || s_read(VM_TARGET_K) != VM_MY_K {
            return;
        }
        let q_idx = s_read(VM_Q_IDX);
        if q_idx != ctl.is_first_quantum {
            q_rem = ctl.quantum_steps;
            s_write(VM_Q_IDX, ctl.is_first_quantum);
        } else {
            q_rem = s_read(VM_Q_REM);
        }
        if q_rem == 0u {
            return;
        }
        let job = jobs[job_idx];
        vm_load_job(job);
        vm_load_state();
        for (var i = 0u; i < 64u; i = i + 1u) {
            lds_cache[p_lds_base + i] = s_read(VM_LDS_OFF + i);
        }
    }

    while p_halt == 0u && p_sp > 0u && q_rem > 0u {
        let top = p_sp - 1u;
        let op = f_read(top, 0u);
        if op_kernel(op) != VM_MY_K {
            break;
        }
        if p_steps >= hdr.max_steps {
            halt_delegate(REASON_STEP_BUDGET);
            break;
        }
        p_steps = p_steps + 1u;
        q_rem = q_rem - 1u;
        p_do_pop = false;
        p_req_op = 0u;
        switch op {
            // __OP_CASES__
            default: { halt_delegate(REASON_UNMODELED); }
        }
        if p_do_pop && p_halt == 0u {
            do_pop_ret();
        }
        if p_req_op != 0u && p_halt == 0u {
            dispatch_req(top);
        }
    }

    if p_halt == 0u && p_sp == 0u {
        halt_delegate(REASON_UNMODELED);
    }

    if p_halt == 0u && p_steps >= hdr.max_steps {
        halt_delegate(REASON_STEP_BUDGET);
    }

    s_write(VM_Q_REM, q_rem);

    if p_halt != 0u {
        s_write(VM_HALT, 1u);
        s_write(VM_TARGET_K, K_DONE);
        verdicts[job_idx] = GpuVerdict(p_status, p_reason, p_steps, p_sptr);
    } else {
        for (var i = 0u; i < 64u; i = i + 1u) {
            s_write(VM_LDS_OFF + i, lds_cache[p_lds_base + i]);
        }
        let next_k = op_kernel(f_read(p_sp - 1u, 0u));
        vm_save_state(next_k);
        verdicts[job_idx] = GpuVerdict(STATUS_DELEGATE, REASON_STEP_BUDGET, p_steps, p_sptr);
    }
}
