// Worklist compaction pass executed once per quantum after VM kernel rounds.

@compute @workgroup_size(64, 1, 1)
fn main(
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
    p_scratch_base = hdr.max_stack_frames * 8u;

    let want_tag = job_idx + 1u;
    let want_epoch = select(hdr.batch_epoch, 1u, hdr.batch_epoch == 0u);
    if s_read(VM_JOB_EPOCH) == want_epoch && s_read(VM_JOB_TAG) == want_tag && s_read(VM_HALT) == 0u {
        let out_idx = atomicAdd(&ctl.out_count, 1u);
        active_out[out_idx] = pair;
    }
}
