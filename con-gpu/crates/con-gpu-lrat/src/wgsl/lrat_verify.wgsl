// Data-parallel GPU LRAT UNSAT proof verifier (Pipeline C).
// ZERO f32/f64 and ZERO u64/SHADER_INT64 instructions; pure u32/i32 arithmetic.
// Each thread verifies RUP derivation for one derived clause step k using strictly causal hints (hint_id < k).

struct LratHeader {
    num_steps: u32,
    max_clause_id: u32,
    num_cnf_clauses: u32,
    pad0: u32,
}

struct LratStep {
    clause_id: u32,
    step_order: u32,
    hint_off: u32,
    hint_len: u32,
}

struct LratVerdict {
    status: u32,          // 0=Verified, 1=Rejected, 2=Delegate
    reason: u32,
    clause_id: u32,
    is_empty_clause: u32,
}

@group(0) @binding(0) var<uniform> hdr: LratHeader;
@group(0) @binding(1) var<storage, read> steps: array<LratStep>;
@group(0) @binding(2) var<storage, read> step_flags: array<u32>;
@group(0) @binding(3) var<storage, read> hints: array<i32>;
@group(0) @binding(4) var<storage, read> clause_lits: array<i32>;
@group(0) @binding(5) var<storage, read> clause_off: array<u32>;
@group(0) @binding(6) var<storage, read> clause_len: array<u32>;
@group(0) @binding(7) var<storage, read> clause_birth_step: array<u32>;
@group(0) @binding(8) var<storage, read> clause_deleted_at: array<u32>;
@group(0) @binding(9) var<storage, read_write> verdicts: array<LratVerdict>;
@group(0) @binding(10) var<storage, read_write> summary: array<atomic<u32>>;
// summary[0] = verified_count, summary[1] = delegated_count, summary[2] = rejected_count, summary[3] = empty_clause_verified

// Per-lane open-addressed signed-literal table in on-chip LDS (64 lanes * 64 slots = 16 KB).
var<workgroup> lds_table: array<i32, 4096>;
var<workgroup> wg_red: array<u32, 256>;

const STATUS_VERIFIED: u32 = 0u;
const STATUS_REJECTED: u32 = 1u;
const STATUS_DELEGATE: u32 = 2u;

const REASON_OK: u32 = 0u;
const REASON_EMPTY_HINTS: u32 = 1u;
const REASON_ACAUSAL_HINT: u32 = 2u;
const REASON_UNDEFINED_HINT: u32 = 3u;
const REASON_DELETED_HINT: u32 = 4u;
const REASON_NON_UNIT_HINT: u32 = 5u;
const REASON_SAT_HINT: u32 = 6u;
const REASON_NO_CONFLICT: u32 = 7u;
const REASON_BAD_ID: u32 = 8u;
const REASON_DELEGATE_RAT: u32 = 9u;
const REASON_DELEGATE_CAP: u32 = 10u;

const LDS_SLOTS_PER_LANE: u32 = 64u;
const LDS_MAX_OCC: u32 = 48u;

fn mix_u32(x_in: u32) -> u32 {
    var x = x_in;
    x = (x ^ (x >> 16u)) * 0x7feb352du;
    x = (x ^ (x >> 15u)) * 0x846ca68bu;
    return x ^ (x >> 16u);
}

// Returns 0=inserted/already present, 1=contradiction (-lit was already true), 2=capacity overflow (delegate).
fn lds_insert_true(lds_base: u32, lit: i32, occ: ptr<function, u32>) -> u32 {
    let v = abs(lit);
    var slot = mix_u32(bitcast<u32>(v)) & 63u;
    for (var p = 0u; p < LDS_SLOTS_PER_LANE; p += 1u) {
        let cur = lds_table[lds_base + slot];
        if cur == 0i {
            if *occ >= LDS_MAX_OCC {
                return 2u;
            }
            lds_table[lds_base + slot] = lit;
            *occ = *occ + 1u;
            return 0u;
        }
        if cur == lit {
            return 0u;
        }
        if cur == -lit {
            return 1u;
        }
        slot = (slot + 1u) & 63u;
    }
    return 2u;
}

// Returns 1 if lit is TRUE, -1 if lit is FALSE (-lit is TRUE), 0 if unassigned.
fn lds_probe_lit(lds_base: u32, lit: i32) -> i32 {
    let v = abs(lit);
    var slot = mix_u32(bitcast<u32>(v)) & 63u;
    for (var p = 0u; p < LDS_SLOTS_PER_LANE; p += 1u) {
        let cur = lds_table[lds_base + slot];
        if cur == 0i {
            return 0i;
        }
        if cur == lit {
            return 1i;
        }
        if cur == -lit {
            return -1i;
        }
        slot = (slot + 1u) & 63u;
    }
    return 0i;
}

@compute @workgroup_size(64)
fn main(
    @builtin(global_invocation_id) gid: vec3<u32>,
    @builtin(local_invocation_id) lid: vec3<u32>,
) {
    let lane = lid.x;
    let tid = gid.x;
    let lds_base = lane * LDS_SLOTS_PER_LANE;

    var my_ver = 0u;
    var my_del = 0u;
    var my_rej = 0u;
    var my_empty_ok = 0u;

    if tid < hdr.num_steps {
        let step = steps[tid];
        let sflags = step_flags[tid];
        let cid = step.clause_id;

        var status = STATUS_VERIFIED;
        var reason = REASON_OK;

        if cid == 0u || cid > hdr.max_clause_id || (sflags & 6u) != 0u {
            status = STATUS_REJECTED;
            reason = REASON_BAD_ID;
        } else if (sflags & 1u) != 0u {
            status = STATUS_DELEGATE;
            reason = REASON_DELEGATE_RAT;
        } else if step.hint_len == 0u {
            status = STATUS_REJECTED;
            reason = REASON_EMPTY_HINTS;
        } else {
            // Clear this lane's private LDS open-addressed table slice.
            for (var z = 0u; z < LDS_SLOTS_PER_LANE; z += 1u) {
                lds_table[lds_base + z] = 0i;
            }
            var occ = 0u;

            // Negate derived clause C: assert (-l) is TRUE for each l in C.
            let c_off = clause_off[cid];
            let c_len = clause_len[cid];
            for (var i = 0u; i < c_len; i += 1u) {
                let lit = clause_lits[c_off + i];
                if lit == 0i {
                    status = STATUS_REJECTED;
                    reason = REASON_BAD_ID;
                    break;
                }
                let ins = lds_insert_true(lds_base, -lit, &occ);
                if ins == 2u {
                    status = STATUS_DELEGATE;
                    reason = REASON_DELEGATE_CAP;
                    break;
                }
                if ins == 1u {
                    // Tautological clause in C; delegate to host exact checker so hint rules apply uniformly.
                    status = STATUS_DELEGATE;
                    reason = REASON_DELEGATE_CAP;
                    break;
                }
            }

            // Reverse Unit Propagation along hints.
            var conflict_found = false;
            if status == STATUS_VERIFIED {
                for (var hi = 0u; hi < step.hint_len; hi += 1u) {
                    let h_raw = hints[step.hint_off + hi];
                    if h_raw <= 0i {
                        if h_raw < 0i {
                            status = STATUS_DELEGATE;
                            reason = REASON_DELEGATE_RAT;
                        } else {
                            status = STATUS_REJECTED;
                            reason = REASON_UNDEFINED_HINT;
                        }
                        break;
                    }
                    let hid = u32(h_raw);
                    if hid >= cid {
                        status = STATUS_REJECTED;
                        reason = REASON_ACAUSAL_HINT;
                        break;
                    }
                    if hid > hdr.max_clause_id {
                        status = STATUS_REJECTED;
                        reason = REASON_UNDEFINED_HINT;
                        break;
                    }
                    if clause_birth_step[hid] >= step.step_order {
                        status = STATUS_REJECTED;
                        reason = REASON_UNDEFINED_HINT;
                        break;
                    }
                    if step.step_order >= clause_deleted_at[hid] {
                        status = STATUS_REJECTED;
                        reason = REASON_DELETED_HINT;
                        break;
                    }

                    if !conflict_found {
                        let hoff = clause_off[hid];
                        let hlen = clause_len[hid];
                        var unassigned_lit = 0i;
                        var unassigned_cnt = 0u;
                        var is_sat = false;

                        for (var j = 0u; j < hlen; j += 1u) {
                            let lit = clause_lits[hoff + j];
                            if lit == 0i {
                                status = STATUS_REJECTED;
                                reason = REASON_BAD_ID;
                                break;
                            }
                            let p = lds_probe_lit(lds_base, lit);
                            if p == 1i {
                                is_sat = true;
                                break;
                            }
                            if p == 0i {
                                if unassigned_cnt == 0u {
                                    unassigned_lit = lit;
                                    unassigned_cnt = 1u;
                                } else if lit != unassigned_lit {
                                    unassigned_cnt = 2u;
                                    break;
                                }
                            }
                        }

                        if status != STATUS_VERIFIED {
                            break;
                        }
                        if is_sat {
                            status = STATUS_REJECTED;
                            reason = REASON_SAT_HINT;
                            break;
                        }
                        if unassigned_cnt >= 2u {
                            status = STATUS_REJECTED;
                            reason = REASON_NON_UNIT_HINT;
                            break;
                        }
                        if unassigned_cnt == 1u {
                            let ins = lds_insert_true(lds_base, unassigned_lit, &occ);
                            if ins == 2u {
                                status = STATUS_DELEGATE;
                                reason = REASON_DELEGATE_CAP;
                                break;
                            }
                        } else {
                            conflict_found = true;
                        }
                    }
                }

                if status == STATUS_VERIFIED && !conflict_found {
                    status = STATUS_REJECTED;
                    reason = REASON_NO_CONFLICT;
                }
            }
        }

        let is_empty = select(0u, 1u, cid <= hdr.max_clause_id && clause_len[cid] == 0u);
        verdicts[tid] = LratVerdict(status, reason, cid, is_empty);

        if status == STATUS_VERIFIED {
            my_ver = 1u;
            if is_empty != 0u {
                my_empty_ok = 1u;
            }
        } else if status == STATUS_DELEGATE {
            my_del = 1u;
        } else {
            my_rej = 1u;
        }
    }

    wg_red[lane * 4u + 0u] = my_ver;
    wg_red[lane * 4u + 1u] = my_del;
    wg_red[lane * 4u + 2u] = my_rej;
    wg_red[lane * 4u + 3u] = my_empty_ok;
    workgroupBarrier();

    if lane == 0u {
        var s0 = 0u;
        var s1 = 0u;
        var s2 = 0u;
        var s3 = 0u;
        for (var i = 0u; i < 64u; i += 1u) {
            s0 += wg_red[i * 4u + 0u];
            s1 += wg_red[i * 4u + 1u];
            s2 += wg_red[i * 4u + 2u];
            s3 += wg_red[i * 4u + 3u];
        }
        if s0 > 0u { atomicAdd(&summary[0], s0); }
        if s1 > 0u { atomicAdd(&summary[1], s1); }
        if s2 > 0u { atomicAdd(&summary[2], s2); }
        if s3 > 0u { atomicAdd(&summary[3], s3); }
    }
}
