// Zero-float exact Lean 4 arena kernel verifier (WGSL compute, @workgroup_size(64)).
// Strictly uses u32 / i32 integer & bitwise operations (no f32/f64, no SHADER_INT64).
// Any unmodeled kernel construct or resource exhaustion sets STATUS_DELEGATE so the
// host exact parallel con-ron-core checker completes it without ever silently accepting.

const STATUS_VERIFIED_GPU: u32 = 0u;
const STATUS_REJECTED_GPU: u32 = 1u;
const STATUS_DELEGATE: u32 = 2u;
const E_NODES_PAGED: bool = true;

const REASON_OK: u32 = 0u;
const REASON_NOT_ELIGIBLE: u32 = 1u;
const REASON_UNMODELED: u32 = 2u;
const REASON_STEP_BUDGET: u32 = 3u;
const REASON_STACK_BUDGET: u32 = 4u;
const REASON_SCRATCH_BUDGET: u32 = 5u;
const REASON_DUP_DECL: u32 = 10u;
const REASON_DUP_LPARAM: u32 = 11u;
const REASON_LOOSE_BVAR: u32 = 12u;
const REASON_FVAR_FREE_ERR: u32 = 13u;
const REASON_UNDECL_LPARAM: u32 = 14u;
const REASON_UNRESOLVED_CONST: u32 = 15u;
const REASON_NOT_SORT: u32 = 16u;
const REASON_THM_NOT_PROP: u32 = 17u;
const REASON_TYPE_MISMATCH: u32 = 18u;
const REASON_APP_NOT_FORALL: u32 = 19u;
const REASON_ARG_MISMATCH: u32 = 20u;
const REASON_PROJ_ERR: u32 = 21u;
const REASON_BVAR_INFER: u32 = 22u;
const REASON_LIT_UNSTORED: u32 = 23u;

const JOB_FLAG_ELIGIBLE: u32 = 1u;
const JOB_FLAG_LAZY_BVAR: u32 = 2u;
const JOB_FLAG_SPECIAL: u32 = 4u;
const JOB_FLAG_TY_GUARD_OK: u32 = 256u;
const JOB_FLAG_VAL_GUARD_OK: u32 = 512u;

const KIND_AXIOM: u32 = 0u;
const KIND_DEFN: u32 = 1u;
const KIND_THM: u32 = 2u;
const KIND_OPAQUE: u32 = 3u;
const KIND_IND: u32 = 4u;
const KIND_QUOT: u32 = 5u;

const CKIND_AXIOM: u32 = 0u;
const CKIND_DEFN: u32 = 1u;
const CKIND_THM: u32 = 2u;
const CKIND_IND: u32 = 3u;
const CKIND_CTOR: u32 = 4u;
const CKIND_REC: u32 = 5u;

const HINT_OPAQUE: u32 = 0u;
const HINT_ABBREV: u32 = 1u;
const HINT_REGULAR: u32 = 2u;

const ETAG_BVAR: u32 = 0u;
const ETAG_FVAR: u32 = 1u;
const ETAG_SORT: u32 = 2u;
const ETAG_CONST: u32 = 3u;
const ETAG_APP: u32 = 4u;
const ETAG_LAM: u32 = 5u;
const ETAG_FORALL_E: u32 = 6u;
const ETAG_LET_E: u32 = 7u;
const ETAG_LIT: u32 = 8u;
const ETAG_PROJ: u32 = 9u;

const LTAG_ZERO: u32 = 0u;
const LTAG_SUCC: u32 = 1u;
const LTAG_MAX: u32 = 2u;
const LTAG_IMAX: u32 = 3u;
const LTAG_PARAM: u32 = 4u;

const TIER_SPAN: u32 = 0x80000000u;
const WIDE_CAP: u32 = 0x40000000u;
const IDX_CAP: u32 = 0x04000000u;
const EMPTY_SENTINEL: u32 = 0xFFFFFFFFu;
const NONE_U32: u32 = 0xFFFFFFFFu;

const E_NODES_PAGE_SHIFT: u32 = 28u;
const E_NODES_PAGE_MASK: u32 = 0x0FFFFFFFu;
const MAX_BIGNAT_LIMBS: u32 = 64u;
const BIGNAT_WORK_A: u32 = 0u;
const BIGNAT_WORK_B: u32 = 64u;
const BIGNAT_WORK_OUT: u32 = 128u;

// Per-lane scratch layout prefix inside [0 .. hdr.max_scratch_words):
//   [0..192): temporary BigNat arithmetic limbs (A[64], B[64], OUT[64]),
//   [256..896): run_decl_guards seen+dfs, [896..928): check_level_lparams,
//   [960..1024): saved LDS cache, [1024..1036): VM state,
//   [1056..2080): subst epoch memo (256 slots x 4 words: key_e, key_d, gen, val)
//   [2080..hdr.max_scratch_words): bump-allocated TIER_S nodes & argument slices
const SUBST_MEMO_BASE: u32 = 1056u;
const SUBST_MEMO_SLOTS: u32 = 256u;
const SUBST_MEMO_WORDS: u32 = 1280u;
const INFER_MEMO_BASE: u32 = 2336u;
const INFER_MEMO_SLOTS: u32 = 256u;
const WHNF_MEMO_BASE: u32 = 3104u;
const WHNF_MEMO_SLOTS: u32 = 256u;
const DEFEQ_MEMO_BASE: u32 = 3872u;
const DEFEQ_MEMO_SLOTS: u32 = 256u;
const SCRATCH_ALLOC_START: u32 = 4896u;

const K_DONE: u32 = 0u;
const K_INFER: u32 = 1u;
const K_WHNF: u32 = 2u;
const K_DEFEQ: u32 = 3u;
const K_LEVEL: u32 = 4u;
const K_SUBST: u32 = 5u;

const VM_LDS_OFF: u32 = 960u;
const VM_JOB_TAG: u32 = 1024u;
const VM_TARGET_K: u32 = 1025u;
const VM_SP: u32 = 1026u;
const VM_SPTR: u32 = 1027u;
const VM_STEPS: u32 = 1028u;
const VM_RES0: u32 = 1029u;
const VM_RES1: u32 = 1030u;
const VM_STATUS: u32 = 1031u;
const VM_REASON: u32 = 1032u;
const VM_HALT: u32 = 1033u;
const VM_SUBST_GEN: u32 = 1034u;
const VM_FLAGS: u32 = 1035u;
const VM_DEFEQ_DEPTH: u32 = 1036u;
const VM_DEFEQ_SPTR: u32 = 1037u;
const VM_JOB_EPOCH: u32 = 1038u;
const VM_Q_IDX: u32 = 1039u;
const VM_Q_REM: u32 = 1040u;

// Opcodes for the iterative continuation frame stack (8 u32s per frame).
const OP_JOB_FINISH: u32 = 1u;
const OP_INFER: u32 = 2u;
const OP_WHNF: u32 = 3u;
const OP_WHNF_CORE: u32 = 4u;
const OP_DEFEQ: u32 = 5u;
const OP_INST_LP: u32 = 6u;
const OP_INST_REV: u32 = 7u;
const OP_ABS_RANGE: u32 = 8u;
const OP_DEFEQ_LAM_CHAIN: u32 = 9u;
const OP_DEFEQ_FORALL_CHAIN: u32 = 10u;
const OP_DEFEQ_SPINE: u32 = 11u;
const OP_DEFEQ_STRUCT_ETA: u32 = 12u;
const OP_LEVEL_CMP: u32 = 13u;
const OP_INFER_IO: u32 = 14u;

struct ArenaHeader {
    num_jobs: u32,
    job_offset: u32,
    verified_mode: u32,
    max_steps: u32,

    max_stack_frames: u32,
    max_scratch_words: u32,
    scratch_wg_stride: u32,
    wg_size: u32,

    off_bvar: u32,
    n_bvar: u32,
    off_bvar_der: u32,
    off_fvar: u32,

    n_fvar: u32,
    off_fvar_der: u32,
    off_sort: u32,
    n_sort: u32,

    off_sort_der: u32,
    off_const: u32,
    n_const: u32,
    off_const_der: u32,

    off_app: u32,
    n_app: u32,
    off_app_der: u32,
    off_lam: u32,

    n_lam: u32,
    off_lam_der: u32,
    off_forall: u32,
    n_forall: u32,

    off_forall_der: u32,
    off_let: u32,
    n_let: u32,
    off_let_der: u32,

    off_lit: u32,
    n_lit: u32,
    off_lit_der: u32,
    off_proj: u32,

    n_proj: u32,
    off_proj_der: u32,
    e_nodes_len: u32,
    off_l_zero_der: u32,

    n_l_zero: u32,
    off_l_succ: u32,
    n_l_succ: u32,
    off_l_succ_der: u32,

    off_l_max: u32,
    n_l_max: u32,
    off_l_max_der: u32,
    off_l_imax: u32,

    n_l_imax: u32,
    off_l_imax_der: u32,
    off_l_param: u32,
    n_l_param: u32,

    off_l_param_der: u32,
    off_ls_meta: u32,
    n_ls: u32,
    off_ls_items: u32,

    off_lit_pool: u32,
    meta_nodes_len: u32,
    off_consts: u32,
    n_consts: u32,

    off_const_hash: u32,
    const_hash_mask: u32,
    off_env_nidx: u32,
    off_rec_rules: u32,

    n_rec_rules: u32,
    off_rec_fire: u32,
    off_proj_tables: u32,
    n_proj_tables: u32,

    off_proj_hash: u32,
    proj_hash_mask: u32,
    off_env_eidx: u32,
    env_tables_len: u32,

    pin_nat: u32,
    pin_nat_zero: u32,
    pin_nat_succ: u32,
    pin_nat_pred: u32,

    pin_nat_add: u32,
    pin_nat_sub: u32,
    pin_nat_mul: u32,
    pin_nat_pow: u32,

    pin_nat_beq: u32,
    pin_nat_ble: u32,
    pin_nat_div: u32,
    pin_nat_mod: u32,

    pin_nat_gcd: u32,
    pin_nat_land: u32,
    pin_nat_lor: u32,
    pin_nat_xor: u32,

    pin_nat_shl: u32,
    pin_nat_shr: u32,
    pin_bool: u32,
    pin_bool_true: u32,

    pin_bool_false: u32,
    pin_string: u32,
    pin_eq: u32,
    pin_sorry_ax: u32,

    pin_eager_reduce: u32,
    pin_reduce_nat: u32,
    pin_reduce_bool: u32,
    pin_empty_levels: u32,

    pin_zero_level: u32,
    pin_sort_one: u32,
    pin_quot: u32,
    pin_quot_mk: u32,

    pin_quot_lift: u32,
    pin_quot_ind: u32,
    batch_epoch: u32,
    pad0: u32,
};

struct GpuJob {
    orig_decl_idx: u32,
    decl_kind: u32,
    record_pos: u32,
    base_below: u32,
    name: u32,
    ty: u32,
    val: u32,
    lparams_off: u32,
    lparams_len: u32,
    ast_size: u32,
    ast_bucket: u32,
    flags: u32,
};

struct GpuVerdict {
    status: u32,
    reason: u32,
    steps_used: u32,
    scratch_used: u32,
};

@group(0) @binding(0) var<uniform> hdr: ArenaHeader;
@group(0) @binding(1) var<storage, read> e_nodes_0: array<u32>;
@group(0) @binding(2) var<storage, read> meta_nodes: array<u32>;
@group(0) @binding(3) var<storage, read> env_tables: array<u32>;
@group(0) @binding(4) var<storage, read> jobs: array<GpuJob>;
struct ActiveCtl {
    in_count: u32,
    out_count: atomic<u32>,
    is_first_quantum: u32,
    quantum_steps: u32,
}

@group(0) @binding(5) var<storage, read_write> scratch: array<u32>;
@group(0) @binding(6) var<storage, read_write> verdicts: array<GpuVerdict>;
@group(0) @binding(7) var<storage, read_write> ctl: ActiveCtl;
@group(0) @binding(8) var<storage, read> active_in: array<vec2<u32>>;
@group(0) @binding(9) var<storage, read_write> active_out: array<vec2<u32>>;
@group(0) @binding(10) var<storage, read> e_nodes_1: array<u32>;
@group(0) @binding(11) var<storage, read> e_nodes_2: array<u32>;
@group(0) @binding(12) var<storage, read> e_nodes_3: array<u32>;
@group(0) @binding(13) var<storage, read> e_nodes_4: array<u32>;
@group(0) @binding(14) var<storage, read> e_nodes_5: array<u32>;
@group(0) @binding(15) var<storage, read> e_nodes_6: array<u32>;
@group(0) @binding(16) var<storage, read> e_nodes_7: array<u32>;

fn e_read(idx: u32) -> u32 {
    if !E_NODES_PAGED {
        return e_nodes_0[idx];
    }
    let pg = idx >> E_NODES_PAGE_SHIFT;
    let off = idx & E_NODES_PAGE_MASK;
    switch pg {
        case 0u: { return e_nodes_0[off]; }
        case 1u: { return e_nodes_1[off]; }
        case 2u: { return e_nodes_2[off]; }
        case 3u: { return e_nodes_3[off]; }
        case 4u: { return e_nodes_4[off]; }
        case 5u: { return e_nodes_5[off]; }
        case 6u: { return e_nodes_6[off]; }
        default: { return e_nodes_7[off]; }
    }
}

// 16 KB workgroup LDS: 64 words per lane x 64 lanes = 4096 u32s.
// Words [0..32) per lane: 16 direct-mapped infer cache entries [key_e, type_e]
// Words [32..64) per lane: 16 direct-mapped whnf cache entries [key_e, whnf_e]
var<workgroup> lds_cache: array<u32, 4096>;

// Per-lane private state registers.
var<private> p_wg_base: u32 = 0u;
var<private> p_lane: u32 = 0u;
var<private> p_lds_base: u32 = 0u;
var<private> p_scratch_base: u32 = 0u;
var<private> p_sp: u32 = 0u;
var<private> p_sptr: u32 = SCRATCH_ALLOC_START;
var<private> p_steps: u32 = 0u;
var<private> p_res0: u32 = 0u;
var<private> p_res1: u32 = 0u;
var<private> p_status: u32 = STATUS_VERIFIED_GPU;
var<private> p_reason: u32 = REASON_OK;
var<private> p_halt: u32 = 0u;
var<private> p_subst_gen: u32 = 1u;
var<private> p_job_epoch: u32 = 0u;
var<private> p_defeq_depth: u32 = 0u;
var<private> p_defeq_sptr: u32 = SCRATCH_ALLOC_START;

var<private> p_nat_ok: bool = false;
var<private> p_bool_ok: bool = false;
var<private> p_do_pop: bool = false;
var<private> p_req_op: u32 = 0u;
var<private> p_req_ph: u32 = 0u;
var<private> p_req_f1: u32 = 0u;
var<private> p_req_raw: bool = false;
var<private> p_req_a: u32 = 0u;
var<private> p_req_b: u32 = 0u;
var<private> p_req_c: u32 = 0u;
var<private> p_req_d: u32 = 0u;

var<private> p_decl_kind: u32 = 0u;
var<private> p_record_pos: u32 = 0u;
var<private> p_base_below: u32 = 0u;
var<private> p_job_ty: u32 = 0u;
var<private> p_job_val: u32 = 0u;
var<private> p_job_lp_off: u32 = 0u;
var<private> p_job_lp_len: u32 = 0u;
var<private> p_job_flags: u32 = 0u;

fn op_kernel(op: u32) -> u32 {
    switch op {
        case OP_JOB_FINISH, OP_INFER, OP_INFER_IO: { return K_INFER; }
        case OP_WHNF, OP_WHNF_CORE: { return K_WHNF; }
        case OP_DEFEQ, OP_DEFEQ_LAM_CHAIN, OP_DEFEQ_FORALL_CHAIN, OP_DEFEQ_SPINE, OP_DEFEQ_STRUCT_ETA: { return K_DEFEQ; }
        case OP_LEVEL_CMP: { return K_LEVEL; }
        case OP_INST_LP, OP_INST_REV, OP_ABS_RANGE: { return K_SUBST; }
        default: { return K_INFER; }
    }
}

fn vm_load_job(job: GpuJob) {
    p_decl_kind = job.decl_kind;
    p_record_pos = job.record_pos;
    p_base_below = job.base_below;
    p_job_ty = job.ty;
    p_job_val = job.val;
    p_job_lp_off = job.lparams_off;
    p_job_lp_len = job.lparams_len;
    p_job_flags = job.flags;
}

fn vm_load_state() {
    p_sp = s_read(VM_SP);
    p_sptr = s_read(VM_SPTR);
    p_steps = s_read(VM_STEPS);
    p_res0 = s_read(VM_RES0);
    p_res1 = s_read(VM_RES1);
    p_status = s_read(VM_STATUS);
    p_reason = s_read(VM_REASON);
    p_halt = s_read(VM_HALT);
    p_subst_gen = s_read(VM_SUBST_GEN);
    p_job_epoch = s_read(VM_JOB_EPOCH);
    p_defeq_depth = s_read(VM_DEFEQ_DEPTH);
    p_defeq_sptr = s_read(VM_DEFEQ_SPTR);
    let fl = s_read(VM_FLAGS);
    p_nat_ok = (fl & 1u) != 0u;
    p_bool_ok = (fl & 2u) != 0u;
    p_req_op = 0u;
}

fn vm_save_state(next_k: u32) {
    s_write(VM_TARGET_K, next_k);
    s_write(VM_SP, p_sp);
    s_write(VM_SPTR, p_sptr);
    s_write(VM_STEPS, p_steps);
    s_write(VM_RES0, p_res0);
    s_write(VM_RES1, p_res1);
    s_write(VM_STATUS, p_status);
    s_write(VM_REASON, p_reason);
    s_write(VM_HALT, p_halt);
    s_write(VM_SUBST_GEN, p_subst_gen);
    s_write(VM_JOB_EPOCH, p_job_epoch);
    s_write(VM_DEFEQ_DEPTH, p_defeq_depth);
    s_write(VM_DEFEQ_SPTR, p_defeq_sptr);
    var fl = 0u;
    if p_nat_ok { fl = fl | 1u; }
    if p_bool_ok { fl = fl | 2u; }
    s_write(VM_FLAGS, fl);
}

fn mix_hash32(h: u32) -> u32 {
    var x = h ^ (h >> 16u);
    x = x * 0x7feb352du;
    x = x ^ (x >> 15u);
    x = x * 0x846ca68bu;
    return x ^ (x >> 16u);
}

fn halt_delegate(reason: u32) {
    if p_halt == 0u {
        p_halt = 1u;
        p_status = STATUS_DELEGATE;
        p_reason = reason;
    }
}

fn halt_reject(reason: u32) {
    if p_halt == 0u {
        p_halt = 1u;
        p_status = STATUS_REJECTED_GPU;
        p_reason = reason;
    }
}

// The host intentionally omits sorryAx from its constant table and declines its use.
fn halt_unknown_const(name: u32) {
    if name == hdr.pin_sorry_ax {
        halt_delegate(REASON_UNMODELED);
    } else {
        halt_reject(REASON_UNRESOLVED_CONST);
    }
}

fn stack_word_addr(frame: u32, field: u32) -> u32 {
    return p_wg_base + (frame * 8u + field) * 64u + p_lane;
}

fn f_read(frame: u32, field: u32) -> u32 {
    return scratch[stack_word_addr(frame, field)];
}

fn f_write(frame: u32, field: u32, val: u32) {
    scratch[stack_word_addr(frame, field)] = val;
}

fn push_frame(
    op: u32,
    phase: u32,
    a0: u32,
    a1: u32,
    a2: u32,
    a3: u32,
    a4: u32,
    a5: u32,
) -> bool {
    if p_sp >= hdr.max_stack_frames {
        halt_delegate(REASON_STACK_BUDGET);
        return false;
    }
    let idx = p_sp;
    p_sp = p_sp + 1u;
    f_write(idx, 0u, op);
    f_write(idx, 1u, phase);
    f_write(idx, 2u, a0);
    f_write(idx, 3u, a1);
    f_write(idx, 4u, a2);
    f_write(idx, 5u, a3);
    f_write(idx, 6u, a4);
    f_write(idx, 7u, a5);
    return true;
}

fn scratch_safe(w: u32) -> bool {
    if w == NONE_U32 || word_tier(w) == 0u {
        return true;
    }
    let lim = select(p_sptr, p_defeq_sptr, p_defeq_depth > 0u);
    return word_index(w) < lim;
}

fn defeq_memo_get(a: u32, b: u32, depth: u32) -> u32 {
    if p_job_epoch == 0u || depth >= 0x7FFFFFFFu || a == NONE_U32 || b == NONE_U32 || !e_is_closed(a) || !e_is_closed(b) {
        return NONE_U32;
    }
    let ka = min(a, b);
    let kb = max(a, b);
    let slot = mix_hash32(ka ^ (kb * 0x9e3779b9u) ^ (depth * 0x85ebca6bu)) & 255u;
    let base = DEFEQ_MEMO_BASE + slot * 4u;
    if s_read(base) == p_job_epoch && s_read(base + 1u) == ka && s_read(base + 2u) == kb {
        let val = s_read(base + 3u);
        if (val >> 1u) == depth {
            return val & 1u;
        }
    }
    return NONE_U32;
}

fn defeq_memo_set(a: u32, b: u32, depth: u32, res: u32) {
    if p_halt != 0u || (res != 0u && res != 1u) || p_job_epoch == 0u || depth >= 0x7FFFFFFFu
        || a == NONE_U32 || b == NONE_U32 || !scratch_safe(a) || !scratch_safe(b)
    {
        return;
    }
    if !e_is_closed(a) || !e_is_closed(b) {
        return;
    }
    let ka = min(a, b);
    let kb = max(a, b);
    let slot = mix_hash32(ka ^ (kb * 0x9e3779b9u) ^ (depth * 0x85ebca6bu)) & 255u;
    let base = DEFEQ_MEMO_BASE + slot * 4u;
    s_write(base, p_job_epoch);
    s_write(base + 1u, ka);
    s_write(base + 2u, kb);
    s_write(base + 3u, (depth << 1u) | (res & 1u));
}

fn pop_ret(v0: u32, v1: u32) {
    p_res0 = v0;
    p_res1 = v1;
    p_do_pop = true;
}

fn do_pop_ret() {
    if p_sp > 0u {
        let f_idx = p_sp - 1u;
        let popped_op = f_read(f_idx, 0u);
        let ka = f_read(f_idx, 2u);
        let kb = f_read(f_idx, 3u);
        let kdepth = f_read(f_idx, 4u);
        p_sp = f_idx;
        if popped_op == OP_DEFEQ {
            if p_defeq_depth > 0u {
                p_defeq_depth = p_defeq_depth - 1u;
                if p_defeq_depth == 0u && p_sptr > p_defeq_sptr {
                    p_sptr = p_defeq_sptr;
                    for (var li = 0u; li < 64u; li = li + 2u) {
                        let ke = lds_cache[p_lds_base + li];
                        let va = lds_cache[p_lds_base + li + 1u];
                        if (ke != NONE_U32 && word_tier(ke) != 0u && word_index(ke) >= p_sptr)
                            || (va != NONE_U32 && word_tier(va) != 0u && word_index(va) >= p_sptr)
                        {
                            lds_cache[p_lds_base + li] = NONE_U32;
                            lds_cache[p_lds_base + li + 1u] = NONE_U32;
                        }
                    }
                }
            }
            defeq_memo_set(ka, kb, kdepth, p_res0);
        }
    }
}

fn s_read(word_off: u32) -> u32 {
    return scratch[p_wg_base + (p_scratch_base + word_off) * 64u + p_lane];
}

fn s_write(word_off: u32, val: u32) {
    scratch[p_wg_base + (p_scratch_base + word_off) * 64u + p_lane] = val;
}

fn s_alloc(n_words: u32) -> u32 {
    if p_sptr + n_words > hdr.max_scratch_words {
        halt_delegate(REASON_SCRATCH_BUDGET);
        return 0u;
    }
    let ptr = p_sptr;
    p_sptr = p_sptr + n_words;
    return ptr;
}

fn subst_memo_get(e: u32, d: u32) -> u32 {
    if p_job_epoch == 0u {
        return NONE_U32;
    }
    let slot = mix_hash32(e ^ (d * 0x9e3779b9u)) & 255u;
    let base = SUBST_MEMO_BASE + slot * 5u;
    if s_read(base + 2u) == p_job_epoch
        && s_read(base + 3u) == p_subst_gen
        && s_read(base) == e
        && s_read(base + 1u) == d
    {
        return s_read(base + 4u);
    }
    return NONE_U32;
}

fn subst_memo_set(e: u32, d: u32, val: u32) {
    if p_job_epoch == 0u {
        return;
    }
    let slot = mix_hash32(e ^ (d * 0x9e3779b9u)) & 255u;
    let base = SUBST_MEMO_BASE + slot * 5u;
    s_write(base, e);
    s_write(base + 1u, d);
    s_write(base + 2u, p_job_epoch);
    s_write(base + 3u, p_subst_gen);
    s_write(base + 4u, val);
}

// Handle decoding (matching con-ron-core Handle.lean)
fn word_tier(w: u32) -> u32 {
    return (w >> 31u) & 1u;
}

fn word_is_wide(w: u32) -> bool {
    return ((w >> 30u) & 1u) != 0u;
}

fn word_tag(w: u32) -> u32 {
    if word_is_wide(w) {
        return ETAG_APP;
    }
    return (w >> 26u) & 15u;
}

fn word_index(w: u32) -> u32 {
    if word_is_wide(w) {
        return w & 0x3FFFFFFFu;
    }
    return w & 0x03FFFFFFu;
}

fn word_mk_s(tag: u32, s_ptr: u32) -> u32 {
    if tag == ETAG_APP {
        return TIER_SPAN | WIDE_CAP | s_ptr;
    }
    return TIER_SPAN | ((tag & 15u) << 26u) | s_ptr;
}

fn mk_der_lo(has_lp: bool, fvar_b: u32, bvar_b: u32) -> u32 {
    var d = 0u;
    if has_lp {
        d = 1u;
    }
    let fb = min(fvar_b, 0x7FFFu);
    let bb = min(bvar_b, 0x7FFFu);
    return d | (fb << 1u) | (bb << 16u);
}

fn merge_bound(a: u32, b: u32) -> u32 {
    return min(max(a, b), 0x7FFFu);
}

fn sub_bound1(b: u32) -> u32 {
    if b >= 0x7FFFu {
        return 0x7FFFu;
    }
    if b == 0u {
        return 0u;
    }
    return b - 1u;
}

fn e_der_lo(e: u32) -> u32 {
    if word_tier(e) != 0u {
        return s_read(word_index(e));
    }
    let tg = word_tag(e);
    let idx = word_index(e);
    var off = hdr.off_bvar_der;
    off = select(off, hdr.off_fvar_der, tg == ETAG_FVAR);
    off = select(off, hdr.off_sort_der, tg == ETAG_SORT);
    off = select(off, hdr.off_const_der, tg == ETAG_CONST);
    off = select(off, hdr.off_app_der, tg == ETAG_APP);
    off = select(off, hdr.off_lam_der, tg == ETAG_LAM);
    off = select(off, hdr.off_forall_der, tg == ETAG_FORALL_E);
    off = select(off, hdr.off_let_der, tg == ETAG_LET_E);
    off = select(off, hdr.off_lit_der, tg == ETAG_LIT);
    off = select(off, hdr.off_proj_der, tg == ETAG_PROJ);
    return e_read(off + idx * 2u);
}

fn e_has_lp(e: u32) -> bool {
    return (e_der_lo(e) & 1u) != 0u;
}

fn e_fvar_b(e: u32) -> u32 {
    return (e_der_lo(e) >> 1u) & 0x7FFFu;
}

fn e_bvar_b(e: u32) -> u32 {
    return (e_der_lo(e) >> 16u) & 0x7FFFu;
}

fn e_is_closed(e: u32) -> bool {
    let d = e_der_lo(e);
    return ((d >> 1u) & 0x3FFFFFFFu) == 0u;
}

fn e_is_fvar_free(e: u32) -> bool {
    return e_fvar_b(e) == 0u;
}

fn lds_infer_get(e: u32) -> u32 {
    if e == NONE_U32 || !e_is_closed(e) {
        return NONE_U32;
    }
    let h = mix_hash32(e);
    let slot = h & 15u;
    let base = p_lds_base + slot * 2u;
    if lds_cache[base] == e {
        return lds_cache[base + 1u];
    }
    if p_job_epoch == 0u {
        return NONE_U32;
    }
    let l2 = INFER_MEMO_BASE + (h & 255u) * 3u;
    if s_read(l2) == p_job_epoch && s_read(l2 + 1u) == e {
        let r = s_read(l2 + 2u);
        lds_cache[base] = e;
        lds_cache[base + 1u] = r;
        return r;
    }
    return NONE_U32;
}

fn lds_infer_set(e: u32, ty: u32) {
    if e != NONE_U32 && e_is_closed(e) {
        let h = mix_hash32(e);
        let slot = h & 15u;
        let base = p_lds_base + slot * 2u;
        lds_cache[base] = e;
        lds_cache[base + 1u] = ty;
        if p_job_epoch != 0u && scratch_safe(e) && scratch_safe(ty) {
            let l2 = INFER_MEMO_BASE + (h & 255u) * 3u;
            s_write(l2, p_job_epoch);
            s_write(l2 + 1u, e);
            s_write(l2 + 2u, ty);
        }
    }
}

fn lds_whnf_get(e: u32) -> u32 {
    if e == NONE_U32 || !e_is_closed(e) {
        return NONE_U32;
    }
    let h = mix_hash32(e);
    let slot = h & 15u;
    let base = p_lds_base + 32u + slot * 2u;
    if lds_cache[base] == e {
        return lds_cache[base + 1u];
    }
    if p_job_epoch == 0u {
        return NONE_U32;
    }
    let l2 = WHNF_MEMO_BASE + (h & 255u) * 3u;
    if s_read(l2) == p_job_epoch && s_read(l2 + 1u) == e {
        let r = s_read(l2 + 2u);
        lds_cache[base] = e;
        lds_cache[base + 1u] = r;
        return r;
    }
    return NONE_U32;
}

fn lds_whnf_set(e: u32, w: u32) {
    if e != NONE_U32 && e_is_closed(e) {
        let h = mix_hash32(e);
        let slot = h & 15u;
        let base = p_lds_base + 32u + slot * 2u;
        lds_cache[base] = e;
        lds_cache[base + 1u] = w;
        if p_job_epoch != 0u && scratch_safe(e) && scratch_safe(w) {
            let l2 = WHNF_MEMO_BASE + (h & 255u) * 3u;
            s_write(l2, p_job_epoch);
            s_write(l2 + 1u, e);
            s_write(l2 + 2u, w);
        }
    }
}

// Expression field readers
fn view_bvar_lo(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    return e_read(hdr.off_bvar + word_index(e) * 2u);
}

fn view_bvar_hi(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 2u); }
    return e_read(hdr.off_bvar + word_index(e) * 2u + 1u);
}

fn view_fvar_lo(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    return e_read(hdr.off_fvar + word_index(e) * 3u);
}

fn view_fvar_hi(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 2u); }
    return e_read(hdr.off_fvar + word_index(e) * 3u + 1u);
}

fn view_fvar_ty(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 3u); }
    return e_read(hdr.off_fvar + word_index(e) * 3u + 2u);
}

fn view_sort_u(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    return e_read(hdr.off_sort + word_index(e));
}

fn view_const_n(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    return e_read(hdr.off_const + word_index(e) * 2u);
}

fn view_const_us(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 2u); }
    return e_read(hdr.off_const + word_index(e) * 2u + 1u);
}

fn view_app_f(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    return e_read(hdr.off_app + word_index(e) * 2u);
}

fn view_app_a(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 2u); }
    return e_read(hdr.off_app + word_index(e) * 2u + 1u);
}

fn view_bind_ty(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    if word_tag(e) == ETAG_LAM {
        return e_read(hdr.off_lam + word_index(e) * 2u);
    }
    return e_read(hdr.off_forall + word_index(e) * 2u);
}

fn view_bind_body(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 2u); }
    if word_tag(e) == ETAG_LAM {
        return e_read(hdr.off_lam + word_index(e) * 2u + 1u);
    }
    return e_read(hdr.off_forall + word_index(e) * 2u + 1u);
}

fn view_let_ty(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    return e_read(hdr.off_let + word_index(e) * 3u);
}

fn view_let_val(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 2u); }
    return e_read(hdr.off_let + word_index(e) * 3u + 1u);
}

fn view_let_body(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 3u); }
    return e_read(hdr.off_let + word_index(e) * 3u + 2u);
}

fn view_lit_kind(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    return e_read(hdr.off_lit + word_index(e) * 3u);
}

fn view_lit_a(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 2u); }
    return e_read(hdr.off_lit + word_index(e) * 3u + 1u);
}

fn view_lit_b(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 3u); }
    return e_read(hdr.off_lit + word_index(e) * 3u + 2u);
}

fn view_proj_sn(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 1u); }
    return e_read(hdr.off_proj + word_index(e) * 4u);
}

fn view_proj_idx_lo(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 2u); }
    return e_read(hdr.off_proj + word_index(e) * 4u + 1u);
}

fn view_proj_idx_hi(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 3u); }
    return e_read(hdr.off_proj + word_index(e) * 4u + 2u);
}

fn view_proj_e(e: u32) -> u32 {
    if word_tier(e) != 0u { return s_read(word_index(e) + 4u); }
    return e_read(hdr.off_proj + word_index(e) * 4u + 3u);
}

// Level & Levels readers (TIER_P uses meta_nodes; TIER_S stores [has_param, ...])
fn l_has_param(l: u32) -> bool {
    if word_tier(l) != 0u {
        return (s_read(word_index(l)) & 1u) != 0u;
    }
    let tg = word_tag(l);
    if tg >= LTAG_PARAM {
        return true;
    }
    let idx = word_index(l);
    var off = hdr.off_l_zero_der;
    off = select(off, hdr.off_l_succ_der, tg == LTAG_SUCC);
    off = select(off, hdr.off_l_max_der, tg == LTAG_MAX);
    off = select(off, hdr.off_l_imax_der, tg == LTAG_IMAX);
    return meta_nodes[off + idx * 2u + 1u] != 0u;
}

fn view_l_op0(l: u32) -> u32 {
    if word_tier(l) != 0u {
        return s_read(word_index(l) + 1u);
    }
    let tg = word_tag(l);
    let idx = word_index(l);
    let stride = select(1u, 2u, tg == LTAG_MAX || tg == LTAG_IMAX);
    var off = hdr.off_l_succ;
    off = select(off, hdr.off_l_max, tg == LTAG_MAX);
    off = select(off, hdr.off_l_imax, tg == LTAG_IMAX);
    off = select(off, hdr.off_l_param, tg == LTAG_PARAM);
    return select(0u, meta_nodes[off + idx * stride], tg >= LTAG_SUCC && tg <= LTAG_PARAM);
}

fn view_l_op1(l: u32) -> u32 {
    if word_tier(l) != 0u {
        return s_read(word_index(l) + 2u);
    }
    let tg = word_tag(l);
    let idx = word_index(l);
    let off = select(hdr.off_l_max, hdr.off_l_imax, tg == LTAG_IMAX);
    return select(0u, meta_nodes[off + idx * 2u + 1u], tg == LTAG_MAX || tg == LTAG_IMAX);
}

fn ls_len(ls: u32) -> u32 {
    if word_tier(ls) != 0u {
        return s_read(word_index(ls) + 1u);
    }
    return meta_nodes[hdr.off_ls_meta + word_index(ls) * 4u + 1u];
}

fn ls_has_param(ls: u32) -> bool {
    if word_tier(ls) != 0u {
        return (s_read(word_index(ls)) & 1u) != 0u;
    }
    return meta_nodes[hdr.off_ls_meta + word_index(ls) * 4u + 2u] != 0u;
}

fn ls_item(ls: u32, i: u32) -> u32 {
    if word_tier(ls) != 0u {
        return s_read(word_index(ls) + 2u + i);
    }
    let off = meta_nodes[hdr.off_ls_meta + word_index(ls) * 4u];
    return meta_nodes[hdr.off_ls_items + off + i];
}

// TIER_S constructors
fn intern_s_bvar(lo: u32, hi: u32) -> u32 {
    let ptr = s_alloc(3u);
    if p_halt != 0u { return 0u; }
    var bb = 0x7FFFu;
    if hi == 0u && lo < 0x7FFEu {
        bb = lo + 1u;
    }
    s_write(ptr, mk_der_lo(false, 0u, bb));
    s_write(ptr + 1u, lo);
    s_write(ptr + 2u, hi);
    return word_mk_s(ETAG_BVAR, ptr);
}

fn intern_s_fvar(idx_lo: u32, idx_hi: u32, ty: u32) -> u32 {
    let ptr = s_alloc(4u);
    if p_halt != 0u { return 0u; }
    let dty = e_der_lo(ty);
    var fb = 0x7FFFu;
    if idx_hi == 0u && idx_lo < 0x7FFEu {
        fb = max(idx_lo + 1u, (dty >> 1u) & 0x7FFFu);
    }
    s_write(ptr, mk_der_lo((dty & 1u) != 0u, fb, (dty >> 16u) & 0x7FFFu));
    s_write(ptr + 1u, idx_lo);
    s_write(ptr + 2u, idx_hi);
    s_write(ptr + 3u, ty);
    return word_mk_s(ETAG_FVAR, ptr);
}

fn intern_s_sort(u: u32) -> u32 {
    let ptr = s_alloc(2u);
    if p_halt != 0u { return 0u; }
    s_write(ptr, mk_der_lo(l_has_param(u), 0u, 0u));
    s_write(ptr + 1u, u);
    return word_mk_s(ETAG_SORT, ptr);
}

fn intern_s_const(n: u32, us: u32) -> u32 {
    let ptr = s_alloc(3u);
    if p_halt != 0u { return 0u; }
    s_write(ptr, mk_der_lo(ls_has_param(us), 0u, 0u));
    s_write(ptr + 1u, n);
    s_write(ptr + 2u, us);
    return word_mk_s(ETAG_CONST, ptr);
}

fn intern_s_app(f: u32, a: u32) -> u32 {
    let ptr = s_alloc(3u);
    if p_halt != 0u { return 0u; }
    let df = e_der_lo(f);
    let da = e_der_lo(a);
    let hl = ((df | da) & 1u) != 0u;
    let fb = merge_bound((df >> 1u) & 0x7FFFu, (da >> 1u) & 0x7FFFu);
    let bb = merge_bound((df >> 16u) & 0x7FFFu, (da >> 16u) & 0x7FFFu);
    s_write(ptr, mk_der_lo(hl, fb, bb));
    s_write(ptr + 1u, f);
    s_write(ptr + 2u, a);
    return word_mk_s(ETAG_APP, ptr);
}

fn intern_s_bind(tg: u32, ty: u32, body: u32) -> u32 {
    let ptr = s_alloc(3u);
    if p_halt != 0u { return 0u; }
    let dt = e_der_lo(ty);
    let db = e_der_lo(body);
    let hl = ((dt | db) & 1u) != 0u;
    let fb = merge_bound((dt >> 1u) & 0x7FFFu, (db >> 1u) & 0x7FFFu);
    let bb = merge_bound((dt >> 16u) & 0x7FFFu, sub_bound1((db >> 16u) & 0x7FFFu));
    s_write(ptr, mk_der_lo(hl, fb, bb));
    s_write(ptr + 1u, ty);
    s_write(ptr + 2u, body);
    return word_mk_s(tg, ptr);
}

fn intern_s_let(ty: u32, val: u32, body: u32) -> u32 {
    let ptr = s_alloc(4u);
    if p_halt != 0u { return 0u; }
    let dt = e_der_lo(ty);
    let dv = e_der_lo(val);
    let db = e_der_lo(body);
    let hl = ((dt | dv | db) & 1u) != 0u;
    let fb = merge_bound((dt >> 1u) & 0x7FFFu, merge_bound((dv >> 1u) & 0x7FFFu, (db >> 1u) & 0x7FFFu));
    let bb = merge_bound((dt >> 16u) & 0x7FFFu, merge_bound((dv >> 16u) & 0x7FFFu, sub_bound1((db >> 16u) & 0x7FFFu)));
    s_write(ptr, mk_der_lo(hl, fb, bb));
    s_write(ptr + 1u, ty);
    s_write(ptr + 2u, val);
    s_write(ptr + 3u, body);
    return word_mk_s(ETAG_LET_E, ptr);
}

fn intern_s_lit_u64(lo: u32, hi: u32) -> u32 {
    let ptr = s_alloc(4u);
    if p_halt != 0u { return 0u; }
    s_write(ptr, 0u);
    s_write(ptr + 1u, 0u);
    s_write(ptr + 2u, lo);
    s_write(ptr + 3u, hi);
    return word_mk_s(ETAG_LIT, ptr);
}

fn bignat_raw_limb(a: u32, i: u32) -> u32 {
    if (a & 0x80000000u) != 0u {
        return s_read((a & 0x7FFFFFFFu) + i);
    }
    return meta_nodes[hdr.off_lit_pool + a + i];
}

fn bignat_trimmed_len(e: u32) -> u32 {
    let k = view_lit_kind(e);
    if k == 0u {
        let lo = view_lit_a(e);
        let hi = view_lit_b(e);
        if hi != 0u { return 2u; }
        if lo != 0u { return 1u; }
        return 0u;
    }
    let a = view_lit_a(e);
    var len = view_lit_b(e);
    while len > 0u {
        if bignat_raw_limb(a, len - 1u) != 0u {
            break;
        }
        len = len - 1u;
    }
    return len;
}

fn bignat_limb(e: u32, i: u32) -> u32 {
    let k = view_lit_kind(e);
    if k == 0u {
        if i == 0u { return view_lit_a(e); }
        if i == 1u { return view_lit_b(e); }
        return 0u;
    }
    let len = view_lit_b(e);
    if i >= len { return 0u; }
    return bignat_raw_limb(view_lit_a(e), i);
}

fn intern_s_bignat_from_work(base: u32, raw_len: u32) -> u32 {
    var len = raw_len;
    while len > 0u {
        if s_read(base + len - 1u) != 0u {
            break;
        }
        len = len - 1u;
    }
    if len > MAX_BIGNAT_LIMBS {
        halt_delegate(REASON_UNMODELED);
        return NONE_U32;
    }
    if len == 0u {
        return intern_s_lit_u64(0u, 0u);
    }
    if len == 1u {
        return intern_s_lit_u64(s_read(base), 0u);
    }
    if len == 2u {
        return intern_s_lit_u64(s_read(base), s_read(base + 1u));
    }
    let limb_ptr = s_alloc(len);
    if p_halt != 0u { return NONE_U32; }
    for (var i = 0u; i < len; i = i + 1u) {
        s_write(limb_ptr + i, s_read(base + i));
    }
    let ptr = s_alloc(4u);
    if p_halt != 0u { return NONE_U32; }
    s_write(ptr, 0u);
    s_write(ptr + 1u, 1u);
    s_write(ptr + 2u, 0x80000000u | limb_ptr);
    s_write(ptr + 3u, len);
    return word_mk_s(ETAG_LIT, ptr);
}

fn intern_s_proj(sn: u32, idx_lo: u32, idx_hi: u32, e: u32) -> u32 {
    let ptr = s_alloc(5u);
    if p_halt != 0u { return 0u; }
    s_write(ptr, e_der_lo(e));
    s_write(ptr + 1u, sn);
    s_write(ptr + 2u, idx_lo);
    s_write(ptr + 3u, idx_hi);
    s_write(ptr + 4u, e);
    return word_mk_s(ETAG_PROJ, ptr);
}

fn intern_s_l_zero() -> u32 {
    return hdr.pin_zero_level;
}

fn intern_s_l_succ(u: u32) -> u32 {
    let ptr = s_alloc(2u);
    if p_halt != 0u { return 0u; }
    var hp = 0u;
    if l_has_param(u) { hp = 1u; }
    s_write(ptr, hp);
    s_write(ptr + 1u, u);
    return word_mk_s(LTAG_SUCC, ptr);
}

fn intern_s_l_max(a: u32, b: u32) -> u32 {
    let ptr = s_alloc(3u);
    if p_halt != 0u { return 0u; }
    var hp = 0u;
    if l_has_param(a) || l_has_param(b) { hp = 1u; }
    s_write(ptr, hp);
    s_write(ptr + 1u, a);
    s_write(ptr + 2u, b);
    return word_mk_s(LTAG_MAX, ptr);
}

fn intern_s_l_imax(a: u32, b: u32) -> u32 {
    let ptr = s_alloc(3u);
    if p_halt != 0u { return 0u; }
    var hp = 0u;
    if l_has_param(a) || l_has_param(b) { hp = 1u; }
    s_write(ptr, hp);
    s_write(ptr + 1u, a);
    s_write(ptr + 2u, b);
    return word_mk_s(LTAG_IMAX, ptr);
}

// Environment lookup helpers
fn env_nidx_item(off: u32, i: u32) -> u32 {
    return env_tables[hdr.off_env_nidx + off + i];
}

fn env_eidx_item(off: u32, i: u32) -> u32 {
    return env_tables[hdr.off_env_eidx + off + i];
}

fn find_const_slot_raw(name_w: u32) -> u32 {
    let mask = hdr.const_hash_mask;
    var idx = mix_hash32(name_w) & mask;
    for (var probe = 0u; probe <= mask; probe = probe + 1u) {
        let cell = hdr.off_const_hash + idx * 2u;
        let k = env_tables[cell];
        if k == EMPTY_SENTINEL {
            return NONE_U32;
        }
        if k == name_w {
            return env_tables[cell + 1u] - 1u;
        }
        idx = (idx + 1u) & mask;
    }
    return NONE_U32;
}

fn find_const_visible(name_w: u32) -> u32 {
    let s = find_const_slot_raw(name_w);
    if s == NONE_U32 || s >= p_base_below {
        return NONE_U32;
    }
    return s;
}

fn const_field(slot: u32, f: u32) -> u32 {
    return env_tables[hdr.off_consts + slot * 16u + f];
}

fn find_proj_visible(sn: u32) -> u32 {
    let mask = hdr.proj_hash_mask;
    var idx = mix_hash32(sn) & mask;
    for (var probe = 0u; probe <= mask; probe = probe + 1u) {
        let cell = hdr.off_proj_hash + idx * 2u;
        let k = env_tables[cell];
        if k == EMPTY_SENTINEL {
            return NONE_U32;
        }
        if k == sn {
            let s = env_tables[cell + 1u] - 1u;
            let rec_pos = env_tables[hdr.off_proj_tables + s * 10u + 1u];
            if rec_pos < p_record_pos {
                return s;
            }
            return NONE_U32;
        }
        idx = (idx + 1u) & mask;
    }
    return NONE_U32;
}

fn proj_field(slot: u32, f: u32) -> u32 {
    return env_tables[hdr.off_proj_tables + slot * 10u + f];
}

fn rec_rule_field(rule_idx: u32, f: u32) -> u32 {
    return env_tables[hdr.off_rec_rules + rule_idx * 6u + f];
}

// Level operations & non-recursive level_leq
fn level_is_zero(l: u32) -> bool {
    return word_tag(l) == LTAG_ZERO;
}

fn level_is_nonzero(l_in: u32) -> bool {
    var cur = l_in;
    for (var i = 0u; i < 32u; i = i + 1u) {
        let tg = word_tag(cur);
        if tg == LTAG_SUCC { return true; }
        if tg == LTAG_ZERO || tg == LTAG_PARAM { return false; }
        if tg == LTAG_IMAX {
            cur = view_l_op1(cur);
            continue;
        }
        if tg == LTAG_MAX {
            // Bounded check without recursion: inspect immediate left/right chains
            let a = view_l_op0(cur);
            let b = view_l_op1(cur);
            if word_tag(a) == LTAG_SUCC || word_tag(b) == LTAG_SUCC {
                return true;
            }
            // Conservatively recurse-unroll right if max(a, b): check b along chain
            if word_tag(a) == LTAG_IMAX {
                // Rare deep max(imax, ...): let simplify/byCases handle
                return false;
            }
            cur = b;
            continue;
        }
        return false;
    }
    return false;
}

fn level_struct_eq(a_in: u32, b_in: u32) -> bool {
    var top = 1u;
    s_write(368u, a_in);
    s_write(384u, b_in);
    for (var iter = 0u; iter < 64u; iter = iter + 1u) {
        if top == 0u { return true; }
        top = top - 1u;
        let a = s_read(368u + top);
        let b = s_read(384u + top);
        if a == b { continue; }
        let ta = word_tag(a);
        let tb = word_tag(b);
        if ta != tb { return false; }
        switch ta {
            case LTAG_ZERO: { }
            case LTAG_PARAM: {
                if view_l_op0(a) != view_l_op0(b) { return false; }
            }
            case LTAG_SUCC: {
                if top >= 16u { return false; }
                s_write(368u + top, view_l_op0(a));
                s_write(384u + top, view_l_op0(b));
                top = top + 1u;
            }
            case LTAG_MAX, LTAG_IMAX: {
                if top + 2u > 16u { return false; }
                s_write(368u + top, view_l_op0(a));
                s_write(384u + top, view_l_op0(b));
                top = top + 1u;
                s_write(368u + top, view_l_op1(a));
                s_write(384u + top, view_l_op1(b));
                top = top + 1u;
            }
            default: { return false; }
        }
    }
    return false;
}

fn level_mk_max_simp(a: u32, b: u32) -> u32 {
    if level_is_zero(a) { return b; }
    if level_is_zero(b) { return a; }
    if level_struct_eq(a, b) { return a; }
    return intern_s_l_max(a, b);
}

fn level_mk_imax_simp(a: u32, b: u32) -> u32 {
    if level_is_zero(b) { return intern_s_l_zero(); }
    if level_is_zero(a) { return b; }
    if word_tag(a) == LTAG_SUCC && level_is_zero(view_l_op0(a)) { return b; }
    if level_is_nonzero(b) { return level_mk_max_simp(a, b); }
    if level_struct_eq(a, b) { return a; }
    return intern_s_l_imax(a, b);
}

// Compare two ETAG_LIT expressions exactly (Nat64/BigNat up to arbitrary limbs, or Str pool).
fn lit_eq(a: u32, b: u32) -> bool {
    let ka = view_lit_kind(a);
    let kb = view_lit_kind(b);
    if ka <= 1u && kb <= 1u {
        if ka == 0u && kb == 0u {
            return view_lit_a(a) == view_lit_a(b) && view_lit_b(a) == view_lit_b(b);
        }
        let la = bignat_trimmed_len(a);
        let lb = bignat_trimmed_len(b);
        if la != lb {
            return false;
        }
        for (var i = 0u; i < la; i = i + 1u) {
            if bignat_limb(a, i) != bignat_limb(b, i) {
                return false;
            }
        }
        return true;
    }
    if ka == 2u && kb == 2u {
        let ab = view_lit_b(a);
        let bb = view_lit_b(b);
        if ab != bb { return false; }
        let pa = hdr.off_lit_pool + view_lit_a(a);
        let pb = hdr.off_lit_pool + view_lit_a(b);
        for (var i = 0u; i < ab; i = i + 1u) {
            if meta_nodes[pa + i] != meta_nodes[pb + i] {
                return false;
            }
        }
        return true;
    }
    return false;
}

// Iterative inst_lp on Levels: replaces params[0..lp_len] with us
fn inst_lp_level(l: u32, lp_off: u32, lp_len: u32, us: u32) -> u32 {
    if !l_has_param(l) { return l; }
    // Uses scratch [448..544): nodes[32], states[32], left_res[32]
    var sp = 1u;
    s_write(448u, l);
    s_write(480u, 0u);
    var out = l;
    for (var step = 0u; step < 1024u; step = step + 1u) {
        let top = sp - 1u;
        let cur = s_read(448u + top);
        let st = s_read(480u + top);
        let tg = word_tag(cur);
        if st == 0u {
            if !l_has_param(cur) {
                out = cur;
                sp = sp - 1u;
                if sp == 0u { return out; }
            } else if tg == LTAG_PARAM {
                let nm = view_l_op0(cur);
                out = cur;
                for (var i = 0u; i < lp_len; i = i + 1u) {
                    if env_nidx_item(lp_off, i) == nm {
                        out = ls_item(us, i);
                        break;
                    }
                }
                sp = sp - 1u;
                if sp == 0u { return out; }
            } else if tg == LTAG_SUCC {
                if sp >= 32u { halt_delegate(REASON_STACK_BUDGET); return 0u; }
                s_write(480u + top, 1u);
                s_write(448u + sp, view_l_op0(cur));
                s_write(480u + sp, 0u);
                sp = sp + 1u;
            } else {
                if sp >= 32u { halt_delegate(REASON_STACK_BUDGET); return 0u; }
                s_write(480u + top, 2u);
                s_write(448u + sp, view_l_op0(cur));
                s_write(480u + sp, 0u);
                sp = sp + 1u;
            }
        } else if st == 1u {
            let child = view_l_op0(cur);
            if out == child {
                out = cur;
            } else {
                out = intern_s_l_succ(out);
                if p_halt != 0u { return 0u; }
            }
            sp = sp - 1u;
            if sp == 0u { return out; }
        } else if st == 2u {
            s_write(512u + top, out);
            s_write(480u + top, 3u);
            if sp >= 32u { halt_delegate(REASON_STACK_BUDGET); return 0u; }
            s_write(448u + sp, view_l_op1(cur));
            s_write(480u + sp, 0u);
            sp = sp + 1u;
        } else {
            let a_orig = view_l_op0(cur);
            let b_orig = view_l_op1(cur);
            let a2 = s_read(512u + top);
            let b2 = out;
            if a2 == a_orig && b2 == b_orig {
                out = cur;
            } else if tg == LTAG_MAX {
                out = level_mk_max_simp(a2, b2);
            } else {
                out = level_mk_imax_simp(a2, b2);
            }
            if p_halt != 0u { return 0u; }
            sp = sp - 1u;
            if sp == 0u { return out; }
        }
    }
    halt_delegate(REASON_STEP_BUDGET);
    return 0u;
}

fn inst_lp_ls(ls: u32, lp_off: u32, lp_len: u32, us: u32) -> u32 {
    if !ls_has_param(ls) { return ls; }
    let len = ls_len(ls);
    let ptr = s_alloc(2u + len);
    if p_halt != 0u { return 0u; }
    var any_hp = 0u;
    var same = true;
    for (var i = 0u; i < len; i = i + 1u) {
        let orig = ls_item(ls, i);
        let r = inst_lp_level(orig, lp_off, lp_len, us);
        if p_halt != 0u { return 0u; }
        if r != orig { same = false; }
        if l_has_param(r) { any_hp = 1u; }
        s_write(ptr + 2u + i, r);
    }
    if same {
        return ls;
    }
    s_write(ptr, any_hp);
    s_write(ptr + 1u, len);
    return word_mk_s(0u, ptr);
}

fn nat_sub_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> vec2<u32> {
    if ahi < bhi || (ahi == bhi && alo <= blo) {
        return vec2<u32>(0u, 0u);
    }
    var borrow = 0u;
    if alo < blo { borrow = 1u; }
    return vec2<u32>(alo - blo, ahi - bhi - borrow);
}

fn nat_lit_to_ctor(e: u32) -> u32 {
    if word_tag(e) != ETAG_LIT || view_lit_kind(e) > 1u {
        halt_delegate(REASON_UNMODELED);
        return 0u;
    }
    if view_lit_kind(e) == 0u {
        let alo = view_lit_a(e);
        let ahi = view_lit_b(e);
        if alo == 0u && ahi == 0u {
            return intern_s_const(hdr.pin_nat_zero, hdr.pin_empty_levels);
        }
        let pred = nat_sub_u64(alo, ahi, 1u, 0u);
        let lit = intern_s_lit_u64(pred.x, pred.y);
        let sc = intern_s_const(hdr.pin_nat_succ, hdr.pin_empty_levels);
        if p_halt != 0u { return 0u; }
        return intern_s_app(sc, lit);
    }
    let len = bignat_trimmed_len(e);
    if len == 0u {
        return intern_s_const(hdr.pin_nat_zero, hdr.pin_empty_levels);
    }
    if len <= 2u {
        let pred = nat_sub_u64(bignat_limb(e, 0u), bignat_limb(e, 1u), 1u, 0u);
        let lit = intern_s_lit_u64(pred.x, pred.y);
        let sc = intern_s_const(hdr.pin_nat_succ, hdr.pin_empty_levels);
        if p_halt != 0u { return 0u; }
        return intern_s_app(sc, lit);
    }
    if len > MAX_BIGNAT_LIMBS {
        halt_delegate(REASON_UNMODELED);
        return 0u;
    }
    var borrow = 1u;
    for (var i = 0u; i < len; i = i + 1u) {
        let limb = bignat_limb(e, i);
        let d = limb - borrow;
        let next_b = select(0u, 1u, limb < borrow);
        s_write(BIGNAT_WORK_OUT + i, d);
        borrow = next_b;
    }
    let lit = intern_s_bignat_from_work(BIGNAT_WORK_OUT, len);
    if p_halt != 0u { return 0u; }
    let sc = intern_s_const(hdr.pin_nat_succ, hdr.pin_empty_levels);
    if p_halt != 0u { return 0u; }
    return intern_s_app(sc, lit);
}

// Helper: build n-ary App node from spine head + s_read(args_ptr + 0..argc-1)
fn mk_app_slice(head: u32, args_ptr: u32, start: u32, end: u32) -> u32 {
    var cur = head;
    for (var i = start; i < end; i = i + 1u) {
        cur = intern_s_app(cur, s_read(args_ptr + i));
        if p_halt != 0u { return 0u; }
    }
    return cur;
}

fn mk_app_slice_rebuilt(
    head: u32,
    same_head: bool,
    args_ptr: u32,
    nodes_ptr: u32,
    argc: u32,
) -> u32 {
    if same_head && argc > 0u {
        return s_read(nodes_ptr + argc - 1u);
    }
    return mk_app_slice(head, args_ptr, 0u, argc);
}

// Handle-compatible fast check: is e syntactically head-normal stuck (Sort, FVar, ForallE, Const, Lit)?
fn is_stuck_head_tag(tg: u32) -> bool {
    return tg == ETAG_SORT || tg == ETAG_FVAR || tg == ETAG_FORALL_E || tg == ETAG_CONST || tg == ETAG_LIT;
}

// Structural head comparison for equal regular height fast-path (same_const_heads)
fn extract_spine_head(e_in: u32) -> u32 {
    var cur = e_in;
    for (var i = 0u; i < 256u; i = i + 1u) {
        if word_tag(cur) != ETAG_APP { return cur; }
        cur = view_app_f(cur);
    }
    return cur;
}

fn head_const_slot(e_in: u32) -> u32 {
    let hd = extract_spine_head(e_in);
    if word_tag(hd) != ETAG_CONST { return NONE_U32; }
    let s = find_const_visible(view_const_n(hd));
    if s == NONE_U32 { return NONE_U32; }
    if const_field(s, 0u) != CKIND_DEFN { return NONE_U32; }
    if ls_len(view_const_us(hd)) != const_field(s, 5u) { return NONE_U32; }
    return s;
}

fn hint_lt(h1_kind: u32, h1_ht: u32, h2_kind: u32, h2_ht: u32) -> bool {
    if h2_kind == HINT_OPAQUE { return false; }
    if h2_kind == HINT_ABBREV { return h1_kind != HINT_ABBREV; }
    // h2_kind == HINT_REGULAR
    if h1_kind == HINT_ABBREV { return false; }
    if h1_kind == HINT_OPAQUE { return true; }
    return h1_ht < h2_ht;
}

// Centralized deferred sub-frame call request (dispatched once per main loop step).
fn req_call(next_ph: u32, op: u32, a: u32, b: u32, c: u32, d: u32) {
    p_req_op = op;
    p_req_ph = next_ph;
    p_req_f1 = 0u;
    p_req_raw = false;
    p_req_a = a;
    p_req_b = b;
    p_req_c = c;
    p_req_d = d;
}

fn req_raw(next_ph: u32, op: u32, f1: u32, a: u32, b: u32, c: u32, d: u32) {
    p_req_op = op;
    p_req_ph = next_ph;
    p_req_f1 = f1;
    p_req_raw = true;
    p_req_a = a;
    p_req_b = b;
    p_req_c = c;
    p_req_d = d;
}

fn dispatch_req(top: u32) {
    f_write(top, 1u, p_req_ph);
    var do_push = true;
    var f4 = p_req_c;
    if !p_req_raw {
        if p_req_op == OP_INFER || p_req_op == OP_INFER_IO {
            let cached = lds_infer_get(p_req_a);
            if cached != NONE_U32 { p_res0 = cached; do_push = false; }
            f4 = p_req_a;
        } else if p_req_op == OP_WHNF {
            let cached = lds_whnf_get(p_req_a);
            if cached != NONE_U32 { p_res0 = cached; do_push = false; }
            f4 = p_req_a;
        } else if p_req_op == OP_WHNF_CORE {
            let tg = word_tag(p_req_a);
            if is_stuck_head_tag(tg) || tg == ETAG_LAM { p_res0 = p_req_a; do_push = false; }
        } else if p_req_op == OP_DEFEQ {
            if p_req_a == p_req_b { p_res0 = 1u; do_push = false; }
            else if word_tag(p_req_a) == ETAG_LIT && word_tag(p_req_b) == ETAG_LIT {
                p_res0 = select(0u, 1u, lit_eq(p_req_a, p_req_b));
                do_push = false;
            } else {
                let d_cached = defeq_memo_get(p_req_a, p_req_b, p_req_c);
                if d_cached != NONE_U32 {
                    p_res0 = d_cached;
                    do_push = false;
                }
            }
        } else if p_req_op == OP_INST_LP {
            if !e_has_lp(p_req_a) || p_req_c == 0u { p_res0 = p_req_a; do_push = false; }
            else if p_subst_gen == 0xFFFFFFFFu { halt_delegate(REASON_UNMODELED); return; }
            else { p_subst_gen = p_subst_gen + 1u; }
        } else if p_req_op == OP_INST_REV {
            let bb = e_bvar_b(p_req_a);
            if bb < 0x7FFFu && bb <= p_req_d { p_res0 = p_req_a; do_push = false; }
            else if p_subst_gen == 0xFFFFFFFFu { halt_delegate(REASON_UNMODELED); return; }
            else { p_subst_gen = p_subst_gen + 1u; }
        } else if p_req_op == OP_ABS_RANGE {
            let fb = e_fvar_b(p_req_a);
            if (fb < 0x7FFFu && fb <= p_req_b) || p_req_c == 0u { p_res0 = p_req_a; do_push = false; }
            else if p_subst_gen == 0xFFFFFFFFu { halt_delegate(REASON_UNMODELED); return; }
            else { p_subst_gen = p_subst_gen + 1u; }
        }
    }
    if do_push {
        let push_ok = push_frame(p_req_op, p_req_f1, p_req_a, p_req_b, f4, p_req_d, 0u, 0u);
        if push_ok && p_req_op == OP_DEFEQ {
            if p_defeq_depth == 0u {
                p_defeq_sptr = p_sptr;
            }
            p_defeq_depth = p_defeq_depth + 1u;
        }
    }
}

// =========================================================================
// Continuation State Machine Step
// =========================================================================

fn exec_subst(top: u32, op: u32) {
    let phase = f_read(top, 1u);
    let e = f_read(top, 2u);
    let a0 = f_read(top, 3u);
    let a1 = f_read(top, 4u);
    let a2 = f_read(top, 5u);
    let tg = word_tag(e);
    let memo_k = select(a2, 0u, op == OP_INST_LP);

    var push_e = NONE_U32;
    var push_next_phase = 0u;
    var push_a2 = a2;

    if phase == 0u {
        if op == OP_INST_LP {
            if !e_has_lp(e) {
                pop_ret(e, 0u);
                return;
            }
        } else if op == OP_INST_REV {
            let bb = e_bvar_b(e);
            if bb < 0x7FFFu && bb <= a2 {
                pop_ret(e, 0u);
                return;
            }
            if tg == ETAG_BVAR {
                if view_bvar_hi(e) != 0u {
                    halt_delegate(REASON_UNMODELED);
                    return;
                }
                let j = view_bvar_lo(e);
                if j < a2 {
                    pop_ret(e, 0u);
                    return;
                }
                let rel = j - a2;
                if rel < a1 {
                    let vi = s_read(a0 + (a1 - 1u - rel));
                    let vbb = e_bvar_b(vi);
                    if vbb == 0u || a2 == 0u {
                        pop_ret(vi, 0u);
                        return;
                    }
                    if word_tag(vi) == ETAG_BVAR && view_bvar_hi(vi) == 0u {
                        pop_ret(intern_s_bvar(view_bvar_lo(vi) + a2, 0u), 0u);
                        return;
                    }
                    halt_delegate(REASON_UNMODELED);
                    return;
                }
                pop_ret(intern_s_bvar(j - a1, 0u), 0u);
                return;
            }
        } else {
            // OP_ABS_RANGE
            let fb = e_fvar_b(e);
            if fb < 0x7FFFu && fb <= a0 {
                pop_ret(e, 0u);
                return;
            }
            if tg == ETAG_FVAR {
                if view_fvar_hi(e) != 0u {
                    halt_delegate(REASON_UNMODELED);
                    return;
                }
                let idx = view_fvar_lo(e);
                if idx >= a0 && idx < a0 + a1 {
                    pop_ret(intern_s_bvar(a2 + (a0 + a1 - 1u - idx), 0u), 0u);
                    return;
                }
                pop_ret(e, 0u);
                return;
            }
        }

        let m = subst_memo_get(e, memo_k);
        if m != NONE_U32 {
            pop_ret(m, 0u);
            return;
        }

        if op == OP_INST_LP && (tg == ETAG_SORT || tg == ETAG_CONST) {
            var r = e;
            if tg == ETAG_SORT {
                let u0 = view_sort_u(e);
                let u2 = inst_lp_level(u0, a0, a1, a2);
                if p_halt != 0u { return; }
                if u2 != u0 { r = intern_s_sort(u2); }
            } else {
                let us0 = view_const_us(e);
                let us2 = inst_lp_ls(us0, a0, a1, a2);
                if p_halt != 0u { return; }
                if us2 != us0 { r = intern_s_const(view_const_n(e), us2); }
            }
            if p_halt != 0u { return; }
            subst_memo_set(e, 0u, r);
            pop_ret(r, 0u);
            return;
        }

        switch tg {
            case ETAG_BVAR, ETAG_FVAR, ETAG_SORT, ETAG_CONST, ETAG_LIT: {
                pop_ret(e, 0u);
            }
            case ETAG_APP: {
                push_e = view_app_f(e);
                push_next_phase = 1u;
            }
            case ETAG_LAM, ETAG_FORALL_E: {
                push_e = view_bind_ty(e);
                push_next_phase = 3u;
            }
            case ETAG_LET_E: {
                push_e = view_let_ty(e);
                push_next_phase = 5u;
            }
            case ETAG_PROJ: {
                push_e = view_proj_e(e);
                push_next_phase = 8u;
            }
            default: { halt_delegate(REASON_UNMODELED); }
        }
    } else if phase == 1u {
        f_write(top, 6u, p_res0);
        push_e = view_app_a(e);
        push_next_phase = 2u;
    } else if phase == 2u {
        let f2 = f_read(top, 6u);
        let a2_c = p_res0;
        var r = e;
        if f2 != view_app_f(e) || a2_c != view_app_a(e) { r = intern_s_app(f2, a2_c); }
        if p_halt != 0u { return; }
        subst_memo_set(e, memo_k, r);
        pop_ret(r, 0u);
    } else if phase == 3u {
        f_write(top, 6u, p_res0);
        push_e = view_bind_body(e);
        push_next_phase = 4u;
        push_a2 = select(a2 + 1u, a2, op == OP_INST_LP);
    } else if phase == 4u {
        let ty2 = f_read(top, 6u);
        let b2 = p_res0;
        var r = e;
        if ty2 != view_bind_ty(e) || b2 != view_bind_body(e) { r = intern_s_bind(tg, ty2, b2); }
        if p_halt != 0u { return; }
        subst_memo_set(e, memo_k, r);
        pop_ret(r, 0u);
    } else if phase == 5u {
        f_write(top, 6u, p_res0);
        push_e = view_let_val(e);
        push_next_phase = 6u;
    } else if phase == 6u {
        f_write(top, 7u, p_res0);
        push_e = view_let_body(e);
        push_next_phase = 7u;
        push_a2 = select(a2 + 1u, a2, op == OP_INST_LP);
    } else if phase == 7u {
        let ty2 = f_read(top, 6u);
        let v2 = f_read(top, 7u);
        let b2 = p_res0;
        let same = ty2 == view_let_ty(e) && v2 == view_let_val(e) && b2 == view_let_body(e);
        var r = e;
        if !same { r = intern_s_let(ty2, v2, b2); }
        if p_halt != 0u { return; }
        subst_memo_set(e, memo_k, r);
        pop_ret(r, 0u);
    } else {
        let pe2 = p_res0;
        var r = e;
        if pe2 != view_proj_e(e) {
            r = intern_s_proj(view_proj_sn(e), view_proj_idx_lo(e), view_proj_idx_hi(e), pe2);
        }
        if p_halt != 0u { return; }
        subst_memo_set(e, memo_k, r);
        pop_ret(r, 0u);
    }

    if push_e != NONE_U32 {
        req_raw(push_next_phase, op, 0u, push_e, a0, a1, push_a2);
    }
}

