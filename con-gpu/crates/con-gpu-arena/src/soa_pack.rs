use std::collections::{HashMap, HashSet};
use std::time::Instant;

use bytemuck::{Pod, Zeroable};

use con_ron_core::arena::env::{
    IConstantInfo, IDeclaration, IProjTable, IRecRuleFire,
};
use con_ron_core::arena::handle::{
    EIdx, LIdx, LsIdx, NIdx, ETAG_APP, ETAG_BVAR, ETAG_CONST, ETAG_FORALL_E, ETAG_FVAR,
    ETAG_LAM, ETAG_LET_E, ETAG_LIT, ETAG_PROJ, ETAG_SORT, LSTAG_LIST, LTAG_IMAX, LTAG_MAX,
    LTAG_PARAM, LTAG_SUCC, LTAG_ZERO, NTAG_NUM, NTAG_STR, TIER_P, TIER_S,
};
use con_ron_core::arena::pins::{
    PIN_AND, PIN_AND_INTRO, PIN_AND_REC, PIN_BOOL, PIN_BOOL_FALSE, PIN_BOOL_TRUE,
    PIN_EAGER_REDUCE, PIN_EQ, PIN_NAT, PIN_NAT_ADD, PIN_NAT_BEQ, PIN_NAT_BLE, PIN_NAT_DIV,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_MOD, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_PRED,
    PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT, PIN_NAT_SUB, PIN_NAT_SUCC, PIN_NAT_XOR,
    PIN_NAT_ZERO, PIN_QUOT, PIN_QUOT_MK, PIN_QUOT_SOUND, PIN_REDUCE_BOOL, PIN_REDUCE_NAT,
    PIN_SORRY_AX, PIN_STRING,
};
use con_ron_core::arena::store::{
    AppNode, BVarNode, BindNode, ConstNode, FVarNode, LetNode, ListNode, LitNode, NTables,
    NumNode, PersTier, ProjNode, SortNode, StrNode, Tbl, ZeroNode, SuccNode, BinLNode, ParamNode,
};
use con_ron_core::kernel::env::ReducibilityHint;
use con_ron_core::kernel::expr::Literal;
use con_ron_core::ron::nat::Nat;

use crate::loader::LoadedEnvironment;

pub const STATUS_VERIFIED_GPU: u32 = 0;
pub const STATUS_REJECTED_GPU: u32 = 1;
pub const STATUS_DELEGATE: u32 = 2;

/// Number of `u32` words in one paged `e_nodes` GPU binding (`1 GiB` per page).
pub const E_NODES_PAGE_WORDS: usize = 1 << 28;
/// Number of `e_nodes` storage pages supported in the GPU pipeline (`8 GiB` total).
pub const E_NODES_NUM_PAGES: usize = 8;
/// Maximum packed `e_nodes` words across all `E_NODES_NUM_PAGES` pages (`2^31` words = `8 GiB`).
pub const MAX_E_NODES_WORDS: usize = E_NODES_PAGE_WORDS * E_NODES_NUM_PAGES;
/// Maximum limb count (`u32` words) for GPU arbitrary-precision `BigNat` operations (`2,048` bits).
pub const MAX_BIGNAT_LIMBS: usize = 64;

pub const EMPTY_NIDX_SENTINEL: u32 = 0xFFFF_FFFF;

pub const JOB_FLAG_ELIGIBLE: u32 = 1 << 0;
pub const JOB_FLAG_LAZY_BVAR: u32 = 1 << 1;
pub const JOB_FLAG_SPECIAL: u32 = 1 << 2;
pub const JOB_FLAG_TY_GUARD_OK: u32 = 1 << 8;
pub const JOB_FLAG_VAL_GUARD_OK: u32 = 1 << 9;

const LP_MASK_OVERFLOW: u64 = 1u64 << 62;

#[repr(u32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum JobKind {
    Axiom = 0,
    Defn = 1,
    Thm = 2,
    Opaque = 3,
    Ind = 4,
    Quot = 5,
}

#[derive(Clone, Copy, Debug)]
pub struct ArenaLimitsConfig {
    pub max_steps: u32,
    pub max_stack_frames: u32,
    pub max_scratch_words: u32,
    pub workgroup_size: u32,
}

impl Default for ArenaLimitsConfig {
    fn default() -> Self {
        Self {
            max_steps: 131_072,
            max_stack_frames: 384,
            max_scratch_words: 21_280,
            workgroup_size: 64,
        }
    }
}

/// Uniform metadata buffer uploaded to `@group(0) @binding(0)`.
/// Uses strictly `u32` fields (no `f32`/`f64`, no WGSL uniform array stride hazards),
/// padded to a multiple of 16 bytes.
#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct ArenaHeader {
    pub num_jobs: u32,
    pub job_offset: u32,
    pub verified_mode: u32,
    pub max_steps: u32,

    pub max_stack_frames: u32,
    pub max_scratch_words: u32,
    pub scratch_wg_stride: u32,
    pub wg_size: u32,

    // Offsets into `e_nodes` (`array<u32>`)
    pub off_bvar: u32,
    pub n_bvar: u32,
    pub off_bvar_der: u32,
    pub off_fvar: u32,

    pub n_fvar: u32,
    pub off_fvar_der: u32,
    pub off_sort: u32,
    pub n_sort: u32,

    pub off_sort_der: u32,
    pub off_const: u32,
    pub n_const: u32,
    pub off_const_der: u32,

    pub off_app: u32,
    pub n_app: u32,
    pub off_app_der: u32,
    pub off_lam: u32,

    pub n_lam: u32,
    pub off_lam_der: u32,
    pub off_forall: u32,
    pub n_forall: u32,

    pub off_forall_der: u32,
    pub off_let: u32,
    pub n_let: u32,
    pub off_let_der: u32,

    pub off_lit: u32,
    pub n_lit: u32,
    pub off_lit_der: u32,
    pub off_proj: u32,

    pub n_proj: u32,
    pub off_proj_der: u32,
    pub e_nodes_len: u32,
    pub off_l_zero_der: u32,

    // Offsets into `meta_nodes` (`array<u32>`)
    pub n_l_zero: u32,
    pub off_l_succ: u32,
    pub n_l_succ: u32,
    pub off_l_succ_der: u32,

    pub off_l_max: u32,
    pub n_l_max: u32,
    pub off_l_max_der: u32,
    pub off_l_imax: u32,

    pub n_l_imax: u32,
    pub off_l_imax_der: u32,
    pub off_l_param: u32,
    pub n_l_param: u32,

    pub off_l_param_der: u32,
    pub off_ls_meta: u32,
    pub n_ls: u32,
    pub off_ls_items: u32,

    pub off_lit_pool: u32,
    pub meta_nodes_len: u32,
    // Offsets into `env_tables` (`array<u32>`)
    pub off_consts: u32,
    pub n_consts: u32,

    pub off_const_hash: u32,
    pub const_hash_mask: u32,
    pub off_env_nidx: u32,
    pub off_rec_rules: u32,

    pub n_rec_rules: u32,
    pub off_rec_fire: u32,
    pub off_proj_tables: u32,
    pub n_proj_tables: u32,

    pub off_proj_hash: u32,
    pub proj_hash_mask: u32,
    pub off_env_eidx: u32,
    pub env_tables_len: u32,

    // Pinned handles
    pub pin_nat: u32,
    pub pin_nat_zero: u32,
    pub pin_nat_succ: u32,
    pub pin_nat_pred: u32,

    pub pin_nat_add: u32,
    pub pin_nat_sub: u32,
    pub pin_nat_mul: u32,
    pub pin_nat_pow: u32,

    pub pin_nat_beq: u32,
    pub pin_nat_ble: u32,
    pub pin_nat_div: u32,
    pub pin_nat_mod: u32,

    pub pin_nat_gcd: u32,
    pub pin_nat_land: u32,
    pub pin_nat_lor: u32,
    pub pin_nat_xor: u32,

    pub pin_nat_shl: u32,
    pub pin_nat_shr: u32,
    pub pin_bool: u32,
    pub pin_bool_true: u32,

    pub pin_bool_false: u32,
    pub pin_string: u32,
    pub pin_eq: u32,
    pub pin_sorry_ax: u32,

    pub pin_eager_reduce: u32,
    pub pin_reduce_nat: u32,
    pub pin_reduce_bool: u32,
    pub pin_empty_levels: u32,

    pub pin_zero_level: u32,
    pub pin_sort_one: u32,
    pub pin_quot: u32,
    pub pin_quot_mk: u32,

    pub pin_quot_lift: u32,
    pub pin_quot_ind: u32,
    pub batch_epoch: u32,
    pub pad0: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct GpuJob {
    pub orig_decl_idx: u32,
    pub decl_kind: u32,
    pub record_pos: u32,
    pub base_below: u32,
    pub name: u32,
    pub ty: u32,
    pub val: u32,
    pub lparams_off: u32,
    pub lparams_len: u32,
    pub ast_size: u32,
    pub ast_bucket: u32,
    pub flags: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct GpuVerdict {
    pub status: u32,
    pub reason: u32,
    pub steps_used: u32,
    pub scratch_used: u32,
}

#[derive(Clone, Debug)]
pub struct GpuArenaPacket {
    pub header: ArenaHeader,
    pub e_nodes: Vec<u32>,
    pub meta_nodes: Vec<u32>,
    pub env_tables: Vec<u32>,
    pub jobs: Vec<GpuJob>,
    pub eligible_jobs_count: usize,
    pub pack_ns: u128,
}

pub fn mix_hash32(h: u32) -> u32 {
    let mut x = h ^ (h >> 16);
    x = x.wrapping_mul(0x7feb352d);
    x ^= x >> 15;
    x = x.wrapping_mul(0x846ca68b);
    x ^ (x >> 16)
}

fn pers_peel_pis_ok(pers: &PersTier, k: u64, mut e_word: u32) -> bool {
    let mut rem = k;
    while rem > 0 {
        let ei = EIdx::of_word(e_word);
        if !ei.is_persistent() || ei.tag() != ETAG_FORALL_E {
            return false;
        }
        let Some((node, _)) = pers.e.foralls.rows.get(ei.idx_nat()) else {
            return false;
        };
        e_word = node.body.word;
        rem -= 1;
    }
    true
}

fn find_quot_child_names(pers: &PersTier, pin_quot: u32) -> (u32, u32) {
    let quot_cps: [u32; 4] = [81, 117, 111, 116];
    let lift_cps: [u32; 4] = [108, 105, 102, 116];
    let ind_cps: [u32; 3] = [105, 110, 100];
    let is_quot_name = |w: u32| -> bool {
        if pin_quot != 0 && w == pin_quot {
            return true;
        }
        let ni = NIdx::of_word(w);
        if !ni.is_persistent() || ni.tag() != NTAG_STR {
            return false;
        }
        pers.n
            .strs
            .rows
            .get(ni.idx_nat())
            .map(|(node, _)| node.pre.word == 0 && node.s.as_slice() == quot_cps)
            .unwrap_or(false)
    };
    let mut lift_w = 0u32;
    let mut ind_w = 0u32;
    for (row_idx, (StrNode { pre, s }, _)) in pers.n.strs.rows.iter().enumerate() {
        if is_quot_name(pre.word) {
            if s.as_slice() == lift_cps {
                lift_w = NIdx::pack(NTAG_STR, TIER_P, row_idx as u32).word;
            } else if s.as_slice() == ind_cps {
                ind_w = NIdx::pack(NTAG_STR, TIER_P, row_idx as u32).word;
            }
            if lift_w != 0 && ind_w != 0 {
                break;
            }
        }
    }
    (lift_w, ind_w)
}

fn push_der<A, I>(der_out: &mut Vec<u32>, tbl: &Tbl<A, I, u64>) {
    der_out.reserve(tbl.rows.len() * 2);
    for (_, d) in &tbl.rows {
        let w = *d;
        der_out.push((w & 0xFFFF_FFFF) as u32);
        der_out.push((w >> 32) as u32);
    }
}

fn nat_to_u64_exact(n: &Nat) -> Option<u64> {
    if n.limbs.is_empty() {
        Some(0)
    } else if n.limbs.len() == 1 {
        Some(n.limbs[0])
    } else {
        None
    }
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
struct ExprSummary {
    lp_mask: u64,
    bvar_b: u64,
    max_const_slotp1: u32,
    max_const_recp1: u32,
    fvar_b: u32,
    size_sat: u32,
}

impl ExprSummary {
    const LIT: Self = Self {
        lp_mask: 0,
        bvar_b: 0,
        max_const_slotp1: 0,
        max_const_recp1: 0,
        fvar_b: 0,
        size_sat: 1,
    };

    const INVALID: Self = Self {
        lp_mask: LP_MASK_OVERFLOW,
        bvar_b: u64::MAX,
        max_const_slotp1: u32::MAX,
        max_const_recp1: u32::MAX,
        fvar_b: 1,
        size_sat: 4096,
    };

    #[inline]
    fn combine(self, other: Self) -> Self {
        Self {
            lp_mask: self.lp_mask | other.lp_mask,
            bvar_b: self.bvar_b.max(other.bvar_b),
            max_const_slotp1: self.max_const_slotp1.max(other.max_const_slotp1),
            max_const_recp1: self.max_const_recp1.max(other.max_const_recp1),
            fvar_b: self.fvar_b.max(other.fvar_b),
            size_sat: self.size_sat.saturating_add(other.size_sat).min(4096),
        }
    }

    #[inline]
    fn shift_binder(mut self) -> Self {
        self.bvar_b = self.bvar_b.saturating_sub(1);
        self
    }
}

struct DagSummaries {
    lp_name_to_bit: HashMap<u32, u8>,
    e_fvar: Vec<ExprSummary>,
    e_app: Vec<ExprSummary>,
    e_lam: Vec<ExprSummary>,
    e_forall: Vec<ExprSummary>,
    e_let: Vec<ExprSummary>,
    e_proj: Vec<ExprSummary>,
    e_bvar: Vec<ExprSummary>,
    e_sort: Vec<ExprSummary>,
    e_const: Vec<ExprSummary>,
    n_lit: usize,
    sparse: Option<HashMap<u32, ExprSummary>>,
}

fn has_dup_u32(xs: &[u32]) -> bool {
    if xs.len() <= 16 {
        for i in 0..xs.len() {
            for j in (i + 1)..xs.len() {
                if xs[i] == xs[j] {
                    return true;
                }
            }
        }
        false
    } else {
        let mut seen = HashSet::with_capacity(xs.len());
        xs.iter().any(|&x| !seen.insert(x))
    }
}

fn compute_slot_to_rec(num_consts: usize, firsts: &[u64]) -> Vec<u32> {
    let mut slot_to_rec = vec![0u32; num_consts];
    let mut rec_cursor = 0usize;
    for (s, dst) in slot_to_rec.iter_mut().enumerate() {
        while rec_cursor + 1 < firsts.len() && (s as u64) >= firsts[rec_cursor + 1] {
            rec_cursor += 1;
        }
        *dst = rec_cursor as u32;
    }
    slot_to_rec
}

fn build_lp_name_to_bit(pers: &PersTier) -> (HashMap<u32, u8>, Vec<u64>) {
    let mut lp_name_to_bit: HashMap<u32, u8> =
        HashMap::with_capacity(pers.l.params.rows.len().min(64));
    let mut next_bit: u8 = 0;
    let mut l_param_mask = vec![0u64; pers.l.params.rows.len()];
    for (row, (ParamNode { n }, _)) in pers.l.params.rows.iter().enumerate() {
        let bit = *lp_name_to_bit.entry(n.word).or_insert_with(|| {
            let b = next_bit;
            if next_bit < 62 {
                next_bit += 1;
            }
            b
        });
        l_param_mask[row] = if bit < 62 {
            1u64 << bit
        } else {
            LP_MASK_OVERFLOW
        };
    }
    (lp_name_to_bit, l_param_mask)
}

#[inline]
fn eval_const_summary(
    first_const_slot: &HashMap<u32, u32>,
    slot_to_rec: &[u32],
    name_word: u32,
    lp_mask: u64,
) -> ExprSummary {
    let (slotp1, recp1) = match first_const_slot.get(&name_word) {
        None => (u32::MAX, u32::MAX),
        Some(&slot) => {
            let rec = slot_to_rec.get(slot as usize).copied().unwrap_or(u32::MAX - 1);
            (slot.saturating_add(1), rec.saturating_add(1))
        }
    };
    ExprSummary {
        lp_mask,
        bvar_b: 0,
        max_const_slotp1: slotp1,
        max_const_recp1: recp1,
        fvar_b: 0,
        size_sat: 1,
    }
}

#[inline]
fn eval_bvar_summary(i: u64) -> ExprSummary {
    if i == u64::MAX {
        ExprSummary::INVALID
    } else {
        ExprSummary {
            lp_mask: 0,
            bvar_b: i.saturating_add(1),
            max_const_slotp1: 0,
            max_const_recp1: 0,
            fvar_b: 0,
            size_sat: 1,
        }
    }
}

fn level_mask_sparse(
    pers: &PersTier,
    l_param_mask: &[u64],
    l_memo: &mut HashMap<u32, u64>,
    root_word: u32,
) -> u64 {
    if let Some(&m) = l_memo.get(&root_word) {
        return m;
    }
    let mut state: HashMap<u32, u8> = HashMap::new();
    let mut stack = vec![(root_word, false)];
    while let Some((cur_w, expanded)) = stack.pop() {
        if l_memo.contains_key(&cur_w) {
            continue;
        }
        let li = LIdx::of_word(cur_w);
        if !li.is_persistent() {
            l_memo.insert(cur_w, LP_MASK_OVERFLOW);
            continue;
        }
        let r = li.idx_nat();
        let t = li.tag();
        if t == LTAG_ZERO {
            let m = if r < pers.l.zeros.rows.len() { 0 } else { LP_MASK_OVERFLOW };
            l_memo.insert(cur_w, m);
            continue;
        }
        if t == LTAG_PARAM {
            let m = l_param_mask.get(r).copied().unwrap_or(LP_MASK_OVERFLOW);
            l_memo.insert(cur_w, m);
            continue;
        }
        if !expanded {
            if state.get(&cur_w).copied() == Some(1) {
                l_memo.insert(cur_w, LP_MASK_OVERFLOW);
                continue;
            }
            state.insert(cur_w, 1);
            stack.push((cur_w, true));
            match t {
                x if x == LTAG_SUCC => {
                    if let Some((SuccNode { u }, _)) = pers.l.succs.rows.get(r) {
                        if !l_memo.contains_key(&u.word) && state.get(&u.word).copied() != Some(1) {
                            stack.push((u.word, false));
                        }
                    } else {
                        l_memo.insert(cur_w, LP_MASK_OVERFLOW);
                    }
                }
                x if x == LTAG_MAX => {
                    if let Some((BinLNode { u, v }, _)) = pers.l.maxs.rows.get(r) {
                        for cw in [u.word, v.word] {
                            if !l_memo.contains_key(&cw) && state.get(&cw).copied() != Some(1) {
                                stack.push((cw, false));
                            }
                        }
                    } else {
                        l_memo.insert(cur_w, LP_MASK_OVERFLOW);
                    }
                }
                x if x == LTAG_IMAX => {
                    if let Some((BinLNode { u, v }, _)) = pers.l.imaxs.rows.get(r) {
                        for cw in [u.word, v.word] {
                            if !l_memo.contains_key(&cw) && state.get(&cw).copied() != Some(1) {
                                stack.push((cw, false));
                            }
                        }
                    } else {
                        l_memo.insert(cur_w, LP_MASK_OVERFLOW);
                    }
                }
                _ => {
                    l_memo.insert(cur_w, LP_MASK_OVERFLOW);
                }
            }
        } else {
            let m = match t {
                x if x == LTAG_SUCC => pers
                    .l
                    .succs
                    .rows
                    .get(r)
                    .map(|(n, _)| l_memo.get(&n.u.word).copied().unwrap_or(LP_MASK_OVERFLOW))
                    .unwrap_or(LP_MASK_OVERFLOW),
                x if x == LTAG_MAX => pers
                    .l
                    .maxs
                    .rows
                    .get(r)
                    .map(|(n, _)| {
                        l_memo.get(&n.u.word).copied().unwrap_or(LP_MASK_OVERFLOW)
                            | l_memo.get(&n.v.word).copied().unwrap_or(LP_MASK_OVERFLOW)
                    })
                    .unwrap_or(LP_MASK_OVERFLOW),
                x if x == LTAG_IMAX => pers
                    .l
                    .imaxs
                    .rows
                    .get(r)
                    .map(|(n, _)| {
                        l_memo.get(&n.u.word).copied().unwrap_or(LP_MASK_OVERFLOW)
                            | l_memo.get(&n.v.word).copied().unwrap_or(LP_MASK_OVERFLOW)
                    })
                    .unwrap_or(LP_MASK_OVERFLOW),
                _ => LP_MASK_OVERFLOW,
            };
            l_memo.insert(cur_w, m);
        }
    }
    l_memo.get(&root_word).copied().unwrap_or(LP_MASK_OVERFLOW)
}

fn levels_mask_sparse(
    pers: &PersTier,
    l_param_mask: &[u64],
    l_memo: &mut HashMap<u32, u64>,
    ls_memo: &mut HashMap<u32, u64>,
    ls_word: u32,
) -> u64 {
    if let Some(&m) = ls_memo.get(&ls_word) {
        return m;
    }
    let lsi = LsIdx::of_word(ls_word);
    let m = if !lsi.is_persistent() || lsi.tag() != LSTAG_LIST {
        LP_MASK_OVERFLOW
    } else if let Some((ListNode { us }, _)) = pers.ls.lists.rows.get(lsi.idx_nat()) {
        let mut acc = 0u64;
        for u in us {
            acc |= level_mask_sparse(pers, l_param_mask, l_memo, u.word);
        }
        acc
    } else {
        LP_MASK_OVERFLOW
    };
    ls_memo.insert(ls_word, m);
    m
}

fn collect_decl_seed_exprs(decls: &[IDeclaration]) -> Vec<u32> {
    let mut seeds = Vec::with_capacity(decls.len() * 2);
    for decl in decls {
        match decl {
            IDeclaration::DefnDecl(cv, v, _)
            | IDeclaration::ThmDecl(cv, v)
            | IDeclaration::OpaqueDecl(cv, v) => {
                seeds.push(cv.ty.word);
                seeds.push(v.word);
            }
            IDeclaration::AxiomDecl(cv) | IDeclaration::QuotDecl(_, cv) => {
                seeds.push(cv.ty.word);
            }
            IDeclaration::IndDecl(_, _) => {}
        }
    }
    seeds
}

impl DagSummaries {
    fn build_reachable(
        pers: &PersTier,
        first_const_slot: &HashMap<u32, u32>,
        slot_to_rec: &[u32],
        seeds: &[u32],
    ) -> Self {
        let (lp_name_to_bit, l_param_mask) = build_lp_name_to_bit(pers);
        let mut l_memo: HashMap<u32, u64> = HashMap::new();
        let mut ls_memo: HashMap<u32, u64> = HashMap::new();
        let mut map: HashMap<u32, ExprSummary> = HashMap::with_capacity(seeds.len() * 4);
        let mut state: HashMap<u32, u8> = HashMap::with_capacity(seeds.len() * 4);
        let mut stack: Vec<(u32, bool)> = Vec::with_capacity(256);

        let push_needed = |stack: &mut Vec<(u32, bool)>, state: &HashMap<u32, u8>, w: u32| {
            let ei = EIdx::of_word(w);
            if ei.is_persistent() && state.get(&w).copied().unwrap_or(0) != 2 {
                stack.push((w, false));
            }
        };

        for &sw in seeds {
            push_needed(&mut stack, &state, sw);
            while let Some((cur_w, expanded)) = stack.pop() {
                if state.get(&cur_w).copied() == Some(2) {
                    continue;
                }
                let ei = EIdx::of_word(cur_w);
                if !ei.is_persistent() {
                    continue;
                }
                let t = ei.tag();
                let r = ei.idx_nat();

                if t == ETAG_BVAR {
                    let s = pers
                        .e
                        .bvars
                        .rows
                        .get(r)
                        .map(|(BVarNode { i }, _)| eval_bvar_summary(*i))
                        .unwrap_or(ExprSummary::INVALID);
                    map.insert(cur_w, s);
                    state.insert(cur_w, 2);
                    continue;
                }
                if t == ETAG_SORT {
                    let s = pers
                        .e
                        .sorts
                        .rows
                        .get(r)
                        .map(|(SortNode { u }, _)| ExprSummary {
                            lp_mask: level_mask_sparse(pers, &l_param_mask, &mut l_memo, u.word),
                            bvar_b: 0,
                            max_const_slotp1: 0,
                            max_const_recp1: 0,
                            fvar_b: 0,
                            size_sat: 1,
                        })
                        .unwrap_or(ExprSummary::INVALID);
                    map.insert(cur_w, s);
                    state.insert(cur_w, 2);
                    continue;
                }
                if t == ETAG_CONST {
                    let s = pers
                        .e
                        .consts
                        .rows
                        .get(r)
                        .map(|(ConstNode { n, us }, _)| {
                            let m = levels_mask_sparse(
                                pers,
                                &l_param_mask,
                                &mut l_memo,
                                &mut ls_memo,
                                us.word,
                            );
                            eval_const_summary(first_const_slot, slot_to_rec, n.word, m)
                        })
                        .unwrap_or(ExprSummary::INVALID);
                    map.insert(cur_w, s);
                    state.insert(cur_w, 2);
                    continue;
                }
                if t == ETAG_LIT {
                    let s = if r < pers.e.lits.rows.len() {
                        ExprSummary::LIT
                    } else {
                        ExprSummary::INVALID
                    };
                    map.insert(cur_w, s);
                    state.insert(cur_w, 2);
                    continue;
                }

                if !expanded {
                    if state.get(&cur_w).copied() == Some(1) {
                        map.insert(cur_w, ExprSummary::INVALID);
                        state.insert(cur_w, 2);
                        continue;
                    }
                    state.insert(cur_w, 1);
                    stack.push((cur_w, true));
                    match t {
                        x if x == ETAG_FVAR => {
                            if let Some((n, _)) = pers.e.fvars.rows.get(r) {
                                push_needed(&mut stack, &state, n.ty.word);
                            }
                        }
                        x if x == ETAG_APP => {
                            if let Some((n, _)) = pers.e.apps.rows.get(r) {
                                push_needed(&mut stack, &state, n.a.word);
                                push_needed(&mut stack, &state, n.f.word);
                            }
                        }
                        x if x == ETAG_LAM => {
                            if let Some((n, _)) = pers.e.lams.rows.get(r) {
                                push_needed(&mut stack, &state, n.body.word);
                                push_needed(&mut stack, &state, n.ty.word);
                            }
                        }
                        x if x == ETAG_FORALL_E => {
                            if let Some((n, _)) = pers.e.foralls.rows.get(r) {
                                push_needed(&mut stack, &state, n.body.word);
                                push_needed(&mut stack, &state, n.ty.word);
                            }
                        }
                        x if x == ETAG_LET_E => {
                            if let Some((n, _)) = pers.e.lets.rows.get(r) {
                                push_needed(&mut stack, &state, n.body.word);
                                push_needed(&mut stack, &state, n.val.word);
                                push_needed(&mut stack, &state, n.ty.word);
                            }
                        }
                        _ => {
                            if let Some((n, _)) = pers.e.projs.rows.get(r) {
                                push_needed(&mut stack, &state, n.e.word);
                            }
                        }
                    }
                } else {
                    let read_child = |cw: u32| -> ExprSummary {
                        let cei = EIdx::of_word(cw);
                        if !cei.is_persistent() {
                            return ExprSummary::INVALID;
                        }
                        map.get(&cw).copied().unwrap_or(ExprSummary::INVALID)
                    };
                    let s = match t {
                        x if x == ETAG_FVAR => pers
                            .e
                            .fvars
                            .rows
                            .get(r)
                            .map(|(n, _)| {
                                let mut s = read_child(n.ty.word);
                                s.fvar_b = 1;
                                s.size_sat = (s.size_sat + 1).min(4096);
                                s
                            })
                            .unwrap_or(ExprSummary::INVALID),
                        x if x == ETAG_APP => pers
                            .e
                            .apps
                            .rows
                            .get(r)
                            .map(|(n, _)| {
                                let mut s = read_child(n.f.word).combine(read_child(n.a.word));
                                s.size_sat = s.size_sat.saturating_add(1).min(4096);
                                s
                            })
                            .unwrap_or(ExprSummary::INVALID),
                        x if x == ETAG_LAM => pers
                            .e
                            .lams
                            .rows
                            .get(r)
                            .map(|(n, _)| {
                                let mut s = read_child(n.ty.word)
                                    .combine(read_child(n.body.word).shift_binder());
                                s.size_sat = s.size_sat.saturating_add(1).min(4096);
                                s
                            })
                            .unwrap_or(ExprSummary::INVALID),
                        x if x == ETAG_FORALL_E => pers
                            .e
                            .foralls
                            .rows
                            .get(r)
                            .map(|(n, _)| {
                                let mut s = read_child(n.ty.word)
                                    .combine(read_child(n.body.word).shift_binder());
                                s.size_sat = s.size_sat.saturating_add(1).min(4096);
                                s
                            })
                            .unwrap_or(ExprSummary::INVALID),
                        x if x == ETAG_LET_E => pers
                            .e
                            .lets
                            .rows
                            .get(r)
                            .map(|(n, _)| {
                                let mut s = read_child(n.ty.word)
                                    .combine(read_child(n.val.word))
                                    .combine(read_child(n.body.word).shift_binder());
                                s.size_sat = s.size_sat.saturating_add(1).min(4096);
                                s
                            })
                            .unwrap_or(ExprSummary::INVALID),
                        _ => pers
                            .e
                            .projs
                            .rows
                            .get(r)
                            .map(|(n, _)| {
                                let mut c = read_child(n.e.word);
                                c.size_sat = (c.size_sat + 1).min(4096);
                                c
                            })
                            .unwrap_or(ExprSummary::INVALID),
                    };
                    map.insert(cur_w, s);
                    state.insert(cur_w, 2);
                }
            }
        }

        Self {
            lp_name_to_bit,
            e_fvar: Vec::new(),
            e_app: Vec::new(),
            e_lam: Vec::new(),
            e_forall: Vec::new(),
            e_let: Vec::new(),
            e_proj: Vec::new(),
            e_bvar: Vec::new(),
            e_sort: Vec::new(),
            e_const: Vec::new(),
            n_lit: pers.e.lits.rows.len(),
            sparse: Some(map),
        }
    }

    fn build(pers: &PersTier, first_const_slot: &HashMap<u32, u32>, slot_to_rec: &[u32]) -> Self {
        let (lp_name_to_bit, l_param_mask) = build_lp_name_to_bit(pers);

        let n_zero = pers.l.zeros.rows.len();
        let n_succ = pers.l.succs.rows.len();
        let n_max = pers.l.maxs.rows.len();
        let n_imax = pers.l.imaxs.rows.len();
        let mut l_succ_mask = vec![0u64; n_succ];
        let mut l_max_mask = vec![0u64; n_max];
        let mut l_imax_mask = vec![0u64; n_imax];
        let mut l_succ_st = vec![0u8; n_succ];
        let mut l_max_st = vec![0u8; n_max];
        let mut l_imax_st = vec![0u8; n_imax];

        let mut l_stack: Vec<(u32, bool)> = Vec::new();
        let push_l = |stack: &mut Vec<(u32, bool)>,
                          l_word: u32,
                          st_succ: &[u8],
                          st_max: &[u8],
                          st_imax: &[u8]| {
            let li = LIdx::of_word(l_word);
            if !li.is_persistent() {
                return;
            }
            let row = li.idx_nat();
            match li.tag() {
                t if t == LTAG_SUCC && row < n_succ && st_succ[row] != 2 => {
                    stack.push((l_word, false));
                }
                t if t == LTAG_MAX && row < n_max && st_max[row] != 2 => {
                    stack.push((l_word, false));
                }
                t if t == LTAG_IMAX && row < n_imax && st_imax[row] != 2 => {
                    stack.push((l_word, false));
                }
                _ => {}
            }
        };

        for (tag, len) in [(LTAG_SUCC, n_succ), (LTAG_MAX, n_max), (LTAG_IMAX, n_imax)] {
            for start_row in 0..len {
                let done = match tag {
                    t if t == LTAG_SUCC => l_succ_st[start_row] == 2,
                    t if t == LTAG_MAX => l_max_st[start_row] == 2,
                    _ => l_imax_st[start_row] == 2,
                };
                if done {
                    continue;
                }
                l_stack.push((LIdx::pack(tag, TIER_P, start_row as u32).word, false));
                while let Some((cur_w, expanded)) = l_stack.pop() {
                    let li = LIdx::of_word(cur_w);
                    if !li.is_persistent() {
                        continue;
                    }
                    let row = li.idx_nat();
                    let t = li.tag();
                    if !expanded {
                        let st = match t {
                            x if x == LTAG_SUCC && row < n_succ => l_succ_st[row],
                            x if x == LTAG_MAX && row < n_max => l_max_st[row],
                            x if x == LTAG_IMAX && row < n_imax => l_imax_st[row],
                            _ => 2,
                        };
                        if st == 2 {
                            continue;
                        }
                        if st == 1 {
                            match t {
                                x if x == LTAG_SUCC => {
                                    l_succ_mask[row] = LP_MASK_OVERFLOW;
                                    l_succ_st[row] = 2;
                                }
                                x if x == LTAG_MAX => {
                                    l_max_mask[row] = LP_MASK_OVERFLOW;
                                    l_max_st[row] = 2;
                                }
                                _ => {
                                    l_imax_mask[row] = LP_MASK_OVERFLOW;
                                    l_imax_st[row] = 2;
                                }
                            }
                            continue;
                        }
                        match t {
                            x if x == LTAG_SUCC => {
                                l_succ_st[row] = 1;
                                l_stack.push((cur_w, true));
                                push_l(
                                    &mut l_stack,
                                    pers.l.succs.rows[row].0.u.word,
                                    &l_succ_st,
                                    &l_max_st,
                                    &l_imax_st,
                                );
                            }
                            x if x == LTAG_MAX => {
                                l_max_st[row] = 1;
                                l_stack.push((cur_w, true));
                                let n = &pers.l.maxs.rows[row].0;
                                push_l(&mut l_stack, n.v.word, &l_succ_st, &l_max_st, &l_imax_st);
                                push_l(&mut l_stack, n.u.word, &l_succ_st, &l_max_st, &l_imax_st);
                            }
                            _ => {
                                l_imax_st[row] = 1;
                                l_stack.push((cur_w, true));
                                let n = &pers.l.imaxs.rows[row].0;
                                push_l(&mut l_stack, n.v.word, &l_succ_st, &l_max_st, &l_imax_st);
                                push_l(&mut l_stack, n.u.word, &l_succ_st, &l_max_st, &l_imax_st);
                            }
                        }
                    } else {
                        let read_l = |w: u32,
                                      sm: &[u64],
                                      ss: &[u8],
                                      mm: &[u64],
                                      ms: &[u8],
                                      im: &[u64],
                                      is: &[u8]|
                         -> u64 {
                            let c = LIdx::of_word(w);
                            if !c.is_persistent() {
                                return LP_MASK_OVERFLOW;
                            }
                            let r = c.idx_nat();
                            match c.tag() {
                                x if x == LTAG_ZERO && r < n_zero => 0u64,
                                x if x == LTAG_PARAM && r < l_param_mask.len() => l_param_mask[r],
                                x if x == LTAG_SUCC && r < n_succ && ss[r] == 2 => sm[r],
                                x if x == LTAG_MAX && r < n_max && ms[r] == 2 => mm[r],
                                x if x == LTAG_IMAX && r < n_imax && is[r] == 2 => im[r],
                                _ => LP_MASK_OVERFLOW,
                            }
                        };
                        match t {
                            x if x == LTAG_SUCC => {
                                if l_succ_st[row] != 2 {
                                    l_succ_mask[row] = read_l(
                                        pers.l.succs.rows[row].0.u.word,
                                        &l_succ_mask,
                                        &l_succ_st,
                                        &l_max_mask,
                                        &l_max_st,
                                        &l_imax_mask,
                                        &l_imax_st,
                                    );
                                    l_succ_st[row] = 2;
                                }
                            }
                            x if x == LTAG_MAX => {
                                if l_max_st[row] != 2 {
                                    let n = &pers.l.maxs.rows[row].0;
                                    let mu = read_l(
                                        n.u.word,
                                        &l_succ_mask,
                                        &l_succ_st,
                                        &l_max_mask,
                                        &l_max_st,
                                        &l_imax_mask,
                                        &l_imax_st,
                                    );
                                    let mv = read_l(
                                        n.v.word,
                                        &l_succ_mask,
                                        &l_succ_st,
                                        &l_max_mask,
                                        &l_max_st,
                                        &l_imax_mask,
                                        &l_imax_st,
                                    );
                                    l_max_mask[row] = mu | mv;
                                    l_max_st[row] = 2;
                                }
                            }
                            _ => {
                                if l_imax_st[row] != 2 {
                                    let n = &pers.l.imaxs.rows[row].0;
                                    let mu = read_l(
                                        n.u.word,
                                        &l_succ_mask,
                                        &l_succ_st,
                                        &l_max_mask,
                                        &l_max_st,
                                        &l_imax_mask,
                                        &l_imax_st,
                                    );
                                    let mv = read_l(
                                        n.v.word,
                                        &l_succ_mask,
                                        &l_succ_st,
                                        &l_max_mask,
                                        &l_max_st,
                                        &l_imax_mask,
                                        &l_imax_st,
                                    );
                                    l_imax_mask[row] = mu | mv;
                                    l_imax_st[row] = 2;
                                }
                            }
                        }
                    }
                }
            }
        }

        let level_mask = |l_word: u32| -> u64 {
            let li = LIdx::of_word(l_word);
            if !li.is_persistent() {
                return LP_MASK_OVERFLOW;
            }
            let r = li.idx_nat();
            match li.tag() {
                t if t == LTAG_ZERO && r < n_zero => 0u64,
                t if t == LTAG_PARAM && r < l_param_mask.len() => l_param_mask[r],
                t if t == LTAG_SUCC && r < l_succ_mask.len() => l_succ_mask[r],
                t if t == LTAG_MAX && r < l_max_mask.len() => l_max_mask[r],
                t if t == LTAG_IMAX && r < l_imax_mask.len() => l_imax_mask[r],
                _ => LP_MASK_OVERFLOW,
            }
        };

        let mut ls_mask = Vec::with_capacity(pers.ls.lists.rows.len());
        for (ListNode { us }, _) in &pers.ls.lists.rows {
            let mut m = 0u64;
            for u in us {
                m |= level_mask(u.word);
            }
            ls_mask.push(m);
        }
        let levels_mask = |ls_word: u32| -> u64 {
            let lsi = LsIdx::of_word(ls_word);
            if !lsi.is_persistent() || lsi.tag() != LSTAG_LIST {
                return LP_MASK_OVERFLOW;
            }
            ls_mask.get(lsi.idx_nat()).copied().unwrap_or(LP_MASK_OVERFLOW)
        };

        // Leaf expression summaries
        let mut e_bvar = Vec::with_capacity(pers.e.bvars.rows.len());
        for (BVarNode { i }, _) in &pers.e.bvars.rows {
            if *i == u64::MAX {
                e_bvar.push(ExprSummary::INVALID);
            } else {
                e_bvar.push(ExprSummary {
                    lp_mask: 0,
                    bvar_b: i.saturating_add(1),
                    max_const_slotp1: 0,
                    max_const_recp1: 0,
                    fvar_b: 0,
                    size_sat: 1,
                });
            }
        }
        let mut e_sort = Vec::with_capacity(pers.e.sorts.rows.len());
        for (SortNode { u }, _) in &pers.e.sorts.rows {
            e_sort.push(ExprSummary {
                lp_mask: level_mask(u.word),
                bvar_b: 0,
                max_const_slotp1: 0,
                max_const_recp1: 0,
                fvar_b: 0,
                size_sat: 1,
            });
        }
        let mut e_const = Vec::with_capacity(pers.e.consts.rows.len());
        for (ConstNode { n, us }, _) in &pers.e.consts.rows {
            let (slotp1, recp1) = match first_const_slot.get(&n.word) {
                None => (u32::MAX, u32::MAX),
                Some(&slot) => {
                    let rec = slot_to_rec.get(slot as usize).copied().unwrap_or(u32::MAX - 1);
                    (slot.saturating_add(1), rec.saturating_add(1))
                }
            };
            e_const.push(ExprSummary {
                lp_mask: levels_mask(us.word),
                bvar_b: 0,
                max_const_slotp1: slotp1,
                max_const_recp1: recp1,
                fvar_b: 0,
                size_sat: 1,
            });
        }
        let n_lit = pers.e.lits.rows.len();

        let n_fvar = pers.e.fvars.rows.len();
        let n_app = pers.e.apps.rows.len();
        let n_lam = pers.e.lams.rows.len();
        let n_forall = pers.e.foralls.rows.len();
        let n_let = pers.e.lets.rows.len();
        let n_proj = pers.e.projs.rows.len();

        let mut e_fvar = vec![ExprSummary::default(); n_fvar];
        let mut e_app = vec![ExprSummary::default(); n_app];
        let mut e_lam = vec![ExprSummary::default(); n_lam];
        let mut e_forall = vec![ExprSummary::default(); n_forall];
        let mut e_let = vec![ExprSummary::default(); n_let];
        let mut e_proj = vec![ExprSummary::default(); n_proj];

        let mut st_fvar = vec![0u8; n_fvar];
        let mut st_app = vec![0u8; n_app];
        let mut st_lam = vec![0u8; n_lam];
        let mut st_forall = vec![0u8; n_forall];
        let mut st_let = vec![0u8; n_let];
        let mut st_proj = vec![0u8; n_proj];

        let mut e_stack: Vec<(u32, bool)> = Vec::new();
        let push_e_if_needed = |stack: &mut Vec<(u32, bool)>,
                                w: u32,
                                sf: &[u8],
                                sa: &[u8],
                                sl: &[u8],
                                sfo: &[u8],
                                sle: &[u8],
                                sp: &[u8]| {
            let ei = EIdx::of_word(w);
            if !ei.is_persistent() {
                return;
            }
            let r = ei.idx_nat();
            match ei.tag() {
                t if t == ETAG_FVAR && r < n_fvar && sf[r] != 2 => stack.push((w, false)),
                t if t == ETAG_APP && r < n_app && sa[r] != 2 => stack.push((w, false)),
                t if t == ETAG_LAM && r < n_lam && sl[r] != 2 => stack.push((w, false)),
                t if t == ETAG_FORALL_E && r < n_forall && sfo[r] != 2 => stack.push((w, false)),
                t if t == ETAG_LET_E && r < n_let && sle[r] != 2 => stack.push((w, false)),
                t if t == ETAG_PROJ && r < n_proj && sp[r] != 2 => stack.push((w, false)),
                _ => {}
            }
        };

        for (tag, len) in [
            (ETAG_FVAR, n_fvar),
            (ETAG_APP, n_app),
            (ETAG_LAM, n_lam),
            (ETAG_FORALL_E, n_forall),
            (ETAG_LET_E, n_let),
            (ETAG_PROJ, n_proj),
        ] {
            for start_row in 0..len {
                let done = match tag {
                    t if t == ETAG_FVAR => st_fvar[start_row] == 2,
                    t if t == ETAG_APP => st_app[start_row] == 2,
                    t if t == ETAG_LAM => st_lam[start_row] == 2,
                    t if t == ETAG_FORALL_E => st_forall[start_row] == 2,
                    t if t == ETAG_LET_E => st_let[start_row] == 2,
                    _ => st_proj[start_row] == 2,
                };
                if done {
                    continue;
                }
                let start_word = if tag == ETAG_APP {
                    EIdx::pack_wide(TIER_P, start_row as u32).word
                } else {
                    EIdx::pack(tag, TIER_P, start_row as u32).word
                };
                e_stack.push((start_word, false));
                while let Some((cur_w, expanded)) = e_stack.pop() {
                    let ei = EIdx::of_word(cur_w);
                    if !ei.is_persistent() {
                        continue;
                    }
                    let t = ei.tag();
                    let r = ei.idx_nat();
                    if !expanded {
                        let st = match t {
                            x if x == ETAG_FVAR && r < n_fvar => st_fvar[r],
                            x if x == ETAG_APP && r < n_app => st_app[r],
                            x if x == ETAG_LAM && r < n_lam => st_lam[r],
                            x if x == ETAG_FORALL_E && r < n_forall => st_forall[r],
                            x if x == ETAG_LET_E && r < n_let => st_let[r],
                            x if x == ETAG_PROJ && r < n_proj => st_proj[r],
                            _ => 2,
                        };
                        if st == 2 {
                            continue;
                        }
                        if st == 1 {
                            match t {
                                x if x == ETAG_FVAR => {
                                    e_fvar[r] = ExprSummary::INVALID;
                                    st_fvar[r] = 2;
                                }
                                x if x == ETAG_APP => {
                                    e_app[r] = ExprSummary::INVALID;
                                    st_app[r] = 2;
                                }
                                x if x == ETAG_LAM => {
                                    e_lam[r] = ExprSummary::INVALID;
                                    st_lam[r] = 2;
                                }
                                x if x == ETAG_FORALL_E => {
                                    e_forall[r] = ExprSummary::INVALID;
                                    st_forall[r] = 2;
                                }
                                x if x == ETAG_LET_E => {
                                    e_let[r] = ExprSummary::INVALID;
                                    st_let[r] = 2;
                                }
                                _ => {
                                    e_proj[r] = ExprSummary::INVALID;
                                    st_proj[r] = 2;
                                }
                            }
                            continue;
                        }
                        match t {
                            x if x == ETAG_FVAR => {
                                st_fvar[r] = 1;
                                e_stack.push((cur_w, true));
                                push_e_if_needed(
                                    &mut e_stack,
                                    pers.e.fvars.rows[r].0.ty.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                            }
                            x if x == ETAG_APP => {
                                st_app[r] = 1;
                                e_stack.push((cur_w, true));
                                let n = &pers.e.apps.rows[r].0;
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.a.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.f.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                            }
                            x if x == ETAG_LAM => {
                                st_lam[r] = 1;
                                e_stack.push((cur_w, true));
                                let n = &pers.e.lams.rows[r].0;
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.body.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.ty.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                            }
                            x if x == ETAG_FORALL_E => {
                                st_forall[r] = 1;
                                e_stack.push((cur_w, true));
                                let n = &pers.e.foralls.rows[r].0;
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.body.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.ty.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                            }
                            x if x == ETAG_LET_E => {
                                st_let[r] = 1;
                                e_stack.push((cur_w, true));
                                let n = &pers.e.lets.rows[r].0;
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.body.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.val.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                                push_e_if_needed(
                                    &mut e_stack,
                                    n.ty.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                            }
                            _ => {
                                st_proj[r] = 1;
                                e_stack.push((cur_w, true));
                                push_e_if_needed(
                                    &mut e_stack,
                                    pers.e.projs.rows[r].0.e.word,
                                    &st_fvar,
                                    &st_app,
                                    &st_lam,
                                    &st_forall,
                                    &st_let,
                                    &st_proj,
                                );
                            }
                        }
                    } else {
                        let read_e = |w: u32,
                                      ef: &[ExprSummary],
                                      sf: &[u8],
                                      ea: &[ExprSummary],
                                      sa: &[u8],
                                      el: &[ExprSummary],
                                      sl: &[u8],
                                      efo: &[ExprSummary],
                                      sfo: &[u8],
                                      ele: &[ExprSummary],
                                      sle: &[u8],
                                      ep: &[ExprSummary],
                                      sp: &[u8]|
                         -> ExprSummary {
                            let c = EIdx::of_word(w);
                            if !c.is_persistent() {
                                return ExprSummary::INVALID;
                            }
                            let cr = c.idx_nat();
                            match c.tag() {
                                x if x == ETAG_BVAR => {
                                    e_bvar.get(cr).copied().unwrap_or(ExprSummary::INVALID)
                                }
                                x if x == ETAG_SORT => {
                                    e_sort.get(cr).copied().unwrap_or(ExprSummary::INVALID)
                                }
                                x if x == ETAG_CONST => {
                                    e_const.get(cr).copied().unwrap_or(ExprSummary::INVALID)
                                }
                                x if x == ETAG_LIT && cr < n_lit => ExprSummary::LIT,
                                x if x == ETAG_FVAR && cr < n_fvar && sf[cr] == 2 => ef[cr],
                                x if x == ETAG_APP && cr < n_app && sa[cr] == 2 => ea[cr],
                                x if x == ETAG_LAM && cr < n_lam && sl[cr] == 2 => el[cr],
                                x if x == ETAG_FORALL_E && cr < n_forall && sfo[cr] == 2 => efo[cr],
                                x if x == ETAG_LET_E && cr < n_let && sle[cr] == 2 => ele[cr],
                                x if x == ETAG_PROJ && cr < n_proj && sp[cr] == 2 => ep[cr],
                                _ => ExprSummary::INVALID,
                            }
                        };
                        match t {
                            x if x == ETAG_FVAR => {
                                if st_fvar[r] != 2 {
                                    let mut s = read_e(
                                        pers.e.fvars.rows[r].0.ty.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    );
                                    s.fvar_b = 1;
                                    s.size_sat = (s.size_sat + 1).min(4096);
                                    e_fvar[r] = s;
                                    st_fvar[r] = 2;
                                }
                            }
                            x if x == ETAG_APP => {
                                if st_app[r] != 2 {
                                    let n = &pers.e.apps.rows[r].0;
                                    let sf = read_e(
                                        n.f.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    );
                                    let sa = read_e(
                                        n.a.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    );
                                    let mut c = sf.combine(sa);
                                    c.size_sat = (c.size_sat + 1).min(4096);
                                    e_app[r] = c;
                                    st_app[r] = 2;
                                }
                            }
                            x if x == ETAG_LAM => {
                                if st_lam[r] != 2 {
                                    let n = &pers.e.lams.rows[r].0;
                                    let st = read_e(
                                        n.ty.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    );
                                    let sb = read_e(
                                        n.body.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    )
                                    .shift_binder();
                                    let mut c = st.combine(sb);
                                    c.size_sat = (c.size_sat + 1).min(4096);
                                    e_lam[r] = c;
                                    st_lam[r] = 2;
                                }
                            }
                            x if x == ETAG_FORALL_E => {
                                if st_forall[r] != 2 {
                                    let n = &pers.e.foralls.rows[r].0;
                                    let st = read_e(
                                        n.ty.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    );
                                    let sb = read_e(
                                        n.body.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    )
                                    .shift_binder();
                                    let mut c = st.combine(sb);
                                    c.size_sat = (c.size_sat + 1).min(4096);
                                    e_forall[r] = c;
                                    st_forall[r] = 2;
                                }
                            }
                            x if x == ETAG_LET_E => {
                                if st_let[r] != 2 {
                                    let n = &pers.e.lets.rows[r].0;
                                    let st = read_e(
                                        n.ty.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    );
                                    let sv = read_e(
                                        n.val.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    );
                                    let sb = read_e(
                                        n.body.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    )
                                    .shift_binder();
                                    let mut c = st.combine(sv).combine(sb);
                                    c.size_sat = (c.size_sat + 1).min(4096);
                                    e_let[r] = c;
                                    st_let[r] = 2;
                                }
                            }
                            _ => {
                                if st_proj[r] != 2 {
                                    let mut c = read_e(
                                        pers.e.projs.rows[r].0.e.word,
                                        &e_fvar,
                                        &st_fvar,
                                        &e_app,
                                        &st_app,
                                        &e_lam,
                                        &st_lam,
                                        &e_forall,
                                        &st_forall,
                                        &e_let,
                                        &st_let,
                                        &e_proj,
                                        &st_proj,
                                    );
                                    c.size_sat = (c.size_sat + 1).min(4096);
                                    e_proj[r] = c;
                                    st_proj[r] = 2;
                                }
                            }
                        }
                    }
                }
            }
        }

        Self {
            lp_name_to_bit,
            e_fvar,
            e_app,
            e_lam,
            e_forall,
            e_let,
            e_proj,
            e_bvar,
            e_sort,
            e_const,
            n_lit,
            sparse: None,
        }
    }

    #[inline]
    fn expr_summary(&self, e_word: u32) -> Option<ExprSummary> {
        let ei = EIdx::of_word(e_word);
        if !ei.is_persistent() {
            return None;
        }
        if let Some(ref map) = self.sparse {
            return map.get(&e_word).copied();
        }
        let r = ei.idx_nat();
        match ei.tag() {
            t if t == ETAG_BVAR => self.e_bvar.get(r).copied(),
            t if t == ETAG_FVAR => self.e_fvar.get(r).copied(),
            t if t == ETAG_SORT => self.e_sort.get(r).copied(),
            t if t == ETAG_CONST => self.e_const.get(r).copied(),
            t if t == ETAG_APP => self.e_app.get(r).copied(),
            t if t == ETAG_LAM => self.e_lam.get(r).copied(),
            t if t == ETAG_FORALL_E => self.e_forall.get(r).copied(),
            t if t == ETAG_LET_E => self.e_let.get(r).copied(),
            t if t == ETAG_LIT => {
                if r < self.n_lit {
                    Some(ExprSummary::LIT)
                } else {
                    None
                }
            }
            t if t == ETAG_PROJ => self.e_proj.get(r).copied(),
            _ => None,
        }
    }

    #[inline]
    fn expr_size_sat(&self, e_word: u32) -> u32 {
        self.expr_summary(e_word).map(|s| s.size_sat).unwrap_or(1)
    }

    fn summary_guard_ok(
        &self,
        e_word: u32,
        dup_decl: bool,
        dup_lp: bool,
        job_lp_mask: u64,
        base_below: u32,
        record_pos: u32,
    ) -> bool {
        if dup_decl || dup_lp {
            return false;
        }
        let Some(s) = self.expr_summary(e_word) else {
            return false;
        };
        s.bvar_b == 0
            && s.fvar_b == 0
            && s.max_const_slotp1 != u32::MAX
            && s.max_const_slotp1 <= base_below
            && s.max_const_recp1 <= record_pos
            && (s.lp_mask & LP_MASK_OVERFLOW) == 0
            && (s.lp_mask & !job_lp_mask) == 0
    }
}

pub fn pack_arena(env: &LoadedEnvironment, cfg: ArenaLimitsConfig) -> GpuArenaPacket {
    pack_arena_from(env, cfg, 0)
}

#[inline]
fn check_u32_bound(label: &str, val: usize) -> Result<u32, String> {
    u32::try_from(val).map_err(|_| format!("SoA pack `{label}` length ({val}) exceeds u32::MAX"))
}

/// Checks 26-bit narrow handle, 30-bit wide `app` handle, and 32-bit GPU SoA offset bounds before
/// packing, returning `Err` instead of panicking or silently wrapping on huge closures.
pub fn try_pack_arena_from(
    env: &LoadedEnvironment,
    cfg: ArenaLimitsConfig,
    start_decl: usize,
) -> Result<GpuArenaPacket, String> {
    use con_ron_core::arena::handle::{IDX_CAP, WIDE_CAP};
    let pers = &env.pers;
    let cap_26 = IDX_CAP as usize;
    let cap_30 = WIDE_CAP as usize;
    for (label, len) in [
        ("l.zeros", pers.l.zeros.rows.len()),
        ("l.succs", pers.l.succs.rows.len()),
        ("l.maxs", pers.l.maxs.rows.len()),
        ("l.imaxs", pers.l.imaxs.rows.len()),
        ("l.params", pers.l.params.rows.len()),
        ("ls.lists", pers.ls.lists.rows.len()),
        ("e.bvars", pers.e.bvars.rows.len()),
        ("e.fvars", pers.e.fvars.rows.len()),
        ("e.sorts", pers.e.sorts.rows.len()),
        ("e.consts", pers.e.consts.rows.len()),
        ("e.lams", pers.e.lams.rows.len()),
        ("e.foralls", pers.e.foralls.rows.len()),
        ("e.lets", pers.e.lets.rows.len()),
        ("e.lits", pers.e.lits.rows.len()),
        ("e.projs", pers.e.projs.rows.len()),
        ("env.consts", pers.env.consts.len()),
    ] {
        if len >= cap_26 {
            return Err(format!("arena `{label}` rows ({len}) >= 26-bit IDX_CAP ({cap_26})"));
        }
    }
    if pers.e.apps.rows.len() >= cap_30 {
        return Err(format!(
            "arena `e.apps` rows ({}) >= 30-bit WIDE_CAP ({cap_30})",
            pers.e.apps.rows.len()
        ));
    }

    // Estimate final word counts before allocating large SoA buffers to catch u32 offset overflows cleanly.
    let est_e_words = pers.e.bvars.rows.len() * 4
        + pers.e.fvars.rows.len() * 4
        + pers.e.sorts.rows.len() * 3
        + pers.e.consts.rows.len() * 4
        + pers.e.apps.rows.len() * 4
        + pers.e.lams.rows.len() * 4
        + pers.e.foralls.rows.len() * 4
        + pers.e.lets.rows.len() * 5
        + pers.e.lits.rows.len() * 5
        + pers.e.projs.rows.len() * 5
        + 1;
    check_u32_bound("estimated e_nodes words", est_e_words)?;
    if est_e_words > MAX_E_NODES_WORDS {
        return Err(format!(
            "estimated e_nodes words ({est_e_words}) exceeds {}-page GPU limit ({MAX_E_NODES_WORDS} words / 8 GiB)",
            E_NODES_NUM_PAGES
        ));
    }
    let _ = check_u32_bound("env.decls", env.decls.len())?;

    let pkt = pack_arena_from_unchecked(env, cfg, start_decl);
    if (pkt.header.e_nodes_len as usize) < pkt.e_nodes.len()
        || pkt.e_nodes.len() > MAX_E_NODES_WORDS
        || (pkt.header.meta_nodes_len as usize) < pkt.meta_nodes.len()
        || (pkt.header.env_tables_len as usize) < pkt.env_tables.len()
        || (pkt.header.num_jobs as usize) != pkt.jobs.len()
    {
        return Err("packed SoA buffer exceeded 32-bit word offset or 8 GiB e_nodes page limit".to_string());
    }
    Ok(pkt)
}

/// Packs `env` into GPU SoA buffers while emitting jobs and running `DagSummaries` reachability
/// ONLY for `&env.decls[start_decl..]` (preserving full environment lookup tables so deltas can
/// still reference earlier declarations).
pub fn pack_arena_from(
    env: &LoadedEnvironment,
    cfg: ArenaLimitsConfig,
    start_decl: usize,
) -> GpuArenaPacket {
    try_pack_arena_from(env, cfg, start_decl).expect("SoA arena packing exceeded 32-bit GPU limits")
}

fn pack_arena_from_unchecked(
    env: &LoadedEnvironment,
    cfg: ArenaLimitsConfig,
    start_decl: usize,
) -> GpuArenaPacket {
    let t0 = Instant::now();
    let pers = &env.pers;
    let start_decl = start_decl.min(env.decls.len());

    let mut header = ArenaHeader {
        verified_mode: 1,
        max_steps: cfg.max_steps,
        max_stack_frames: cfg.max_stack_frames,
        max_scratch_words: cfg.max_scratch_words,
        scratch_wg_stride: (cfg.max_stack_frames * 8 + cfg.max_scratch_words) * cfg.workgroup_size,
        wg_size: cfg.workgroup_size,
        ..Default::default()
    };

    // Reserve meta_nodes first so `e_nodes` big literals can reference `off_lit_pool`? Wait:
    // keep `lit_pool` inside `meta_nodes`, pack `meta_nodes` up to `lit_pool` first, then `e_nodes`
    // appends big Nat limbs & strings directly into `meta_nodes` relative to `off_lit_pool`!
    let mut meta_nodes: Vec<u32> = Vec::new();

    // Levels (`LTables`)
    header.n_l_zero = pers.l.zeros.rows.len() as u32;
    header.off_l_zero_der = meta_nodes.len() as u32;
    for (_, d) in &pers.l.zeros.rows {
        meta_nodes.push((d.hash & 0xFFFF_FFFF) as u32);
        meta_nodes.push(if d.has_param { 1 } else { 0 });
    }

    header.n_l_succ = pers.l.succs.rows.len() as u32;
    header.off_l_succ = meta_nodes.len() as u32;
    for (n, _) in &pers.l.succs.rows {
        meta_nodes.push(n.u.word);
    }
    header.off_l_succ_der = meta_nodes.len() as u32;
    for (_, d) in &pers.l.succs.rows {
        meta_nodes.push((d.hash & 0xFFFF_FFFF) as u32);
        meta_nodes.push(if d.has_param { 1 } else { 0 });
    }

    header.n_l_max = pers.l.maxs.rows.len() as u32;
    header.off_l_max = meta_nodes.len() as u32;
    for (n, _) in &pers.l.maxs.rows {
        meta_nodes.push(n.u.word);
        meta_nodes.push(n.v.word);
    }
    header.off_l_max_der = meta_nodes.len() as u32;
    for (_, d) in &pers.l.maxs.rows {
        meta_nodes.push((d.hash & 0xFFFF_FFFF) as u32);
        meta_nodes.push(if d.has_param { 1 } else { 0 });
    }

    header.n_l_imax = pers.l.imaxs.rows.len() as u32;
    header.off_l_imax = meta_nodes.len() as u32;
    for (n, _) in &pers.l.imaxs.rows {
        meta_nodes.push(n.u.word);
        meta_nodes.push(n.v.word);
    }
    header.off_l_imax_der = meta_nodes.len() as u32;
    for (_, d) in &pers.l.imaxs.rows {
        meta_nodes.push((d.hash & 0xFFFF_FFFF) as u32);
        meta_nodes.push(if d.has_param { 1 } else { 0 });
    }

    header.n_l_param = pers.l.params.rows.len() as u32;
    header.off_l_param = meta_nodes.len() as u32;
    for (n, _) in &pers.l.params.rows {
        meta_nodes.push(n.n.word);
    }
    header.off_l_param_der = meta_nodes.len() as u32;
    for (_, d) in &pers.l.params.rows {
        meta_nodes.push((d.hash & 0xFFFF_FFFF) as u32);
        meta_nodes.push(if d.has_param { 1 } else { 0 });
    }

    // Level lists (`LsTables`)
    header.n_ls = pers.ls.lists.rows.len() as u32;
    header.off_ls_meta = meta_nodes.len() as u32;
    let mut ls_items: Vec<u32> = Vec::new();
    for (ListNode { us }, d) in &pers.ls.lists.rows {
        let off = ls_items.len() as u32;
        let len = us.len() as u32;
        for u in us {
            ls_items.push(u.word);
        }
        meta_nodes.push(off);
        meta_nodes.push(len);
        meta_nodes.push(if d.has_param { 1 } else { 0 });
        meta_nodes.push((d.hash & 0xFFFF_FFFF) as u32);
    }
    header.off_ls_items = meta_nodes.len() as u32;
    meta_nodes.extend_from_slice(&ls_items);

    header.off_lit_pool = meta_nodes.len() as u32;

    // Expression SoA tables (`e_nodes`)
    let mut e_nodes: Vec<u32> = Vec::new();

    // BVar: 2 u32s/node [lo, hi]
    header.n_bvar = pers.e.bvars.rows.len() as u32;
    header.off_bvar = e_nodes.len() as u32;
    for (BVarNode { i }, _) in &pers.e.bvars.rows {
        e_nodes.push((*i & 0xFFFF_FFFF) as u32);
        e_nodes.push((*i >> 32) as u32);
    }
    header.off_bvar_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.bvars);

    // FVar: 3 u32s/node [idx_lo, idx_hi, ty]
    header.n_fvar = pers.e.fvars.rows.len() as u32;
    header.off_fvar = e_nodes.len() as u32;
    for (FVarNode { idx, ty }, _) in &pers.e.fvars.rows {
        e_nodes.push((*idx & 0xFFFF_FFFF) as u32);
        e_nodes.push((*idx >> 32) as u32);
        e_nodes.push(ty.word);
    }
    header.off_fvar_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.fvars);

    // Sort: 1 u32/node [u]
    header.n_sort = pers.e.sorts.rows.len() as u32;
    header.off_sort = e_nodes.len() as u32;
    for (SortNode { u }, _) in &pers.e.sorts.rows {
        e_nodes.push(u.word);
    }
    header.off_sort_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.sorts);

    // Const: 2 u32s/node [n, us]
    header.n_const = pers.e.consts.rows.len() as u32;
    header.off_const = e_nodes.len() as u32;
    for (ConstNode { n, us }, _) in &pers.e.consts.rows {
        e_nodes.push(n.word);
        e_nodes.push(us.word);
    }
    header.off_const_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.consts);

    // App: 2 u32s/node [f, a]
    header.n_app = pers.e.apps.rows.len() as u32;
    header.off_app = e_nodes.len() as u32;
    for (AppNode { f, a }, _) in &pers.e.apps.rows {
        e_nodes.push(f.word);
        e_nodes.push(a.word);
    }
    header.off_app_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.apps);

    // Lam: 2 u32s/node [ty, body]
    header.n_lam = pers.e.lams.rows.len() as u32;
    header.off_lam = e_nodes.len() as u32;
    for (BindNode { ty, body }, _) in &pers.e.lams.rows {
        e_nodes.push(ty.word);
        e_nodes.push(body.word);
    }
    header.off_lam_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.lams);

    // ForallE: 2 u32s/node [ty, body]
    header.n_forall = pers.e.foralls.rows.len() as u32;
    header.off_forall = e_nodes.len() as u32;
    for (BindNode { ty, body }, _) in &pers.e.foralls.rows {
        e_nodes.push(ty.word);
        e_nodes.push(body.word);
    }
    header.off_forall_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.foralls);

    // LetE: 3 u32s/node [ty, val, body]
    header.n_let = pers.e.lets.rows.len() as u32;
    header.off_let = e_nodes.len() as u32;
    for (LetNode { ty, val, body }, _) in &pers.e.lets.rows {
        e_nodes.push(ty.word);
        e_nodes.push(val.word);
        e_nodes.push(body.word);
    }
    header.off_let_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.lets);

    // Lit: 3 u32s/node [kind (0=Nat64, 1=BigNat, 2=Str), a, b]
    // Offsets a for BigNat/Str are relative to header.off_lit_pool!
    header.n_lit = pers.e.lits.rows.len() as u32;
    header.off_lit = e_nodes.len() as u32;
    for (LitNode { l }, _) in &pers.e.lits.rows {
        match l {
            Literal::NatVal(nat_p) => {
                if let Some(v64) = nat_to_u64_exact(nat_p) {
                    e_nodes.push(0);
                    e_nodes.push((v64 & 0xFFFF_FFFF) as u32);
                    e_nodes.push((v64 >> 32) as u32);
                } else {
                    let off = (meta_nodes.len() as u32) - header.off_lit_pool;
                    let start = meta_nodes.len();
                    for &limb in &nat_p.limbs {
                        meta_nodes.push((limb & 0xFFFF_FFFF) as u32);
                        meta_nodes.push((limb >> 32) as u32);
                    }
                    // Trim possible high zero u32 limb if upper half of top u64 is 0.
                    while meta_nodes.len() > start && *meta_nodes.last().unwrap() == 0 {
                        meta_nodes.pop();
                    }
                    let u32_limbs = (meta_nodes.len() - start) as u32;
                    e_nodes.push(1);
                    e_nodes.push(off);
                    e_nodes.push(u32_limbs);
                }
            }
            Literal::StrVal(s_p) => {
                let off = (meta_nodes.len() as u32) - header.off_lit_pool;
                let len = s_p.len() as u32;
                meta_nodes.extend_from_slice(s_p);
                e_nodes.push(2);
                e_nodes.push(off);
                e_nodes.push(len);
            }
        }
    }
    header.off_lit_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.lits);

    // Proj: 4 u32s/node [n, idx_lo, idx_hi, e]
    header.n_proj = pers.e.projs.rows.len() as u32;
    header.off_proj = e_nodes.len() as u32;
    for (ProjNode { n, i, e }, _) in &pers.e.projs.rows {
        e_nodes.push(n.word);
        e_nodes.push((*i & 0xFFFF_FFFF) as u32);
        e_nodes.push((*i >> 32) as u32);
        e_nodes.push(e.word);
    }
    header.off_proj_der = e_nodes.len() as u32;
    push_der(&mut e_nodes, &pers.e.projs);

    // Guard against empty e_nodes/meta_nodes (wgpu requires non-zero buffer binding >= 4 bytes).
    if e_nodes.is_empty() {
        e_nodes.push(0);
    }
    if meta_nodes.is_empty() {
        meta_nodes.push(0);
    }
    header.e_nodes_len = e_nodes.len() as u32;
    header.meta_nodes_len = meta_nodes.len() as u32;

    // Special reserved / nat-op / basis names set for quick flagging.
    let mut special_names: HashSet<u32> = HashSet::new();
    for n in &env.pins.reserved {
        special_names.insert(n.word);
    }
    // Check pin names carefully without mutating frozen store:
    let pin_at = |slot: usize| env.pins.names.get(slot).map(|n| n.word).unwrap_or(0);
    let pin_quot = pin_at(PIN_QUOT);
    let (pin_quot_lift, pin_quot_ind) = find_quot_child_names(pers, pin_quot);
    for slot in [
        PIN_AND,
        PIN_AND_INTRO,
        PIN_AND_REC,
        PIN_SORRY_AX,
        PIN_QUOT,
        PIN_QUOT_MK,
        PIN_QUOT_SOUND,
        PIN_REDUCE_NAT,
        PIN_REDUCE_BOOL,
        PIN_NAT_PRED,
        PIN_NAT_ADD,
        PIN_NAT_SUB,
        PIN_NAT_MUL,
        PIN_NAT_POW,
        PIN_NAT_BEQ,
        PIN_NAT_BLE,
        PIN_NAT_DIV,
        PIN_NAT_MOD,
        PIN_NAT_GCD,
        PIN_NAT_LAND,
        PIN_NAT_LOR,
        PIN_NAT_XOR,
        PIN_NAT_SHIFT_LEFT,
        PIN_NAT_SHIFT_RIGHT,
        PIN_EAGER_REDUCE,
    ] {
        special_names.insert(pin_at(slot));
    }
    if pin_quot_lift != 0 {
        special_names.insert(pin_quot_lift);
    }
    if pin_quot_ind != 0 {
        special_names.insert(pin_quot_ind);
    }
    // Include all kernel-pinned literal/trust/basis/nat-op declarations (`Nat`, `String`,
    // `String.ofList`, `Char`, `Char.ofNat`, `List`, `propext`, `Classical.choice`, `Lean.*`)
    // so host exact `lit_shape_ok` and axiom-shape guards always run when those names are declared.
    for n in &env.pins.names {
        special_names.insert(n.word);
    }

    let mut nat_op_set: HashSet<u32> = HashSet::new();
    for slot in [
        PIN_NAT_PRED,
        PIN_NAT_ADD,
        PIN_NAT_SUB,
        PIN_NAT_MUL,
        PIN_NAT_POW,
        PIN_NAT_BEQ,
        PIN_NAT_BLE,
        PIN_NAT_DIV,
        PIN_NAT_MOD,
        PIN_NAT_GCD,
        PIN_NAT_LAND,
        PIN_NAT_LOR,
        PIN_NAT_XOR,
        PIN_NAT_SHIFT_LEFT,
        PIN_NAT_SHIFT_RIGHT,
    ] {
        nat_op_set.insert(pin_at(slot));
    }

    // Build `env_tables`
    let mut env_tables: Vec<u32> = Vec::new();
    let mut env_nidx: Vec<u32> = Vec::new();
    let mut rec_rules: Vec<u32> = Vec::new();
    let mut rec_fire_words: Vec<u32> = Vec::new();
    let mut env_eidx: Vec<u32> = Vec::new();

    // Helper to pack NIdx slice
    let push_nidxs = |pool: &mut Vec<u32>, xs: &[NIdx]| -> (u32, u32) {
        let off = pool.len() as u32;
        for x in xs {
            pool.push(x.word);
        }
        (off, xs.len() as u32)
    };

    header.n_consts = pers.env.consts.len() as u32;
    header.off_consts = env_tables.len() as u32;

    // Map first occurrence of each constant name to its slot (`insert_consts` exact rule: first wins!)
    let mut first_const_slot: HashMap<u32, u32> = HashMap::with_capacity(pers.env.consts.len());

    for (slot_idx, ci) in pers.env.consts.iter().enumerate() {
        let slot_u32 = slot_idx as u32;
        let (kind, cv, val_word, hint_kind, hint_height, flags, extra0, extra1, extra2, extra3) =
            match ci {
                IConstantInfo::AxiomInfo(cv) => (0u32, cv, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32),
                IConstantInfo::DefnInfo(cv, v, hint) => {
                    let (hk, hh) = match hint {
                        ReducibilityHint::Opaque => (0u32, 0u32),
                        ReducibilityHint::Abbrev => (1u32, 0u32),
                        ReducibilityHint::Regular(h) => (2u32, (*h).min(u32::MAX as u64) as u32),
                    };
                    (1u32, cv, v.word, hk, hh, 0u32, 0u32, 0u32, 0u32, 0u32)
                }
                IConstantInfo::ThmInfo(cv) => (2u32, cv, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32, 0u32),
                IConstantInfo::IndInfo(cv, caps) => {
                    let mut fl = 0u32;
                    if caps.eta {
                        fl |= 1;
                    }
                    if caps.never_zero {
                        fl |= 2;
                    }
                    let (ctors_off, ctors_len) = push_nidxs(&mut env_nidx, &caps.ctors);
                    let _ = &caps.all;
                    (
                        3u32,
                        cv,
                        0u32,
                        0u32,
                        0u32,
                        fl,
                        caps.nparams as u32,
                        caps.n_idx as u32,
                        ctors_off,
                        ctors_len,
                    )
                }
                IConstantInfo::CtorInfo(cv, n_p, n_f, ind_name) => {
                    (4u32, cv, 0u32, 0u32, 0u32, 0u32, *n_p as u32, *n_f as u32, ind_name.word, 0u32)
                }
                IConstantInfo::RecInfo(cv, major_idx, n_params_plus, is_k, rules) => {
                    let mut fl = if *is_k { 4u32 } else { 0u32 };
                    if major_idx
                        .checked_add(1)
                        .map_or(false, |k| pers_peel_pis_ok(pers, k, cv.ty.word))
                    {
                        fl |= 16u32;
                    }
                    let rules_off = (rec_rules.len() / 6) as u32;
                    for r in rules {
                        let (fire_kind, f_off, f_len) = match &r.fire {
                            IRecRuleFire::Plain => (0u32, 0u32, 0u32),
                            IRecRuleFire::Levels(lvls) => {
                                fl |= 8;
                                let off = rec_fire_words.len() as u32;
                                for u in lvls {
                                    rec_fire_words.push(u.word);
                                }
                                (1u32, off, lvls.len() as u32)
                            }
                            IRecRuleFire::Nested(lvls, pins_e) => {
                                fl |= 8;
                                let off = rec_fire_words.len() as u32;
                                for u in lvls {
                                    rec_fire_words.push(u.word);
                                }
                                for p in pins_e {
                                    rec_fire_words.push(p.word);
                                }
                                // f_len packs lvls.len() in low 16 and pins.len() in high 16
                                (2u32, off, ((pins_e.len() as u32) << 16) | (lvls.len() as u32))
                            }
                        };
                        rec_rules.push(r.ctor.word);
                        rec_rules.push(r.nfields as u32);
                        rec_rules.push(fire_kind);
                        rec_rules.push(r.rhs.word);
                        rec_rules.push(f_off);
                        rec_rules.push(f_len);
                    }
                    (
                        5u32,
                        cv,
                        0u32,
                        0u32,
                        0u32,
                        fl,
                        *major_idx as u32,
                        *n_params_plus as u32,
                        rules_off,
                        rules.len() as u32,
                    )
                }
            };

        let (lp_off, lp_len) = push_nidxs(&mut env_nidx, &cv.level_params);
        let name_word = cv.name.word;
        first_const_slot.entry(name_word).or_insert(slot_u32);

        let mut sp_flags = 0u32;
        if nat_op_set.contains(&name_word) {
            sp_flags |= 1;
        }
        if name_word == pin_at(PIN_SORRY_AX) {
            sp_flags |= 2;
        }
        if name_word == pin_at(PIN_EAGER_REDUCE) {
            sp_flags |= 4;
        }
        if name_word == pin_at(PIN_REDUCE_NAT) || name_word == pin_at(PIN_REDUCE_BOOL) {
            sp_flags |= 8;
        }
        if special_names.contains(&name_word) {
            sp_flags |= 16;
        }

        // 16 u32s per constant entry:
        env_tables.push(kind);
        env_tables.push(name_word);
        env_tables.push(cv.ty.word);
        env_tables.push(val_word);
        env_tables.push(lp_off);
        env_tables.push(lp_len);
        env_tables.push(hint_kind);
        env_tables.push(hint_height);
        env_tables.push(flags);
        env_tables.push(extra0);
        env_tables.push(extra1);
        env_tables.push(extra2);
        env_tables.push(extra3);
        env_tables.push(slot_u32);
        env_tables.push(sp_flags);
        env_tables.push(0);
    }

    // Build open-addressed hash table for constants (`NIdx -> slot + 1`)
    let cap_consts = ((first_const_slot.len() + 1) * 2).next_power_of_two().max(16);
    header.const_hash_mask = (cap_consts - 1) as u32;
    header.off_const_hash = env_tables.len() as u32;
    let hash_start = env_tables.len();
    env_tables.resize(hash_start + cap_consts * 2, 0u32);
    for i in 0..cap_consts {
        env_tables[hash_start + i * 2] = EMPTY_NIDX_SENTINEL;
    }
    for (&name_word, &slot_u32) in &first_const_slot {
        let mut idx = (mix_hash32(name_word) & header.const_hash_mask) as usize;
        loop {
            let cell = hash_start + idx * 2;
            if env_tables[cell] == EMPTY_NIDX_SENTINEL {
                env_tables[cell] = name_word;
                env_tables[cell + 1] = slot_u32 + 1;
                break;
            }
            idx = (idx + 1) & (header.const_hash_mask as usize);
        }
    }

    // Projection tables (`IProjTable`), with each table's `record_pos` from `pers.env.tbls`
    let mut rec_pos_by_table_idx: Vec<u32> = vec![0; pers.env.tables.len()];
    for (idx_pos, tbl) in pers.env.tables.iter().enumerate() {
        let mut chosen_pos = 0u32;
        if let Some((r, _)) = pers.env.tbls.get(&tbl.struct_name) {
            chosen_pos = (*r).min(u32::MAX as u64) as u32;
        }
        rec_pos_by_table_idx[idx_pos] = chosen_pos;
    }

    header.n_proj_tables = pers.env.tables.len() as u32;
    header.off_proj_tables = env_tables.len() as u32;
    let mut first_proj_slot: HashMap<u32, u32> = HashMap::with_capacity(pers.env.tables.len());
    for (tbl_idx, IProjTable { struct_name, level_params, num_params, ctor, num_fields, bodies }) in
        pers.env.tables.iter().enumerate()
    {
        let (lp_off, lp_len) = push_nidxs(&mut env_nidx, level_params);
        let b_off = env_eidx.len() as u32;
        for b in bodies {
            env_eidx.push(b.word);
        }
        first_proj_slot
            .entry(struct_name.word)
            .or_insert(tbl_idx as u32);
        // 8 u32s per proj table entry: [struct_name, record_pos, num_params, ctor, num_fields, bodies_off, bodies_len, lp_off_or_len]
        env_tables.push(struct_name.word);
        env_tables.push(rec_pos_by_table_idx[tbl_idx]);
        env_tables.push(*num_params as u32);
        env_tables.push(ctor.word);
        env_tables.push(*num_fields as u32);
        env_tables.push(b_off);
        env_tables.push(bodies.len() as u32);
        env_tables.push(((lp_len & 0xFFFF) << 16) | (lp_off & 0xFFFF)); // Actually wait: env_nidx can exceed 65k! Store full u32s if needed!
    }

    // Note: fix proj table width to 10 u32s or store `lp_off` cleanly without 16-bit truncation!
    // Let's rewrite proj table stride cleanly to 10 u32s right below before pushing hash table.
    env_tables.truncate(header.off_proj_tables as usize);
    env_eidx.clear();
    // Reset env_nidx back to before proj tables? Easiest: just push fresh lp slices into env_nidx!
    for (tbl_idx, IProjTable { struct_name, level_params, num_params, ctor, num_fields, bodies }) in
        pers.env.tables.iter().enumerate()
    {
        let (lp_off, lp_len) = push_nidxs(&mut env_nidx, level_params);
        let b_off = env_eidx.len() as u32;
        for b in bodies {
            env_eidx.push(b.word);
        }
        // 10 u32s per proj table:
        env_tables.push(struct_name.word);
        env_tables.push(rec_pos_by_table_idx[tbl_idx]);
        env_tables.push(*num_params as u32);
        env_tables.push(ctor.word);
        env_tables.push(*num_fields as u32);
        env_tables.push(b_off);
        env_tables.push(bodies.len() as u32);
        env_tables.push(lp_off);
        env_tables.push(lp_len);
        env_tables.push(0);
        let _ = tbl_idx;
    }

    // Projection open-addressed hash map (`NIdx -> proj_slot + 1`)
    let cap_proj = ((first_proj_slot.len() + 1) * 2).next_power_of_two().max(16);
    header.proj_hash_mask = (cap_proj - 1) as u32;
    header.off_proj_hash = env_tables.len() as u32;
    let p_hash_start = env_tables.len();
    env_tables.resize(p_hash_start + cap_proj * 2, 0u32);
    for i in 0..cap_proj {
        env_tables[p_hash_start + i * 2] = EMPTY_NIDX_SENTINEL;
    }
    for (&name_word, &slot_u32) in &first_proj_slot {
        let mut idx = (mix_hash32(name_word) & header.proj_hash_mask) as usize;
        loop {
            let cell = p_hash_start + idx * 2;
            if env_tables[cell] == EMPTY_NIDX_SENTINEL {
                env_tables[cell] = name_word;
                env_tables[cell + 1] = slot_u32 + 1;
                break;
            }
            idx = (idx + 1) & (header.proj_hash_mask as usize);
        }
    }

    let slot_to_rec = compute_slot_to_rec(pers.env.consts.len(), &pers.env.firsts);
    let delta_decls = env.decls.len().saturating_sub(start_decl);
    let dag = if start_decl == 0 || delta_decls * 8 >= env.decls.len() {
        DagSummaries::build(pers, &first_const_slot, &slot_to_rec)
    } else {
        let seeds = collect_decl_seed_exprs(&env.decls[start_decl..]);
        DagSummaries::build_reachable(pers, &first_const_slot, &slot_to_rec, &seeds)
    };

    // Build jobs vector (adding each job's `cv.level_params` into `env_nidx` BEFORE finalizing `off_env_nidx`).
    let mut jobs: Vec<GpuJob> = Vec::with_capacity(env.decls.len().saturating_sub(start_decl));
    let mut eligible_jobs_count = 0usize;

    for (orig_idx, decl) in env.decls.iter().enumerate().skip(start_decl) {
        let first_c = if orig_idx < pers.env.firsts.len() {
            pers.env.firsts[orig_idx] as u32
        } else {
            pers.env.next as u32
        };

        let (kind, name_word, ty_word, val_word, lps, can_gpu, is_lazy, is_special) = match decl {
            IDeclaration::AxiomDecl(cv) => {
                let (off, len) = push_nidxs(&mut env_nidx, &cv.level_params);
                // AxiomDecl involves pinned standard/trust axiom & Quot.sound rules -> always delegate accurately.
                (JobKind::Axiom as u32, cv.name.word, cv.ty.word, 0u32, (off, len), false, false, true)
            }
            IDeclaration::QuotDecl(_, cv) => {
                let (off, len) = push_nidxs(&mut env_nidx, &cv.level_params);
                (JobKind::Quot as u32, cv.name.word, cv.ty.word, 0u32, (off, len), false, false, true)
            }
            IDeclaration::IndDecl(block, _) => {
                let name_w = block
                    .first()
                    .map(|c| match c {
                        IConstantInfo::AxiomInfo(cv)
                        | IConstantInfo::DefnInfo(cv, _, _)
                        | IConstantInfo::ThmInfo(cv)
                        | IConstantInfo::IndInfo(cv, _)
                        | IConstantInfo::CtorInfo(cv, _, _, _)
                        | IConstantInfo::RecInfo(cv, _, _, _, _) => cv.name.word,
                    })
                    .unwrap_or(0);
                (JobKind::Ind as u32, name_w, 0u32, 0u32, (0u32, 0u32), false, false, true)
            }
            IDeclaration::DefnDecl(cv, val, _) => {
                let (off, len) = push_nidxs(&mut env_nidx, &cv.level_params);
                let sp = special_names.contains(&cv.name.word);
                (
                    JobKind::Defn as u32,
                    cv.name.word,
                    cv.ty.word,
                    val.word,
                    (off, len),
                    !sp,
                    false,
                    sp,
                )
            }
            IDeclaration::ThmDecl(cv, val) => {
                let (off, len) = push_nidxs(&mut env_nidx, &cv.level_params);
                let lazy = val.tag() == ETAG_BVAR;
                let sp = special_names.contains(&cv.name.word);
                (
                    JobKind::Thm as u32,
                    cv.name.word,
                    cv.ty.word,
                    val.word,
                    (off, len),
                    !lazy && !sp,
                    lazy,
                    sp,
                )
            }
            IDeclaration::OpaqueDecl(cv, val) => {
                let (off, len) = push_nidxs(&mut env_nidx, &cv.level_params);
                let sp = special_names.contains(&cv.name.word);
                (
                    JobKind::Opaque as u32,
                    cv.name.word,
                    cv.ty.word,
                    val.word,
                    (off, len),
                    !sp,
                    false,
                    sp,
                )
            }
        };

        let ast_size = match decl {
            IDeclaration::DefnDecl(cv, v, _)
            | IDeclaration::ThmDecl(cv, v)
            | IDeclaration::OpaqueDecl(cv, v) => {
                (dag.expr_size_sat(cv.ty.word) + dag.expr_size_sat(v.word)).min(4096)
            }
            IDeclaration::AxiomDecl(cv) | IDeclaration::QuotDecl(_, cv) => {
                dag.expr_size_sat(cv.ty.word).min(4096)
            }
            IDeclaration::IndDecl(_, _) => 4096,
        }
        .max(1);
        let ast_bucket = ast_size.max(1).ilog2();
        let mut flags = 0u32;
        if can_gpu {
            flags |= JOB_FLAG_ELIGIBLE;
            eligible_jobs_count += 1;

            let lp_slice = &env_nidx[lps.0 as usize..(lps.0 + lps.1) as usize];
            let dup_lp = has_dup_u32(lp_slice);
            let dup_decl = first_const_slot
                .get(&name_word)
                .copied()
                .map(|s| s < first_c)
                .unwrap_or(false);
            let mut job_lp_mask = 0u64;
            for &lp in lp_slice {
                if let Some(&bit) = dag.lp_name_to_bit.get(&lp) {
                    if bit < 62 {
                        job_lp_mask |= 1u64 << bit;
                    }
                }
            }
            if dag.summary_guard_ok(
                ty_word,
                dup_decl,
                dup_lp,
                job_lp_mask,
                first_c,
                orig_idx as u32,
            ) {
                flags |= JOB_FLAG_TY_GUARD_OK;
            }
            if !is_lazy
                && val_word != 0
                && dag.summary_guard_ok(
                    val_word,
                    dup_decl,
                    dup_lp,
                    job_lp_mask,
                    first_c,
                    orig_idx as u32,
                )
            {
                flags |= JOB_FLAG_VAL_GUARD_OK;
            }
        }
        if is_lazy {
            flags |= JOB_FLAG_LAZY_BVAR;
        }
        if is_special {
            flags |= JOB_FLAG_SPECIAL;
        }

        jobs.push(GpuJob {
            orig_decl_idx: orig_idx as u32,
            decl_kind: kind,
            record_pos: orig_idx as u32,
            base_below: first_c,
            name: name_word,
            ty: ty_word,
            val: val_word,
            lparams_off: lps.0,
            lparams_len: lps.1,
            ast_size,
            ast_bucket,
            flags,
        });
    }

    // Sort declaration jobs by (eligible_for_gpu desc, ast_bucket asc, kind_prio [Thm < Opaque < Defn], ast_size asc)
    // for RDNA3 64-lane wavefront execution coherence!
    jobs.sort_unstable_by_key(|j| {
        let non_eligible = if (j.flags & JOB_FLAG_ELIGIBLE) != 0 { 0u32 } else { 1u32 };
        let kind_prio = match j.decl_kind {
            x if x == JobKind::Thm as u32 => 0u32,
            x if x == JobKind::Opaque as u32 => 1u32,
            x if x == JobKind::Defn as u32 => 2u32,
            x => 3u32 + x,
        };
        (non_eligible, j.ast_bucket, kind_prio, j.ast_size, j.orig_decl_idx)
    });

    header.num_jobs = jobs.len() as u32;
    header.job_offset = 0;

    // Append tail pools to `env_tables`
    header.off_rec_rules = env_tables.len() as u32;
    header.n_rec_rules = (rec_rules.len() / 6) as u32;
    env_tables.extend_from_slice(&rec_rules);

    header.off_rec_fire = env_tables.len() as u32;
    env_tables.extend_from_slice(&rec_fire_words);

    header.off_env_eidx = env_tables.len() as u32;
    env_tables.extend_from_slice(&env_eidx);

    header.off_env_nidx = env_tables.len() as u32;
    env_tables.extend_from_slice(&env_nidx);

    if env_tables.is_empty() {
        env_tables.push(0);
    }
    header.env_tables_len = env_tables.len() as u32;

    // Populate pinned handles in header
    header.pin_nat = pin_at(PIN_NAT);
    header.pin_nat_zero = pin_at(PIN_NAT_ZERO);
    header.pin_nat_succ = pin_at(PIN_NAT_SUCC);
    header.pin_nat_pred = pin_at(PIN_NAT_PRED);
    header.pin_nat_add = pin_at(PIN_NAT_ADD);
    header.pin_nat_sub = pin_at(PIN_NAT_SUB);
    header.pin_nat_mul = pin_at(PIN_NAT_MUL);
    header.pin_nat_pow = pin_at(PIN_NAT_POW);
    header.pin_nat_beq = pin_at(PIN_NAT_BEQ);
    header.pin_nat_ble = pin_at(PIN_NAT_BLE);
    header.pin_nat_div = pin_at(PIN_NAT_DIV);
    header.pin_nat_mod = pin_at(PIN_NAT_MOD);
    header.pin_nat_gcd = pin_at(PIN_NAT_GCD);
    header.pin_nat_land = pin_at(PIN_NAT_LAND);
    header.pin_nat_lor = pin_at(PIN_NAT_LOR);
    header.pin_nat_xor = pin_at(PIN_NAT_XOR);
    header.pin_nat_shl = pin_at(PIN_NAT_SHIFT_LEFT);
    header.pin_nat_shr = pin_at(PIN_NAT_SHIFT_RIGHT);
    header.pin_bool = pin_at(PIN_BOOL);
    header.pin_bool_true = pin_at(PIN_BOOL_TRUE);
    header.pin_bool_false = pin_at(PIN_BOOL_FALSE);
    header.pin_string = pin_at(PIN_STRING);
    header.pin_eq = pin_at(PIN_EQ);
    header.pin_sorry_ax = pin_at(PIN_SORRY_AX);
    header.pin_eager_reduce = pin_at(PIN_EAGER_REDUCE);
    header.pin_reduce_nat = pin_at(PIN_REDUCE_NAT);
    header.pin_reduce_bool = pin_at(PIN_REDUCE_BOOL);
    header.pin_empty_levels = env.pins.empty_levels.word;
    header.pin_zero_level = env.pins.zero_level.word;
    header.pin_sort_one = env.pins.sort_one.word;
    header.pin_quot = pin_quot;
    header.pin_quot_mk = pin_at(PIN_QUOT_MK);
    header.pin_quot_lift = pin_quot_lift;
    header.pin_quot_ind = pin_quot_ind;
    header.batch_epoch = 1;
    header.pad0 = 0;

    let pack_ns = t0.elapsed().as_nanos();
    let _ = (
        TIER_P, TIER_S, NTAG_NUM, NTAG_STR, LTAG_ZERO, LTAG_SUCC, LTAG_MAX, LTAG_IMAX, LTAG_PARAM,
        ETAG_APP, ETAG_BVAR, ETAG_FVAR, ETAG_SORT, ETAG_CONST, ETAG_LAM, ETAG_FORALL_E, ETAG_LET_E,
        ETAG_LIT, ETAG_PROJ,
        std::mem::size_of::<ZeroNode>(), std::mem::size_of::<SuccNode>(),
        std::mem::size_of::<BinLNode>(), std::mem::size_of::<ParamNode>(),
        std::mem::size_of::<NTables>(), std::mem::size_of::<StrNode>(),
        std::mem::size_of::<NumNode>(),
    );

    GpuArenaPacket {
        header,
        e_nodes,
        meta_nodes,
        env_tables,
        jobs,
        eligible_jobs_count,
        pack_ns,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::arena::handle::{EIdx, LIdx, LsIdx, NIdx, LSTAG_LIST, NTAG_ANONYMOUS};

    #[test]
    fn arena_header_size_multiple_of_16_and_zero_float() {
        assert_eq!(std::mem::size_of::<ArenaHeader>() % 16, 0);
        assert_eq!(std::mem::size_of::<GpuJob>(), 48);
        assert_eq!(std::mem::size_of::<GpuVerdict>(), 16);
    }

    #[test]
    fn pers_peel_pis_and_quot_child_names_work() {
        use con_ron_core::arena::checker::freeze_tier;
        use con_ron_core::arena::monad::{
            intern_e_forall_e, intern_e_sort, intern_l_node, intern_name, AState,
        };
        use con_ron_core::arena::store::{LNodeView, PersTier};
        use con_ron_core::arena::stream_index::stream_index_empty;
        use con_ron_core::kernel::name;
        use con_ron_core::ron::hashmap::Dup;

        let pers0 = PersTier::empty();
        let mut st = AState::empty();
        let l0 = intern_l_node(&pers0, &mut st, LNodeView::Zero).ok().expect("l0");
        let s0 = intern_e_sort(&pers0, &mut st, l0).ok().expect("s0");
        let pi1 = intern_e_forall_e(&pers0, &mut st, s0.dup2(), s0.dup2()).ok().expect("pi1");
        let pi2 = intern_e_forall_e(&pers0, &mut st, s0, pi1).ok().expect("pi2");

        let quot_raw = name::mk_str(name::anonymous(), "Quot".chars().map(|c| c as u32).collect());
        let lift_raw = name::mk_str(name::dup(&quot_raw), "lift".chars().map(|c| c as u32).collect());
        let ind_raw = name::mk_str(name::dup(&quot_raw), "ind".chars().map(|c| c as u32).collect());
        let quot_ni = intern_name(&pers0, &mut st, &quot_raw).ok().expect("quot_ni");
        let lift_ni = intern_name(&pers0, &mut st, &lift_raw).ok().expect("lift_ni");
        let ind_ni = intern_name(&pers0, &mut st, &ind_raw).ok().expect("ind_ni");

        let pers = freeze_tier(&mut st.store, stream_index_empty());
        assert!(pers_peel_pis_ok(&pers, 0, pi2.word));
        assert!(pers_peel_pis_ok(&pers, 1, pi2.word));
        assert!(pers_peel_pis_ok(&pers, 2, pi2.word));
        assert!(!pers_peel_pis_ok(&pers, 3, pi2.word));

        let (found_lift, found_ind) = find_quot_child_names(&pers, quot_ni.word);
        assert_eq!(found_lift, lift_ni.word);
        assert_eq!(found_ind, ind_ni.word);
    }

    #[test]
    fn handle_bit_encodings_match_con_ron_core() {
        let e_app_p = EIdx::pack_wide(TIER_P, 12345);
        assert_eq!(e_app_p.word, (0u32 << 31) | (1u32 << 30) | 12345u32);
        assert_eq!(e_app_p.tag(), ETAG_APP);
        assert_eq!(e_app_p.tier(), TIER_P);
        assert_eq!(e_app_p.idx_nat(), 12345);
        let e_app_s = EIdx::pack_wide(TIER_S, 999);
        assert_eq!(e_app_s.word, (1u32 << 31) | (1u32 << 30) | 999u32);
        assert_eq!(e_app_s.tag(), ETAG_APP);
        assert_eq!(e_app_s.tier(), TIER_S);
        assert_eq!(e_app_s.idx_nat(), 999);

        let e_lam = EIdx::pack(ETAG_LAM, TIER_S, 77);
        assert_eq!(e_lam.word, (1u32 << 31) | (ETAG_LAM << 26) | 77u32);

        let l_succ = LIdx::pack(LTAG_SUCC, TIER_S, 55);
        assert_eq!(l_succ.word, (1u32 << 31) | (LTAG_SUCC << 26) | 55u32);

        let ls = LsIdx::pack(LSTAG_LIST, TIER_P, 12);
        assert_eq!(ls.word, (0u32 << 31) | (LSTAG_LIST << 26) | 12u32);

        let anon = NIdx::pack(NTAG_ANONYMOUS, TIER_P, 0);
        assert_eq!(anon.word, 0);
        assert_ne!(anon.word, EMPTY_NIDX_SENTINEL);
    }

    #[test]
    fn dag_guard_summary_accepts_closed_valid_and_rejects_malformed() {
        use con_ron_core::arena::checker::freeze_tier;
        use con_ron_core::arena::monad::{
            intern_e_app, intern_e_const, intern_e_fvar, intern_e_lam, intern_e_sort,
            intern_l_node, intern_ls_node, intern_name, AState,
        };
        use con_ron_core::arena::store::{LNodeView, PersTier};
        use con_ron_core::arena::stream_index::stream_index_empty;
        use con_ron_core::kernel::core_types::CheckError;
        use con_ron_core::kernel::name;

        fn ok<T>(r: Result<T, CheckError>) -> T {
            match r {
                Ok(v) => v,
                Err(_) => panic!("unexpected CheckError"),
            }
        }

        let pers0 = PersTier::empty();

        let mut st = AState::empty();
        let mut param_names = Vec::new();
        let mut param_levels = Vec::new();
        for i in 0..64u32 {
            let nm = name::mk_str(
                name::anonymous(),
                format!("u_{i}").chars().map(|c| c as u32).collect(),
            );
            let ni = ok(intern_name(&pers0, &mut st, &nm));
            let li = ok(intern_l_node(&pers0, &mut st, LNodeView::Param(ni)));
            param_names.push(ok(intern_name(&pers0, &mut st, &nm)));
            param_levels.push(li);
        }
        let c_name_raw = name::mk_str(name::anonymous(), "C0".chars().map(|c| c as u32).collect());
        let c_name = ok(intern_name(&pers0, &mut st, &c_name_raw));
        let c_fwd_raw = name::mk_str(
            name::anonymous(),
            "Cfwd".chars().map(|c| c as u32).collect(),
        );
        let c_fwd = ok(intern_name(&pers0, &mut st, &c_fwd_raw));
        let c_unres_raw = name::mk_str(
            name::anonymous(),
            "Cmissing".chars().map(|c| c as u32).collect(),
        );
        let c_unres = ok(intern_name(&pers0, &mut st, &c_unres_raw));

        use con_ron_core::ron::hashmap::Dup;

        let l_zero = ok(intern_l_node(&pers0, &mut st, LNodeView::Zero));
        let ls_empty = ok(intern_ls_node(&pers0, &mut st, Vec::new()));
        let ls_u0 = ok(intern_ls_node(&pers0, &mut st, vec![param_levels[0].dup2()]));
        let ls_u63 = ok(intern_ls_node(&pers0, &mut st, vec![param_levels[63].dup2()]));

        let s_u0 = ok(intern_e_sort(&pers0, &mut st, param_levels[0].dup2()));
        let s_0 = ok(intern_e_sort(&pers0, &mut st, l_zero));
        let s_u63 = ok(intern_e_sort(&pers0, &mut st, param_levels[63].dup2()));

        let b0 = ok(st
            .store
            .intern(&pers0, con_ron_core::arena::store::ENodeView::BVar(0)));
        let b1 = ok(st
            .store
            .intern(&pers0, con_ron_core::arena::store::ENodeView::BVar(1)));
        let lam_closed = ok(intern_e_lam(&pers0, &mut st, s_u0, b0));
        let lam_loose = ok(intern_e_lam(&pers0, &mut st, s_0.dup2(), b1));
        let fvar_e = ok(intern_e_fvar(&pers0, &mut st, 0, s_0.dup2()));
        let app_fvar = ok(intern_e_app(&pers0, &mut st, s_0.dup2(), fvar_e));

        let c_name_w = c_name.word;
        let c_fwd_w = c_fwd.word;
        let c_ok_e = ok(intern_e_const(&pers0, &mut st, c_name, ls_u0));
        let c_fwd_e = ok(intern_e_const(&pers0, &mut st, c_fwd, ls_empty.dup2()));
        let c_unres_e = ok(intern_e_const(&pers0, &mut st, c_unres, ls_empty));
        let app_valid = ok(intern_e_app(&pers0, &mut st, lam_closed, c_ok_e));
        let _ = ls_u63;

        let pers = freeze_tier(&mut st.store, stream_index_empty());
        let mut first_const_slot = HashMap::new();
        first_const_slot.insert(c_name_w, 0u32);
        first_const_slot.insert(c_fwd_w, 2u32);
        let firsts = [0u64, 1, 2, 3];
        let slot_to_rec = compute_slot_to_rec(3, &firsts);
        let dag = DagSummaries::build(&pers, &first_const_slot, &slot_to_rec);

        let u0_bit = *dag.lp_name_to_bit.get(&param_names[0].word).unwrap();
        assert!(u0_bit < 62);
        let u0_mask = 1u64 << u0_bit;

        // Valid closed expr with param u0 and C0 (slot=0, rec=0) checked at job (first_c=2, rec=2)
        assert!(dag.summary_guard_ok(app_valid.word, false, false, u0_mask, 2, 2));
        // Loose BVar fails
        assert!(!dag.summary_guard_ok(lam_loose.word, false, false, u0_mask, 2, 2));
        // FVar fails
        assert!(!dag.summary_guard_ok(app_fvar.word, false, false, u0_mask, 2, 2));
        // Undeclared lparam fails
        assert!(!dag.summary_guard_ok(app_valid.word, false, false, 0, 2, 2));
        // Forward constant fails (slot=2 >= first_c=2, rec=2 >= rec=2)
        assert!(!dag.summary_guard_ok(c_fwd_e.word, false, false, u0_mask, 2, 2));
        // Unresolved constant fails
        assert!(!dag.summary_guard_ok(c_unres_e.word, false, false, u0_mask, 2, 2));
        // dup_decl / dup_lp fail
        assert!(!dag.summary_guard_ok(app_valid.word, true, false, u0_mask, 2, 2));
        assert!(!dag.summary_guard_ok(app_valid.word, false, true, u0_mask, 2, 2));
        // Overflow >= 62 distinct universe param names (param 63 sets bit 62)
        assert!(!dag.summary_guard_ok(s_u63.word, false, false, u64::MAX, 2, 2));
    }

    #[test]
    fn pack_arena_from_delta_matches_full_pack_jobs() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let core_path = std::path::PathBuf::from(
                    "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init/Core.olean",
                );
                if !core_path.exists() {
                    return;
                }
                let sp = vec![std::path::PathBuf::from(
                    "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean",
                )];
                let spec = crate::loader::build_olean_input(
                    &[core_path.to_string_lossy().into_owned()],
                    &sp,
                    None,
                    true,
                );
                let env = crate::loader::load_environment(&spec).expect("Core loads");
                let cfg = ArenaLimitsConfig::default();
                let start_decl = env.decls.len().saturating_sub(250);
                let full_pkt = pack_arena(&env, cfg);
                let delta_pkt = pack_arena_from(&env, cfg, start_decl);

                assert_eq!(delta_pkt.jobs.len(), env.decls.len() - start_decl);
                assert_eq!(delta_pkt.header.num_jobs as usize, delta_pkt.jobs.len());

                let mut full_tail: std::collections::HashMap<u32, GpuJob> =
                    std::collections::HashMap::new();
                for j in &full_pkt.jobs {
                    if (j.orig_decl_idx as usize) >= start_decl {
                        full_tail.insert(j.orig_decl_idx, *j);
                    }
                }
                assert_eq!(full_tail.len(), delta_pkt.jobs.len());
                for dj in &delta_pkt.jobs {
                    let fj = full_tail[&dj.orig_decl_idx];
                    assert_eq!(dj.decl_kind, fj.decl_kind);
                    assert_eq!(dj.record_pos, fj.record_pos);
                    assert_eq!(dj.base_below, fj.base_below);
                    assert_eq!(dj.name, fj.name);
                    assert_eq!(dj.ty, fj.ty);
                    assert_eq!(dj.val, fj.val);
                    assert_eq!(dj.lparams_len, fj.lparams_len);
                    assert_eq!(dj.ast_size, fj.ast_size);
                    assert_eq!(dj.ast_bucket, fj.ast_bucket);
                    assert_eq!(dj.flags, fj.flags);
                    let f_off = (full_pkt.header.off_env_nidx + fj.lparams_off) as usize;
                    let d_off = (delta_pkt.header.off_env_nidx + dj.lparams_off) as usize;
                    let len = dj.lparams_len as usize;
                    assert_eq!(
                        &delta_pkt.env_tables[d_off..d_off + len],
                        &full_pkt.env_tables[f_off..f_off + len]
                    );
                }
            })
            .expect("spawn")
            .join()
            .expect("join");
    }
}
