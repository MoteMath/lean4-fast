use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Instant;

use rayon::prelude::*;

use con_ron_core::arena::basis::{and_pin_ok, basis_names_error, basis_names_ok};
use con_ron_core::arena::checker;
use con_ron_core::arena::checker_base::check_constant_val;
use con_ron_core::arena::core::{enter_record, leave_record};
use con_ron_core::arena::decl_check::{eq_stored, reduce_elem_ok_bool};
use con_ron_core::arena::env::{
    i_constant_val_dup, ifenv_find, IConstantInfo, IConstantVal, IDeclaration, IFEnv, IIndCaps,
    IRecRule, IRecRuleFire,
};
use con_ron_core::arena::handle::{EIdx, LIdx, LsIdx, NIdx, ETAG_BVAR};
use con_ron_core::arena::monad::{
    read_name, view_app, view_const, view_l, view_ls, view_ls_len, AState,
};
use con_ron_core::arena::pins::{pin_bool, pin_bool_true, pin_eq};
use con_ron_core::arena::store::{ENodeView, EStore, LNodeView, NNodeView, PersTier};
use con_ron_core::arena::stream_index::{self, M_AND_PIN};
use con_ron_core::frontend::olean::records::{read_value, value_cache_empty, ValueCache};
use con_ron_core::kernel::core_types::{code_points, CheckError};
use con_ron_core::kernel::env::{CheckMode, QuotKind, ReducibilityHint};
use con_ron_core::kernel::expr::Literal;
use con_ron_core::kernel::trust_axioms as ctrust;
use con_ron_core::ron::hashmap::Eq2;

use crate::fs::StdFs;
use crate::loader::{classify_error, LoadedEnvironment, VerificationVerdict};

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct VerifyOptions {
    pub trust_bv_decide_axioms: bool,
}

#[derive(Clone, Debug, Default)]
pub struct HostTelemetry {
    pub checked_count: usize,
    pub thread_count: usize,
    pub elapsed_ns: u128,
}

struct WorkerCtx {
    state: AState,
    val_cache: ValueCache,
}

impl WorkerCtx {
    fn new(env: &LoadedEnvironment) -> Self {
        Self {
            state: checker::worker_state(&env.pins),
            val_cache: value_cache_empty(),
        }
    }
}

fn str_cp_eq(cp: &[u32], ascii: &str) -> bool {
    let bytes = ascii.as_bytes();
    cp.len() == bytes.len() && cp.iter().zip(bytes.iter()).all(|(&c, &b)| c == b as u32)
}

fn dangling_name_err() -> CheckError {
    const M_DANGLING_N: [u32; 13] = [
        100, 97, 110, 103, 108, 105, 110, 103, 32, 110, 97, 109, 101,
    ];
    CheckError::Internal(code_points(&M_DANGLING_N))
}

fn is_bv_decide_ax_leaf(cp: &[u32]) -> bool {
    if !cp.starts_with(&[97, 120, 95]) {
        return false;
    }
    let rest = &cp[3..];
    !rest.is_empty()
        && rest
            .split(|&c| c == 95)
            .all(|part| !part.is_empty() && part.iter().all(|&c| (48..=57).contains(&c)))
}

fn name_has_bv_decide_ax_suffix(pers: &PersTier, w: &AState, n: &NIdx) -> Result<bool, CheckError> {
    let ns = w.store.ns();
    let Some(NNodeView::Str(p1, s_ax)) = ns.view(pers, n) else {
        return match ns.view(pers, n) {
            None => Err(dangling_name_err()),
            Some(_) => Ok(false),
        };
    };
    if !is_bv_decide_ax_leaf(&s_ax) {
        return Ok(false);
    }
    let Some(NNodeView::Str(p2, s_bvd)) = ns.view(pers, &p1) else {
        return match ns.view(pers, &p1) {
            None => Err(dangling_name_err()),
            Some(_) => Ok(false),
        };
    };
    if !str_cp_eq(&s_bvd, "bv_decide") {
        return Ok(false);
    }
    let Some(NNodeView::Str(p3, s_nat)) = ns.view(pers, &p2) else {
        return match ns.view(pers, &p2) {
            None => Err(dangling_name_err()),
            Some(_) => Ok(false),
        };
    };
    if !str_cp_eq(&s_nat, "_native") {
        return Ok(false);
    }
    match ns.view(pers, &p3) {
        None => Err(dangling_name_err()),
        Some(NNodeView::Anonymous) => Ok(false),
        Some(_) => Ok(true),
    }
}

fn name_is_str_path(
    pers: &PersTier,
    w: &AState,
    n: &NIdx,
    segments: &[&str],
) -> Result<bool, CheckError> {
    let ns = w.store.ns();
    let mut cur = NIdx::of_word(n.word);
    for &seg in segments.iter().rev() {
        match ns.view(pers, &cur) {
            None => return Err(dangling_name_err()),
            Some(NNodeView::Str(parent, cp)) => {
                if !str_cp_eq(&cp, seg) {
                    return Ok(false);
                }
                cur = parent;
            }
            Some(_) => return Ok(false),
        }
    }
    match ns.view(pers, &cur) {
        None => Err(dangling_name_err()),
        Some(NNodeView::Anonymous) => Ok(true),
        Some(_) => Ok(false),
    }
}

fn is_level_one(pers: &PersTier, w: &AState, ls: &LsIdx) -> Result<bool, CheckError> {
    let us = view_ls(pers, w, ls)?;
    if us.len() != 1 {
        return Ok(false);
    }
    match view_l(pers, w, &us[0])? {
        LNodeView::Succ(inner) => Ok(matches!(view_l(pers, w, &inner)?, LNodeView::Zero)),
        _ => Ok(false),
    }
}

fn bv_decide_axiom_shape_and_env_ok(
    pers: &PersTier,
    w: &mut AState,
    fe: &IFEnv,
    cv: &IConstantVal,
) -> Result<bool, CheckError> {
    if !cv.level_params.is_empty() {
        return Ok(false);
    }
    if !eq_stored(pers, w, fe)? {
        return Ok(false);
    }
    if !reduce_elem_ok_bool(pers, w, fe)? {
        return Ok(false);
    }
    let true_name = pin_bool_true(w)?;
    if !matches!(
        ifenv_find(pers, fe, &true_name),
        Some(IConstantInfo::CtorInfo(..))
    ) {
        return Ok(false);
    }

    let Some((f_ab, rhs)) = view_app(pers, w, &cv.ty) else {
        return Ok(false);
    };
    let Some((rhs_name, rhs_ls)) = view_const(pers, w, &rhs) else {
        return Ok(false);
    };
    if !rhs_name.eq2(&true_name) || view_ls_len(pers, w, &rhs_ls) != Some(0) {
        return Ok(false);
    }

    let Some((f_a, lhs)) = view_app(pers, w, &f_ab) else {
        return Ok(false);
    };
    let Some((eq_expr, bool_expr)) = view_app(pers, w, &f_a) else {
        return Ok(false);
    };
    let Some((eq_name, eq_ls)) = view_const(pers, w, &eq_expr) else {
        return Ok(false);
    };
    if !eq_name.eq2(&pin_eq(w)?) || !is_level_one(pers, w, &eq_ls)? {
        return Ok(false);
    }

    let Some((bool_name, bool_ls)) = view_const(pers, w, &bool_expr) else {
        return Ok(false);
    };
    if !bool_name.eq2(&pin_bool(w)?) || view_ls_len(pers, w, &bool_ls) != Some(0) {
        return Ok(false);
    }

    let Some((v_app1, _cert_expr)) = view_app(pers, w, &lhs) else {
        return Ok(false);
    };
    let Some((v_head, _reflected_expr)) = view_app(pers, w, &v_app1) else {
        return Ok(false);
    };
    let Some((v_name, v_ls)) = view_const(pers, w, &v_head) else {
        return Ok(false);
    };
    if view_ls_len(pers, w, &v_ls) != Some(0) {
        return Ok(false);
    }
    if !name_is_str_path(
        pers,
        w,
        &v_name,
        &["Std", "Tactic", "BVDecide", "Reflect", "verifyBVExpr"],
    )? {
        return Ok(false);
    }
    if !matches!(
        ifenv_find(pers, fe, &v_name),
        Some(IConstantInfo::DefnInfo(..))
    ) {
        return Ok(false);
    }
    Ok(true)
}

fn check_axiom_maybe_trusted_bv_decide(
    env: &LoadedEnvironment,
    w: &mut AState,
    k: u64,
    d: &IDeclaration,
    cv: &IConstantVal,
) -> Option<Result<(), (CheckError, u64)>> {
    match name_has_bv_decide_ax_suffix(&env.pers, w, &cv.name) {
        Err(e) => return Some(Err((e, k))),
        Ok(false) => return None,
        Ok(true) => {}
    }

    match and_pin_ok(&env.pers, w, d) {
        Err(e) => return Some(Err((e, k))),
        Ok(false) => return Some(Err((CheckError::Invalid(code_points(&M_AND_PIN)), k))),
        Ok(true) => {}
    }

    let fe = stream_index::stream_index_view(&env.pers, k);
    if let Err(e) = check_constant_val(&env.pers, w, &CheckMode::Verified, &fe, cv, false) {
        return Some(Err((e, k)));
    }

    match bv_decide_axiom_shape_and_env_ok(&env.pers, w, &fe, cv) {
        Err(e) => return Some(Err((e, k))),
        Ok(false) => {
            return match read_name(&env.pers, w, &cv.name) {
                Err(e) => Some(Err((e, k))),
                Ok(n) => Some(Err((
                    CheckError::NotImplemented(ctrust::non_std_axiom_msg(&n)),
                    k,
                ))),
            };
        }
        Ok(true) => {}
    }

    match basis_names_ok(&env.pers, w, d) {
        Err(e) => Some(Err((e, k))),
        Ok(true) => Some(Ok(())),
        Ok(false) => match basis_names_error(&env.pers, w, d) {
            Err(e) => Some(Err((e, k))),
            Ok(e) => Some(Err((e, k))),
        },
    }
}

pub fn check_job_exact(
    env: &LoadedEnvironment,
    w: &mut AState,
    val_cache: &mut ValueCache,
    k: u64,
) -> Result<(), (CheckError, u64)> {
    check_job_exact_with(env, w, val_cache, k, VerifyOptions::default())
}

pub fn check_job_exact_with(
    env: &LoadedEnvironment,
    w: &mut AState,
    val_cache: &mut ValueCache,
    k: u64,
    opts: VerifyOptions,
) -> Result<(), (CheckError, u64)> {
    let idx = k as usize;
    let d = match env.decls.get(idx) {
        Some(d) => d,
        None => {
            return checker::run_job(
                &env.pers,
                w,
                &CheckMode::Verified,
                &env.ipins,
                &env.decls,
                k,
            )
        }
    };

    if opts.trust_bv_decide_axioms {
        if let IDeclaration::AxiomDecl(cv) = d {
            enter_record(w);
            let res = check_axiom_maybe_trusted_bv_decide(env, w, k, d, cv);
            leave_record(w);
            if let Some(r) = res {
                return r;
            }
        }
    }

    if let (Some((ref pk, ref values, ref sp)), IDeclaration::ThmDecl(cv, v)) = (&env.olean, d) {
        if v.tag() == ETAG_BVAR {
            if let Some(code) = w.store.view_bvar(&env.pers, v) {
                enter_record(w);
                let res = match read_value(
                    &StdFs,
                    pk,
                    &env.pers,
                    &mut w.store,
                    sp,
                    values,
                    val_cache,
                    code,
                ) {
                    Err(e) => Err((e, k)),
                    Ok(e) => {
                        let d2 = IDeclaration::ThmDecl(i_constant_val_dup(cv), e);
                        match stream_index::record_check(
                            &env.pers,
                            w,
                            &CheckMode::Verified,
                            &env.ipins,
                            k,
                            &d2,
                        ) {
                            Err(e) => Err((e, k)),
                            Ok(()) => Ok(()),
                        }
                    }
                };
                leave_record(w);
                return res;
            } else {
                const M_DANGLING_REF: [u32; 28] = [
                    100, 97, 110, 103, 108, 105, 110, 103, 32, 111, 108, 101, 97, 110, 32, 116,
                    104, 101, 111, 114, 101, 109, 32, 118, 97, 108, 117, 101,
                ];
                return Err((CheckError::Internal(code_points(&M_DANGLING_REF)), k));
            }
        }
    }

    checker::run_job(
        &env.pers,
        w,
        &CheckMode::Verified,
        &env.ipins,
        &env.decls,
        k,
    )
}

static RAYON_POOL_CACHE: OnceLock<Mutex<Option<(usize, Arc<rayon::ThreadPool>)>>> = OnceLock::new();

fn build_pool(threads: Option<usize>) -> Result<(Arc<rayon::ThreadPool>, usize), String> {
    let n = threads
        .or_else(|| {
            std::env::var("RAYON_NUM_THREADS")
                .ok()
                .and_then(|s| s.parse::<usize>().ok())
        })
        .unwrap_or_else(|| {
            std::thread::available_parallelism()
                .map(|p| p.get())
                .unwrap_or(1)
        })
        .max(1);

    let cache = RAYON_POOL_CACHE.get_or_init(|| Mutex::new(None));
    let mut guard = cache
        .lock()
        .map_err(|_| "rayon thread pool cache poisoned".to_string())?;
    if let Some((cached_n, ref pool)) = *guard {
        if cached_n == n {
            return Ok((Arc::clone(pool), n));
        }
    }

    let pool = Arc::new(
        rayon::ThreadPoolBuilder::new()
            .num_threads(n)
            .stack_size(1024 * 1024 * 1024)
            .build()
            .map_err(|e| format!("failed to build rayon thread pool: {}", e))?,
    );
    *guard = Some((n, Arc::clone(&pool)));
    Ok((pool, n))
}

/// Exact multi-core CPU verifier using `con-ron-core` across up to 96+ rayon cores.
pub fn verify_host_parallel(
    env: &LoadedEnvironment,
    threads: Option<usize>,
) -> (VerificationVerdict, HostTelemetry) {
    verify_host_parallel_with(env, threads, VerifyOptions::default())
}

/// Exact multi-core CPU verifier with explicit `VerifyOptions`.
pub fn verify_host_parallel_with(
    env: &LoadedEnvironment,
    threads: Option<usize>,
    opts: VerifyOptions,
) -> (VerificationVerdict, HostTelemetry) {
    verify_host_range_with(env, 0, threads, opts)
}

/// Exact multi-core CPU verifier checking only `[start_idx .. env.decls.len())`.
/// Intended for daemon `--base-olean` prefix caching when `[0 .. start_idx)` was proven structurally identical.
pub fn verify_host_range_with(
    env: &LoadedEnvironment,
    start_idx: usize,
    threads: Option<usize>,
    opts: VerifyOptions,
) -> (VerificationVerdict, HostTelemetry) {
    let start = start_idx.min(env.decls.len());
    let jobs: Vec<usize> = (start..env.decls.len()).collect();
    let (res, tel) = verify_delegated_exact_with(env, &jobs, threads, opts);
    let verdict = match res {
        Ok(()) => VerificationVerdict::Accepted {
            file_records: env.file_records,
            fold_records: env.decls.len(),
        },
        Err(v) => v,
    };
    (verdict, tel)
}

pub(crate) struct StructuralPrefixCmp<'a> {
    pers_a: &'a PersTier,
    pers_b: &'a PersTier,
    st_a: &'a EStore,
    st_b: &'a EStore,
    n_eq: HashMap<u64, bool>,
    l_eq: HashMap<u64, bool>,
    ls_eq: HashMap<u64, bool>,
    e_ok: HashSet<u64>,
}

impl<'a> StructuralPrefixCmp<'a> {
    pub(crate) fn new(
        pers_a: &'a PersTier,
        st_a: &'a EStore,
        pers_b: &'a PersTier,
        st_b: &'a EStore,
    ) -> Self {
        Self {
            pers_a,
            pers_b,
            st_a,
            st_b,
            n_eq: HashMap::new(),
            l_eq: HashMap::new(),
            ls_eq: HashMap::new(),
            e_ok: HashSet::new(),
        }
    }

    #[inline]
    fn pair_key(a: u32, b: u32) -> u64 {
        ((a as u64) << 32) | (b as u64)
    }

    fn eq_name(&mut self, a: &NIdx, b: &NIdx) -> bool {
        let mut pairs = Vec::new();
        let mut cur_a = NIdx::of_word(a.word);
        let mut cur_b = NIdx::of_word(b.word);
        let ok = loop {
            let k = Self::pair_key(cur_a.word, cur_b.word);
            if let Some(&cached) = self.n_eq.get(&k) {
                break cached;
            }
            pairs.push(k);
            match (
                self.st_a.ns().view(self.pers_a, &cur_a),
                self.st_b.ns().view(self.pers_b, &cur_b),
            ) {
                (Some(NNodeView::Anonymous), Some(NNodeView::Anonymous)) => break true,
                (Some(NNodeView::Str(pa, sa)), Some(NNodeView::Str(pb, sb))) if sa == sb => {
                    cur_a = pa;
                    cur_b = pb;
                }
                (Some(NNodeView::Num(pa, na)), Some(NNodeView::Num(pb, nb))) if na == nb => {
                    cur_a = pa;
                    cur_b = pb;
                }
                _ => break false,
            }
        };
        for k in pairs {
            self.n_eq.insert(k, ok);
        }
        ok
    }

    fn eq_names(&mut self, a: &[NIdx], b: &[NIdx]) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| self.eq_name(x, y))
    }

    fn eq_level(&mut self, a: &LIdx, b: &LIdx) -> bool {
        let mut stack = vec![(LIdx::of_word(a.word), LIdx::of_word(b.word))];
        let mut visited = Vec::new();
        while let Some((la, lb)) = stack.pop() {
            let k = Self::pair_key(la.word, lb.word);
            if let Some(&cached) = self.l_eq.get(&k) {
                if !cached {
                    return false;
                }
                continue;
            }
            visited.push(k);
            match (
                self.st_a.ls().view(self.pers_a, &la),
                self.st_b.ls().view(self.pers_b, &lb),
            ) {
                (Some(LNodeView::Zero), Some(LNodeView::Zero)) => {}
                (Some(LNodeView::Succ(ua)), Some(LNodeView::Succ(ub))) => stack.push((ua, ub)),
                (Some(LNodeView::Max(a1, a2)), Some(LNodeView::Max(b1, b2)))
                | (Some(LNodeView::Imax(a1, a2)), Some(LNodeView::Imax(b1, b2))) => {
                    stack.push((a1, b1));
                    stack.push((a2, b2));
                }
                (Some(LNodeView::Param(na)), Some(LNodeView::Param(nb))) => {
                    if !self.eq_name(&na, &nb) {
                        self.l_eq.insert(k, false);
                        return false;
                    }
                }
                _ => {
                    self.l_eq.insert(k, false);
                    return false;
                }
            }
        }
        for k in visited {
            self.l_eq.insert(k, true);
        }
        true
    }

    fn eq_levels(&mut self, a: &LsIdx, b: &LsIdx) -> bool {
        let k = Self::pair_key(a.word, b.word);
        if let Some(&cached) = self.ls_eq.get(&k) {
            return cached;
        }
        let ok = match (
            self.st_a.ls_s().view(self.pers_a, a),
            self.st_b.ls_s().view(self.pers_b, b),
        ) {
            (Some(va), Some(vb)) => {
                va.len() == vb.len() && va.iter().zip(vb.iter()).all(|(x, y)| self.eq_level(x, y))
            }
            _ => false,
        };
        self.ls_eq.insert(k, ok);
        ok
    }

    fn eq_lidx_vec(&mut self, a: &[LIdx], b: &[LIdx]) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| self.eq_level(x, y))
    }

    fn eq_expr(&mut self, a: &EIdx, b: &EIdx) -> bool {
        let mut stack = vec![(EIdx::of_word(a.word), EIdx::of_word(b.word))];
        let mut newly_checked = Vec::new();
        while let Some((ea, eb)) = stack.pop() {
            let k = Self::pair_key(ea.word, eb.word);
            if self.e_ok.contains(&k) {
                continue;
            }
            match (
                self.st_a.view(self.pers_a, &ea),
                self.st_b.view(self.pers_b, &eb),
            ) {
                (Some(ENodeView::BVar(ia)), Some(ENodeView::BVar(ib))) if ia == ib => {}
                (Some(ENodeView::FVar(ia, ta)), Some(ENodeView::FVar(ib, tb))) if ia == ib => {
                    stack.push((ta, tb));
                }
                (Some(ENodeView::Sort(ua)), Some(ENodeView::Sort(ub))) => {
                    if !self.eq_level(&ua, &ub) {
                        return false;
                    }
                }
                (Some(ENodeView::Const(na, lsa)), Some(ENodeView::Const(nb, lsb))) => {
                    if !self.eq_name(&na, &nb) || !self.eq_levels(&lsa, &lsb) {
                        return false;
                    }
                }
                (Some(ENodeView::App(fa, aa)), Some(ENodeView::App(fb, ab))) => {
                    stack.push((fa, fb));
                    stack.push((aa, ab));
                }
                (Some(ENodeView::Lam(ta, ba)), Some(ENodeView::Lam(tb, bb)))
                | (Some(ENodeView::ForallE(ta, ba)), Some(ENodeView::ForallE(tb, bb))) => {
                    stack.push((ta, tb));
                    stack.push((ba, bb));
                }
                (Some(ENodeView::LetE(ta, va, ba)), Some(ENodeView::LetE(tb, vb, bb))) => {
                    stack.push((ta, tb));
                    stack.push((va, vb));
                    stack.push((ba, bb));
                }
                (Some(ENodeView::Lit(Literal::NatVal(na))), Some(ENodeView::Lit(Literal::NatVal(nb)))) => {
                    if na.limbs != nb.limbs {
                        return false;
                    }
                }
                (Some(ENodeView::Lit(Literal::StrVal(sa))), Some(ENodeView::Lit(Literal::StrVal(sb)))) => {
                    if *sa != *sb {
                        return false;
                    }
                }
                (Some(ENodeView::Proj(na, ia, ea2)), Some(ENodeView::Proj(nb, ib, eb2))) if ia == ib => {
                    if !self.eq_name(&na, &nb) {
                        return false;
                    }
                    stack.push((ea2, eb2));
                }
                _ => return false,
            }
            newly_checked.push(k);
        }
        for k in newly_checked {
            self.e_ok.insert(k);
        }
        true
    }

    fn eq_expr_vec(&mut self, a: &[EIdx], b: &[EIdx]) -> bool {
        a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| self.eq_expr(x, y))
    }

    fn eq_cv(&mut self, a: &IConstantVal, b: &IConstantVal) -> bool {
        self.eq_name(&a.name, &b.name)
            && self.eq_names(&a.level_params, &b.level_params)
            && self.eq_expr(&a.ty, &b.ty)
    }

    fn eq_caps(&mut self, a: &IIndCaps, b: &IIndCaps) -> bool {
        a.eta == b.eta
            && a.nparams == b.nparams
            && a.n_idx == b.n_idx
            && a.never_zero == b.never_zero
            && self.eq_names(&a.all, &b.all)
            && self.eq_names(&a.ctors, &b.ctors)
    }

    fn eq_fire(&mut self, a: &IRecRuleFire, b: &IRecRuleFire) -> bool {
        match (a, b) {
            (IRecRuleFire::Plain, IRecRuleFire::Plain) => true,
            (IRecRuleFire::Nested(la, ea), IRecRuleFire::Nested(lb, eb)) => {
                self.eq_lidx_vec(la, lb) && self.eq_expr_vec(ea, eb)
            }
            (IRecRuleFire::Levels(la), IRecRuleFire::Levels(lb)) => self.eq_lidx_vec(la, lb),
            _ => false,
        }
    }

    fn eq_rec_rules(&mut self, a: &[IRecRule], b: &[IRecRule]) -> bool {
        a.len() == b.len()
            && a.iter().zip(b.iter()).all(|(ra, rb)| {
                ra.nfields == rb.nfields
                    && self.eq_name(&ra.ctor, &rb.ctor)
                    && self.eq_fire(&ra.fire, &rb.fire)
                    && self.eq_expr(&ra.rhs, &rb.rhs)
            })
    }

    fn eq_cinfo(&mut self, a: &IConstantInfo, b: &IConstantInfo) -> bool {
        match (a, b) {
            (IConstantInfo::AxiomInfo(ca), IConstantInfo::AxiomInfo(cb))
            | (IConstantInfo::ThmInfo(ca), IConstantInfo::ThmInfo(cb)) => self.eq_cv(ca, cb),
            (IConstantInfo::DefnInfo(ca, va, ha), IConstantInfo::DefnInfo(cb, vb, hb)) => {
                eq_hint(ha, hb) && self.eq_cv(ca, cb) && self.eq_expr(va, vb)
            }
            (IConstantInfo::IndInfo(ca, xa), IConstantInfo::IndInfo(cb, xb)) => {
                self.eq_caps(xa, xb) && self.eq_cv(ca, cb)
            }
            (
                IConstantInfo::CtorInfo(ca, pa, fa, ia),
                IConstantInfo::CtorInfo(cb, pb, fb, ib),
            ) => pa == pb && fa == fb && self.eq_name(ia, ib) && self.eq_cv(ca, cb),
            (
                IConstantInfo::RecInfo(ca, pa, ia, ka, ra),
                IConstantInfo::RecInfo(cb, pb, ib, kb, rb),
            ) => pa == pb && ia == ib && ka == kb && self.eq_cv(ca, cb) && self.eq_rec_rules(ra, rb),
            _ => false,
        }
    }

    pub(crate) fn eq_decl_prefix_with_lazy_thm<F>(
        &mut self,
        a: &IDeclaration,
        b: &IDeclaration,
        allow_lazy_a: bool,
        mut lazy_thm_unchanged: F,
    ) -> bool
    where
        F: FnMut(&EIdx) -> bool,
    {
        match (a, b) {
            (IDeclaration::AxiomDecl(ca), IDeclaration::AxiomDecl(cb)) => self.eq_cv(ca, cb),
            (IDeclaration::DefnDecl(ca, va, ha), IDeclaration::DefnDecl(cb, vb, hb)) => {
                eq_hint(ha, hb) && self.eq_cv(ca, cb) && self.eq_expr(va, vb)
            }
            (IDeclaration::ThmDecl(ca, va), IDeclaration::ThmDecl(cb, vb)) => {
                if !self.eq_cv(ca, cb) {
                    return false;
                }
                if va.tag() == ETAG_BVAR {
                    return allow_lazy_a && vb.tag() == ETAG_BVAR && lazy_thm_unchanged(vb);
                }
                if vb.tag() != ETAG_BVAR {
                    self.eq_expr(va, vb)
                } else {
                    lazy_thm_unchanged(vb)
                }
            }
            (IDeclaration::OpaqueDecl(ca, va), IDeclaration::OpaqueDecl(cb, vb)) => {
                self.eq_cv(ca, cb) && self.eq_expr(va, vb)
            }
            (IDeclaration::IndDecl(ba, na), IDeclaration::IndDecl(bb, nb)) => {
                na == nb
                    && ba.len() == bb.len()
                    && ba.iter().zip(bb.iter()).all(|(ia, ib)| self.eq_cinfo(ia, ib))
            }
            (IDeclaration::QuotDecl(ka, ca), IDeclaration::QuotDecl(kb, cb)) => {
                eq_quot(ka, kb) && self.eq_cv(ca, cb)
            }
            _ => false,
        }
    }

    fn eq_decl(&mut self, a: &IDeclaration, b: &IDeclaration) -> bool {
        self.eq_decl_prefix_with_lazy_thm(a, b, false, |_| false)
    }
}

fn eq_hint(a: &ReducibilityHint, b: &ReducibilityHint) -> bool {
    match (a, b) {
        (ReducibilityHint::Opaque, ReducibilityHint::Opaque)
        | (ReducibilityHint::Abbrev, ReducibilityHint::Abbrev) => true,
        (ReducibilityHint::Regular(xa), ReducibilityHint::Regular(xb)) => xa == xb,
        _ => false,
    }
}

fn eq_quot(a: &QuotKind, b: &QuotKind) -> bool {
    matches!(
        (a, b),
        (QuotKind::Type, QuotKind::Type)
            | (QuotKind::Ctor, QuotKind::Ctor)
            | (QuotKind::Lift, QuotKind::Lift)
            | (QuotKind::Ind, QuotKind::Ind)
            | (QuotKind::Sound, QuotKind::Sound)
    )
}

/// Returns the maximal leading declaration prefix `[0 .. k)` where `target` is term-for-term
/// structurally identical (with materialized theorem bodies) to `base`.
/// Precondition: caller already checked `base` accepted under compatible `VerifyOptions`.
pub fn matching_verified_prefix_len(
    base: &LoadedEnvironment,
    target: &LoadedEnvironment,
) -> usize {
    let limit = base.decls.len().min(target.decls.len());
    let empty_a = EStore::empty_frozen();
    let empty_b = EStore::empty_frozen();
    let mut cmp = StructuralPrefixCmp::new(&base.pers, &empty_a, &target.pers, &empty_b);
    let mut k = 0usize;
    while k < limit {
        if !cmp.eq_decl(&base.decls[k], &target.decls[k]) {
            break;
        }
        k += 1;
    }
    k
}

/// Exact parallel `con-ron-core` verification for a specified subset of declaration indices
/// (used both for full `--backend cpu` runs and for GPU `STATUS_DELEGATE` fallback).
/// Guarantees fold-order lowest-index error reporting to match sequential `con-ron` semantics.
pub fn verify_delegated_exact(
    env: &LoadedEnvironment,
    indices: &[usize],
    threads: Option<usize>,
) -> (Result<(), VerificationVerdict>, HostTelemetry) {
    verify_delegated_exact_with(env, indices, threads, VerifyOptions::default())
}

/// Exact parallel `con-ron-core` verification for delegated indices with explicit `VerifyOptions`.
pub fn verify_delegated_exact_with(
    env: &LoadedEnvironment,
    indices: &[usize],
    threads: Option<usize>,
    opts: VerifyOptions,
) -> (Result<(), VerificationVerdict>, HostTelemetry) {
    let t0 = Instant::now();
    if indices.is_empty() {
        return (
            Ok(()),
            HostTelemetry {
                checked_count: 0,
                thread_count: 0,
                elapsed_ns: t0.elapsed().as_nanos(),
            },
        );
    }

    let (pool, n_threads) = match build_pool(threads) {
        Ok(p) => p,
        Err(msg) => {
            return (
                Err(VerificationVerdict::Error {
                    message: msg,
                    line_or_pos: 0,
                }),
                HostTelemetry {
                    checked_count: 0,
                    thread_count: 0,
                    elapsed_ns: t0.elapsed().as_nanos(),
                },
            );
        }
    };

    let failures: Vec<(u64, CheckError)> = pool.install(|| {
        indices
            .par_iter()
            .map_init(
                || WorkerCtx::new(env),
                |ctx, &decl_idx| {
                    match check_job_exact_with(
                        env,
                        &mut ctx.state,
                        &mut ctx.val_cache,
                        decl_idx as u64,
                        opts,
                    ) {
                        Ok(()) => None,
                        Err((e, k)) => Some((k, e)),
                    }
                },
            )
            .filter_map(|x| x)
            .collect()
    });

    let elapsed_ns = t0.elapsed().as_nanos();
    let tel = HostTelemetry {
        checked_count: indices.len(),
        thread_count: n_threads,
        elapsed_ns,
    };

    if failures.is_empty() {
        (Ok(()), tel)
    } else {
        // Pick earliest declaration in fold order (deterministic verdict).
        let (k, e) = failures
            .into_iter()
            .min_by_key(|(k, _)| *k)
            .expect("non-empty failures");
        (Err(classify_error(e, k)), tel)
    }
}

/// Persistent rayon worker session that keeps one `(AState, ValueCache)` per worker thread
/// across multiple delegated batches and sorts indices in ascending declaration order to maximize
/// `.olean` compacted-region cache locality while work-stealing dynamically.
pub struct HostExactRunner<'a> {
    env: &'a LoadedEnvironment,
    pool: Arc<rayon::ThreadPool>,
    n_threads: usize,
    ctxs: Vec<Mutex<WorkerCtx>>,
    opts: VerifyOptions,
}

impl<'a> HostExactRunner<'a> {
    pub fn new(env: &'a LoadedEnvironment, threads: Option<usize>) -> Result<Self, VerificationVerdict> {
        Self::new_with(env, threads, VerifyOptions::default())
    }

    pub fn new_with(
        env: &'a LoadedEnvironment,
        threads: Option<usize>,
        opts: VerifyOptions,
    ) -> Result<Self, VerificationVerdict> {
        let (pool, n_threads) = build_pool(threads).map_err(|msg| VerificationVerdict::Error {
            message: msg,
            line_or_pos: 0,
        })?;
        let ctxs: Vec<Mutex<WorkerCtx>> = pool.install(|| {
            (0..n_threads)
                .into_par_iter()
                .map(|_| Mutex::new(WorkerCtx::new(env)))
                .collect()
        });
        Ok(Self {
            env,
            pool,
            n_threads,
            ctxs,
            opts,
        })
    }

    pub fn verify_batch(&self, raw_indices: &[usize]) -> Result<(), VerificationVerdict> {
        if raw_indices.is_empty() {
            return Ok(());
        }
        let mut sorted = raw_indices.to_vec();
        if sorted.len() > 1 {
            sorted.sort_unstable();
        }
        let chunk_sz = if sorted.len() <= 64 { 1 } else { 16 };
        let cursor = AtomicUsize::new(0);
        let errs: Mutex<Vec<(u64, CheckError)>> = Mutex::new(Vec::new());

        self.pool.broadcast(|bctx| {
            let Some(tid) = bctx.index().checked_sub(0).filter(|&i| i < self.ctxs.len()) else {
                return;
            };
            let mut ctx_guard = self.ctxs[tid].lock().expect("worker ctx lock");
            let ctx = &mut *ctx_guard;
            let mut local_best: Option<(u64, CheckError)> = None;
            loop {
                let start = cursor.fetch_add(chunk_sz, Ordering::Relaxed);
                if start >= sorted.len() {
                    break;
                }
                let end = (start + chunk_sz).min(sorted.len());
                for &decl_idx in &sorted[start..end] {
                    if let Err((e, k)) = check_job_exact_with(
                        self.env,
                        &mut ctx.state,
                        &mut ctx.val_cache,
                        decl_idx as u64,
                        self.opts,
                    ) {
                        match &local_best {
                            Some((best_k, _)) if *best_k <= k => {}
                            _ => local_best = Some((k, e)),
                        }
                    }
                }
            }
            if let Some(err) = local_best {
                errs.lock().expect("errs lock").push(err);
            }
        });

        let failures = errs.into_inner().expect("errs lock");
        if failures.is_empty() {
            Ok(())
        } else {
            let (k, e) = failures
                .into_iter()
                .min_by_key(|(k, _)| *k)
                .expect("non-empty failures");
            Err(classify_error(e, k))
        }
    }

    /// Runs a single barrier-free `pool.broadcast` session pulling dynamic index batches
    /// from `next_batch` until exhausted, keeping every worker's `(AState, ValueCache)`
    /// warm across stolen heavy slices and streamed GPU-delegated chunks.
    pub fn run_streaming<F>(&self, next_batch: F) -> Result<(), VerificationVerdict>
    where
        F: FnMut() -> Option<Vec<usize>> + Send,
    {
        struct QueueState<G> {
            items: Vec<usize>,
            cursor: usize,
            chunk_sz: usize,
            done: bool,
            next_batch: G,
        }
        let state = Mutex::new(QueueState {
            items: Vec::new(),
            cursor: 0,
            chunk_sz: 1,
            done: false,
            next_batch,
        });
        let errs: Mutex<Vec<(u64, CheckError)>> = Mutex::new(Vec::new());

        self.pool.broadcast(|bctx| {
            let Some(tid) = bctx.index().checked_sub(0).filter(|&i| i < self.ctxs.len()) else {
                return;
            };
            let mut ctx_guard = self.ctxs[tid].lock().expect("worker ctx lock");
            let ctx = &mut *ctx_guard;
            let mut local_best: Option<(u64, CheckError)> = None;
            let mut buf = [0usize; 4];
            loop {
                let buf_len = {
                    let mut q = state.lock().expect("streaming queue lock");
                    while q.cursor >= q.items.len() {
                        if q.done {
                            break;
                        }
                        if let Some(mut batch) = (q.next_batch)() {
                            if batch.is_empty() {
                                continue;
                            }
                            if batch.len() > 1 {
                                batch.sort_unstable();
                            }
                            q.chunk_sz = if batch.len() <= 64 {
                                1
                            } else if batch.len() <= 1024 {
                                2
                            } else {
                                4
                            };
                            q.items = batch;
                            q.cursor = 0;
                            break;
                        } else {
                            q.done = true;
                            break;
                        }
                    }
                    if q.cursor >= q.items.len() {
                        0
                    } else {
                        let remain = q.items.len() - q.cursor;
                        let step = if remain <= 64 {
                            1
                        } else {
                            q.chunk_sz.min(remain).min(buf.len())
                        };
                        for (dst, &src) in buf[..step].iter_mut().zip(&q.items[q.cursor..q.cursor + step]) {
                            *dst = src;
                        }
                        q.cursor += step;
                        step
                    }
                };
                if buf_len == 0 {
                    break;
                }
                for &decl_idx in &buf[..buf_len] {
                    if let Err((e, k)) = check_job_exact_with(
                        self.env,
                        &mut ctx.state,
                        &mut ctx.val_cache,
                        decl_idx as u64,
                        self.opts,
                    ) {
                        match &local_best {
                            Some((best_k, _)) if *best_k <= k => {}
                            _ => local_best = Some((k, e)),
                        }
                    }
                }
            }
            if let Some(err) = local_best {
                errs.lock().expect("errs lock").push(err);
            }
        });

        let failures = errs.into_inner().expect("errs lock");
        if failures.is_empty() {
            Ok(())
        } else {
            let (k, e) = failures
                .into_iter()
                .min_by_key(|(k, _)| *k)
                .expect("non-empty failures");
            Err(classify_error(e, k))
        }
    }

    pub fn thread_count(&self) -> usize {
        self.n_threads
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::arena::monad::{
        intern_e_app, intern_e_const, intern_e_forall_e, intern_e_lam, intern_e_sort,
        intern_l_node, intern_ls_node, intern_name,
    };
    use con_ron_core::arena::pins::{
        intern_reserved_pins, max_nat_size_default, pin_bool_false, pin_empty_levels,
        pin_zero_level,
    };
    use con_ron_core::arena::store::EStore;
    use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
    use con_ron_core::frontend::prepare::{self, PreludeIx};
    use con_ron_core::frontend::prelude::builtin_prelude_e;
    use con_ron_core::kernel::env::ReducibilityHint;
    use con_ron_core::kernel::name;
    use con_ron_core::kernel::pins_decode;
    use con_ron_core::ron::hashmap::Dup;

    fn ok<T, E>(r: Result<T, E>, msg: &str) -> T {
        match r {
            Ok(v) => v,
            Err(_) => panic!("{}", msg),
        }
    }

    fn intern_segments(pers: &PersTier, st: &mut AState, segs: &[&str]) -> NIdx {
        let mut nm = name::anonymous();
        for &s in segs {
            let cp: Vec<u32> = s.chars().map(|c| c as u32).collect();
            nm = name::mk_str(nm, cp);
        }
        ok(intern_name(pers, st, &nm), "intern name")
    }

    enum TestVariant {
        ValidAx(&'static [&'static str]),
        ForgedEqTrueTrue,
        ForgedNonEmptyLevelParams,
        ForgedVerifyAsAxiom,
        ForgedDuplicateAx,
        IllTypedEqLevelTwo,
        IllTypedVerifyArg,
    }

    fn build_bv_test_env(variant: TestVariant) -> LoadedEnvironment {
        let empty_pers = PersTier::empty();
        let mut st = AState::init(EStore::empty());
        ok(intern_reserved_pins(&empty_pers, &mut st), "pins");
        let prelude_ix: PreludeIx = ok(builtin_prelude_e(&empty_pers, &mut st), "prelude");

        let empty_ls = ok(pin_empty_levels(&st), "empty_ls");
        let zero_l = ok(pin_zero_level(&st), "zero_l");
        let one_l = ok(
            intern_l_node(&empty_pers, &mut st, LNodeView::Succ(zero_l.dup2())),
            "one_l",
        );
        let two_l = ok(
            intern_l_node(&empty_pers, &mut st, LNodeView::Succ(one_l.dup2())),
            "two_l",
        );
        let one_ls = ok(
            intern_ls_node(&empty_pers, &mut st, vec![one_l.dup2()]),
            "one_ls",
        );
        let two_ls = ok(
            intern_ls_node(&empty_pers, &mut st, vec![two_l]),
            "two_ls",
        );

        let bool_pin = ok(pin_bool(&st), "bool");
        let true_pin = ok(pin_bool_true(&st), "bool.true");
        let false_pin = ok(pin_bool_false(&st), "bool.false");
        let eq_pin = ok(pin_eq(&st), "eq");

        let bool_e = ok(
            intern_e_const(&empty_pers, &mut st, bool_pin, empty_ls.dup2()),
            "bool_e",
        );
        let true_e = ok(
            intern_e_const(&empty_pers, &mut st, true_pin, empty_ls.dup2()),
            "true_e",
        );
        let false_e = ok(
            intern_e_const(&empty_pers, &mut st, false_pin, empty_ls.dup2()),
            "false_e",
        );

        let verify_name = intern_segments(
            &empty_pers,
            &mut st,
            &["Std", "Tactic", "BVDecide", "Reflect", "verifyBVExpr"],
        );
        let bool_to_bool = ok(
            intern_e_forall_e(&empty_pers, &mut st, bool_e.dup2(), bool_e.dup2()),
            "Bool->Bool",
        );
        let verify_ty = ok(
            intern_e_forall_e(&empty_pers, &mut st, bool_e.dup2(), bool_to_bool),
            "verify_ty",
        );
        let body1 = ok(
            intern_e_lam(&empty_pers, &mut st, bool_e.dup2(), true_e.dup2()),
            "lam1",
        );
        let verify_val = ok(
            intern_e_lam(&empty_pers, &mut st, bool_e.dup2(), body1),
            "lam2",
        );

        let mut user_decls: Vec<IDeclaration> = Vec::new();
        let verify_cv = IConstantVal {
            name: verify_name.dup2(),
            level_params: Vec::new(),
            ty: verify_ty,
        };
        if matches!(variant, TestVariant::ForgedVerifyAsAxiom) {
            user_decls.push(IDeclaration::AxiomDecl(verify_cv));
        } else {
            user_decls.push(IDeclaration::DefnDecl(
                verify_cv,
                verify_val,
                ReducibilityHint::Abbrev,
            ));
        }

        let verify_const = ok(
            intern_e_const(&empty_pers, &mut st, verify_name, empty_ls),
            "verify_const",
        );
        let bad_sort0 = ok(intern_e_sort(&empty_pers, &mut st, zero_l), "Prop");

        let eq_expr = match variant {
            TestVariant::IllTypedEqLevelTwo => {
                ok(intern_e_const(&empty_pers, &mut st, eq_pin, two_ls), "Eq.{2}")
            }
            _ => ok(intern_e_const(&empty_pers, &mut st, eq_pin, one_ls), "Eq.{1}"),
        };
        let eq_bool = ok(intern_e_app(&empty_pers, &mut st, eq_expr, bool_e), "Eq Bool");

        let lhs = match variant {
            TestVariant::ForgedEqTrueTrue => true_e.dup2(),
            TestVariant::IllTypedVerifyArg => {
                let a1 = ok(
                    intern_e_app(&empty_pers, &mut st, verify_const, bad_sort0),
                    "a1",
                );
                ok(intern_e_app(&empty_pers, &mut st, a1, false_e), "a2")
            }
            _ => {
                let a1 = ok(
                    intern_e_app(&empty_pers, &mut st, verify_const, true_e.dup2()),
                    "a1",
                );
                ok(intern_e_app(&empty_pers, &mut st, a1, false_e), "a2")
            }
        };
        let eq_lhs = ok(intern_e_app(&empty_pers, &mut st, eq_bool, lhs), "Eq Bool lhs");
        let eq_ty = ok(
            intern_e_app(&empty_pers, &mut st, eq_lhs, true_e),
            "Eq Bool lhs true",
        );

        let ax_segs: &[&str] = match variant {
            TestVariant::ValidAx(segs) => segs,
            _ => &["Test", "thm", "_native", "bv_decide", "ax_1"],
        };
        let ax_name = intern_segments(&empty_pers, &mut st, ax_segs);
        let level_params = match variant {
            TestVariant::ForgedNonEmptyLevelParams => vec![intern_segments(&empty_pers, &mut st, &["u"])],
            _ => Vec::new(),
        };
        let ax_cv = IConstantVal {
            name: ax_name,
            level_params,
            ty: eq_ty,
        };
        user_decls.push(IDeclaration::AxiomDecl(i_constant_val_dup(&ax_cv)));
        if matches!(variant, TestVariant::ForgedDuplicateAx) {
            user_decls.push(IDeclaration::AxiomDecl(ax_cv));
        }

        let prepared = ok(
            prepare::prepare_d(&empty_pers, &mut st, prelude_ix, user_decls, &DeclUsedConsts),
            "prepare",
        );
        let file_records = prepared.decls.len();
        let pins_decoded = ok(pins_decode::decode_embedded(), "pins_decode");
        let max_nat = max_nat_size_default();
        let ipins = ok(
            checker::intern_all_pins(&empty_pers, &mut st, &pins_decoded, &max_nat),
            "ipins",
        );
        let ix = ok(
            stream_index::build_index(
                &empty_pers,
                &mut st,
                stream_index::stream_index_empty(),
                &prepared.decls,
                0,
            ),
            "build_index",
        );
        let pers = checker::freeze_tier(&mut st.store, ix);

        LoadedEnvironment {
            pers,
            pins: st.pins,
            ipins,
            decls: prepared.decls,
            file_records,
            synthesized: prepared.synthesised,
            hoisted: prepared.hoisted.len(),
            olean: None,
            load_ns: 0,
            materialize_ns: 0,
            index_ns: 0,
            thm_materialized_count: 0,
            closure_fingerprint: None,
            closure_roots: Vec::new(),
            closure_manifest: Vec::new(),
            module_hashes: std::collections::HashMap::new(),
            preverified_prefix: 0,
        }
    }

    #[test]
    fn bv_decide_axiom_declined_strict_and_accepted_when_trusted() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                for segs in [
                    &["Test", "thm", "_native", "bv_decide", "ax_1"][..],
                    &["Test", "thm", "_native", "bv_decide", "ax_1_2"][..],
                ] {
                    let env = build_bv_test_env(TestVariant::ValidAx(segs));
                    let (strict_verdict, _) = verify_host_parallel(&env, Some(2));
                    assert!(
                        matches!(strict_verdict, VerificationVerdict::Declined { .. }),
                        "strict mode must decline bv_decide axiom {:?}, got {:?}",
                        segs,
                        strict_verdict
                    );

                    let trusted = VerifyOptions {
                        trust_bv_decide_axioms: true,
                    };
                    let (trusted_verdict, _) = verify_host_parallel_with(&env, Some(2), trusted);
                    assert!(
                        matches!(trusted_verdict, VerificationVerdict::Accepted { .. }),
                        "trusted mode must accept exact bv_decide axiom {:?}, got {:?}",
                        segs,
                        trusted_verdict
                    );

                    let runner = HostExactRunner::new_with(&env, Some(2), trusted).expect("runner");
                    let all: Vec<usize> = (0..env.decls.len()).collect();
                    let mut batch_opt = Some(all);
                    runner
                        .run_streaming(|| batch_opt.take())
                        .expect("run_streaming trusted");
                }
            })
            .expect("spawn")
            .join()
            .expect("join");
    }

    #[test]
    fn bv_decide_axiom_declines_and_rejects_forged_shapes() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let trusted = VerifyOptions {
                    trust_bv_decide_axioms: true,
                };

                for segs in [
                    &["Evil", "fake_axiom"][..],
                    &["Test", "thm", "_native", "bv_decide", "ax_bad"][..],
                    &["Test", "thm", "_native", "bv_decide", "ax"][..],
                    &["_native", "bv_decide", "ax_1"][..],
                ] {
                    let env = build_bv_test_env(TestVariant::ValidAx(segs));
                    let (verdict, _) = verify_host_parallel_with(&env, Some(2), trusted);
                    assert!(
                        matches!(verdict, VerificationVerdict::Declined { .. }),
                        "forged name {:?} must be declined, got {:?}",
                        segs,
                        verdict
                    );
                }

                for variant in [
                    TestVariant::ForgedEqTrueTrue,
                    TestVariant::ForgedNonEmptyLevelParams,
                    TestVariant::ForgedVerifyAsAxiom,
                ] {
                    let env = build_bv_test_env(variant);
                    let (verdict, _) = verify_host_parallel_with(&env, Some(2), trusted);
                    assert!(
                        matches!(verdict, VerificationVerdict::Declined { .. }),
                        "forged bv_decide axiom must be declined, got {:?}",
                        verdict
                    );
                }

                for variant in [
                    TestVariant::ForgedDuplicateAx,
                    TestVariant::IllTypedEqLevelTwo,
                    TestVariant::IllTypedVerifyArg,
                ] {
                    let env = build_bv_test_env(variant);
                    let (verdict, _) = verify_host_parallel_with(&env, Some(2), trusted);
                    assert!(
                        matches!(verdict, VerificationVerdict::Rejected { .. }),
                        "ill-typed/duplicate forged bv_decide axiom must be rejected, got {:?}",
                        verdict
                    );
                }
            })
            .expect("spawn")
            .join()
            .expect("join");
    }

    #[test]
    fn matching_verified_prefix_len_detects_identical_prefix_and_stops_at_diff() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let env_a = build_bv_test_env(TestVariant::ValidAx(
                    &["Test", "thm", "_native", "bv_decide", "ax_1"],
                ));
                let env_b = build_bv_test_env(TestVariant::ValidAx(
                    &["Test", "thm", "_native", "bv_decide", "ax_1"],
                ));
                assert_eq!(matching_verified_prefix_len(&env_a, &env_b), env_a.decls.len());

                let env_diff = build_bv_test_env(TestVariant::ForgedEqTrueTrue);
                let pref = matching_verified_prefix_len(&env_a, &env_diff);
                assert!(
                    pref < env_a.decls.len() && pref > 0,
                    "prefix must include shared prelude/defn and stop before differing last axiom: pref={pref}, total={}",
                    env_a.decls.len()
                );

                let (verdict, _) = verify_host_range_with(
                    &env_a,
                    pref,
                    Some(2),
                    VerifyOptions {
                        trust_bv_decide_axioms: true,
                    },
                );
                assert!(matches!(verdict, VerificationVerdict::Accepted { .. }));
            })
            .expect("spawn")
            .join()
            .expect("join");
    }
}
