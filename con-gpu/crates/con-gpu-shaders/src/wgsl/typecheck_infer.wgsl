// Guard check on declared type/value (no loose BVar, no FVar, declared lparams, resolved consts).
fn check_level_lparams(l_in: u32) -> u32 {
    if !l_has_param(l_in) { return 1u; }
    // Uses scratch [896..928)
    var sp = 1u;
    s_write(896u, l_in);
    for (var iter = 0u; iter < 512u; iter = iter + 1u) {
        if sp == 0u { return 1u; }
        sp = sp - 1u;
        let cur = s_read(896u + sp);
        if !l_has_param(cur) { continue; }
        let tg = word_tag(cur);
        if tg == LTAG_PARAM {
            let nm = view_l_op0(cur);
            var found = false;
            for (var i = 0u; i < p_job_lp_len; i = i + 1u) {
                if env_nidx_item(p_job_lp_off, i) == nm {
                    found = true;
                    break;
                }
            }
            if !found { return 0u; }
        } else if tg == LTAG_SUCC {
            if sp >= 32u { return 2u; }
            s_write(896u + sp, view_l_op0(cur));
            sp = sp + 1u;
        } else if tg == LTAG_MAX || tg == LTAG_IMAX {
            if sp + 2u > 32u { return 2u; }
            s_write(896u + sp, view_l_op0(cur));
            sp = sp + 1u;
            s_write(896u + sp, view_l_op1(cur));
            sp = sp + 1u;
        }
    }
    return 2u;
}

// Returns 1 = ok, 0 = reject, 2 = delegate (step/stack budget hit in guard DFS)
fn run_decl_guards(root: u32, is_val: bool) -> u32 {
    if e_bvar_b(root) != 0u {
        halt_reject(REASON_LOOSE_BVAR);
        return 0u;
    }
    if e_fvar_b(root) != 0u {
        halt_reject(REASON_FVAR_FREE_ERR);
        return 0u;
    }

    // Direct-mapped 128-entry seen cache at scratch[256..384), dfs[512] at [384..896)
    for (var i = 0u; i < 128u; i = i + 1u) {
        s_write(256u + i, EMPTY_SENTINEL);
    }

    var sp = 1u;
    s_write(384u, root);

    for (var step = 0u; step < 8192u; step = step + 1u) {
        if sp == 0u { return 1u; }
        sp = sp - 1u;
        let cur = s_read(384u + sp);
        let cslot = 256u + (mix_hash32(cur) & 127u);
        if s_read(cslot) == cur {
            continue;
        }
        s_write(cslot, cur);

        let tg = word_tag(cur);
        switch tg {
            case ETAG_BVAR, ETAG_FVAR, ETAG_LIT: {
            }
            case ETAG_SORT: {
                let rc = check_level_lparams(view_sort_u(cur));
                if rc == 0u {
                    halt_reject(REASON_UNDECL_LPARAM);
                    return 0u;
                }
                if rc == 2u { return 2u; }
            }
            case ETAG_CONST: {
                let cn = view_const_n(cur);
                if find_const_visible(cn) == NONE_U32 {
                    halt_unknown_const(cn);
                    return 0u;
                }
                let us = view_const_us(cur);
                if ls_has_param(us) {
                    let ulen = ls_len(us);
                    for (var i = 0u; i < ulen; i = i + 1u) {
                        let rc = check_level_lparams(ls_item(us, i));
                        if rc == 0u {
                            halt_reject(REASON_UNDECL_LPARAM);
                            return 0u;
                        }
                        if rc == 2u { return 2u; }
                    }
                }
            }
            case ETAG_APP, ETAG_LAM, ETAG_FORALL_E: {
                if sp + 2u > 512u { return 2u; }
                if tg == ETAG_APP {
                    s_write(384u + sp, view_app_a(cur));
                    s_write(384u + sp + 1u, view_app_f(cur));
                } else {
                    s_write(384u + sp, view_bind_body(cur));
                    s_write(384u + sp + 1u, view_bind_ty(cur));
                }
                sp = sp + 2u;
            }
            case ETAG_LET_E: {
                if sp + 3u > 512u { return 2u; }
                s_write(384u + sp, view_let_body(cur));
                s_write(384u + sp + 1u, view_let_val(cur));
                s_write(384u + sp + 2u, view_let_ty(cur));
                sp = sp + 3u;
            }
            case ETAG_PROJ: {
                if sp >= 512u { return 2u; }
                s_write(384u + sp, view_proj_e(cur));
                sp = sp + 1u;
            }
            default: { return 2u; }
        }
    }
    let _unused = is_val;
    return 2u;
}

fn check_decl_top_guards(job: GpuJob) -> bool {
    if (job.flags & JOB_FLAG_ELIGIBLE) == 0u {
        halt_delegate(REASON_NOT_ELIGIBLE);
        return false;
    }
    if job.decl_kind != KIND_DEFN && job.decl_kind != KIND_THM && job.decl_kind != KIND_OPAQUE {
        halt_delegate(REASON_NOT_ELIGIBLE);
        return false;
    }
    if job.lparams_len > 64u {
        halt_delegate(REASON_UNMODELED);
        return false;
    }
    if (job.flags & JOB_FLAG_TY_GUARD_OK) == 0u {
        if find_const_visible(job.name) != NONE_U32 {
            halt_reject(REASON_DUP_DECL);
            return false;
        }
        for (var i = 0u; i < job.lparams_len; i = i + 1u) {
            let li = env_nidx_item(job.lparams_off, i);
            for (var j = i + 1u; j < job.lparams_len; j = j + 1u) {
                if li == env_nidx_item(job.lparams_off, j) {
                    halt_reject(REASON_DUP_LPARAM);
                    return false;
                }
            }
        }
        let gr = run_decl_guards(job.ty, false);
        if gr == 0u { return false; }
        if gr == 2u {
            halt_delegate(REASON_UNMODELED);
            return false;
        }
    }
    return true;
}

fn nat_consts_ok() -> bool {
    return find_const_visible(hdr.pin_nat) != NONE_U32
        && find_const_visible(hdr.pin_nat_zero) != NONE_U32
        && find_const_visible(hdr.pin_nat_succ) != NONE_U32;
}

fn bool_consts_ok() -> bool {
    return find_const_visible(hdr.pin_bool) != NONE_U32
        && find_const_visible(hdr.pin_bool_true) != NONE_U32
        && find_const_visible(hdr.pin_bool_false) != NONE_U32;
}

// =========================================================================
// OP_INFER: [2]=e, [3]=depth, [4]=orig_e, [5]=aux0, [6]=aux1, [7]=aux2
// =========================================================================

fn exec_infer(top: u32, io: bool) {
    let phase = f_read(top, 1u);
    let e = f_read(top, 2u);
    let depth = f_read(top, 3u);
    let orig_e = f_read(top, 4u);
    let tg = word_tag(e);
    let infer_op = select(OP_INFER, OP_INFER_IO, io);

    if phase == 0u {
        let cached = lds_infer_get(e);
        if cached != NONE_U32 {
            pop_ret(cached, 0u);
            return;
        }
        switch tg {
            case ETAG_BVAR: {
                halt_reject(REASON_BVAR_INFER);
            }
            case ETAG_FVAR: {
                let ty = view_fvar_ty(e);
                pop_ret(ty, 0u);
            }
            case ETAG_SORT: {
                let u = view_sort_u(e);
                let su = intern_s_l_succ(u);
                if p_halt != 0u { return; }
                let r = intern_s_sort(su);
                if p_halt != 0u { return; }
                if !io { lds_infer_set(orig_e, r); }
                pop_ret(r, 0u);
            }
            case ETAG_LIT: {
                let lk = view_lit_kind(e);
                if lk == 2u {
                    if find_const_visible(hdr.pin_string) == NONE_U32 {
                        halt_reject(REASON_LIT_UNSTORED);
                        return;
                    }
                    let r = intern_s_const(hdr.pin_string, hdr.pin_empty_levels);
                    if p_halt != 0u { return; }
                    if !io { lds_infer_set(orig_e, r); }
                    pop_ret(r, 0u);
                } else {
                    if !p_nat_ok {
                        halt_reject(REASON_LIT_UNSTORED);
                        return;
                    }
                    let r = intern_s_const(hdr.pin_nat, hdr.pin_empty_levels);
                    if p_halt != 0u { return; }
                    if !io { lds_infer_set(orig_e, r); }
                    pop_ret(r, 0u);
                }
            }
            case ETAG_CONST: {
                let cn = view_const_n(e);
                let cus = view_const_us(e);
                let s = find_const_visible(cn);
                if s == NONE_U32 {
                    halt_unknown_const(cn);
                    return;
                }
                let lp_off = const_field(s, 4u);
                let lp_len = const_field(s, 5u);
                if ls_len(cus) != lp_len {
                    halt_reject(REASON_UNDECL_LPARAM);
                    return;
                }
                let cty = const_field(s, 2u);
                req_call(1u, OP_INST_LP, cty, lp_off, lp_len, cus);
                return;
            }
            case ETAG_APP: {
                req_call(2u, infer_op, view_app_f(e), depth, 0u, 0u);
                return;
            }
            case ETAG_LET_E: {
                if io {
                    let vp = s_alloc(1u);
                    if p_halt != 0u { return; }
                    s_write(vp, view_let_val(e));
                    req_call(13u, OP_INST_REV, view_let_body(e), vp, 1u, 0u);
                    return;
                }
                req_call(6u, OP_INFER, view_let_ty(e), depth, 0u, 0u);
                return;
            }
            case ETAG_PROJ: {
                req_call(10u, infer_op, view_proj_e(e), depth, 0u, 0u);
                return;
            }
            case ETAG_LAM, ETAG_FORALL_E: {
                // Count contiguous binder telescope up to 64 binders
                var k = 0u;
                var w = e;
                for (var i = 0u; i < 64u; i = i + 1u) {
                    if word_tag(w) != tg { break; }
                    w = view_bind_body(w);
                    k = k + 1u;
                }
                // Allocate [fvs(k), aux(k), binders(k), cur_idx, leaf_body] = 3*k + 2
                let blk = s_alloc(k * 3u + 2u);
                if p_halt != 0u { return; }
                w = e;
                for (var i = 0u; i < k; i = i + 1u) {
                    s_write(blk + 2u * k + i, view_bind_ty(w));
                    w = view_bind_body(w);
                }
                s_write(blk + 3u * k, 0u); // cur index i
                s_write(blk + 3u * k + 1u, w); // leaf body
                f_write(top, 5u, blk);
                f_write(top, 6u, k);
                f_write(top, 1u, 14u);
                return;
            }
            default: { halt_delegate(REASON_UNMODELED); }
        }
        return;
    }

    if phase == 1u {
        // CONST ty instantiated
        if !io { lds_infer_set(orig_e, p_res0); }
        pop_ret(p_res0, 0u);
        return;
    }

    // APP: [phase 2=f_ty, 3=whnf(f_ty), 4=arg_ty, 5=defeq(arg_ty, dom), 5b=inst1(body, arg)]
    if phase == 2u {
        req_call(3u, OP_WHNF, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 3u {
        let wf = p_res0;
        if word_tag(wf) != ETAG_FORALL_E {
            halt_reject(REASON_APP_NOT_FORALL);
            return;
        }
        if io {
            let body = view_bind_body(wf);
            let vp = s_alloc(1u);
            if p_halt != 0u { return; }
            s_write(vp, view_app_a(e));
            req_call(1u, OP_INST_REV, body, vp, 1u, 0u);
            return;
        }
        f_write(top, 5u, wf);
        req_call(4u, OP_INFER, view_app_a(e), depth, 0u, 0u);
        return;
    }
    if phase == 4u {
        let wf = f_read(top, 5u);
        let dom = view_bind_ty(wf);
        let arg_ty = p_res0;
        req_call(5u, OP_DEFEQ, arg_ty, dom, depth, 0u);
        return;
    }
    if phase == 5u {
        if p_res0 == 0u {
            halt_reject(REASON_ARG_MISMATCH);
            return;
        }
        let wf = f_read(top, 5u);
        let body = view_bind_body(wf);
        let vp = s_alloc(1u);
        if p_halt != 0u { return; }
        s_write(vp, view_app_a(e));
        req_call(1u, OP_INST_REV, body, vp, 1u, 0u); // reuse phase 1 cache+pop
        return;
    }

    // LET_E: [phase 6=tty, 7=whnf(tty), 8=val_ty, 9=defeq(val_ty, ty)]
    if phase == 6u {
        req_call(7u, OP_WHNF, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 7u {
        if word_tag(p_res0) != ETAG_SORT {
            halt_reject(REASON_NOT_SORT);
            return;
        }
        req_call(8u, OP_INFER, view_let_val(e), depth, 0u, 0u);
        return;
    }
    if phase == 8u {
        req_call(9u, OP_DEFEQ, p_res0, view_let_ty(e), depth, 0u);
        return;
    }
    if phase == 9u {
        if p_res0 == 0u {
            halt_reject(REASON_TYPE_MISMATCH);
            return;
        }
        let vp = s_alloc(1u);
        if p_halt != 0u { return; }
        s_write(vp, view_let_val(e));
        req_call(13u, OP_INST_REV, view_let_body(e), vp, 1u, 0u);
        return;
    }
    if phase == 13u {
        // Infer body[val] and return as orig_e type
        req_call(1u, infer_op, p_res0, depth, 0u, 0u);
        return;
    }

    // PROJ: [10=tp, 11=whnf(tp), 110=guard infer(tp_w), 111=guard whnf, 12=inst_lp, 121=inst_rev]
    if phase == 10u {
        req_call(11u, OP_WHNF, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 11u {
        let tp_w = p_res0;
        let sn = view_proj_sn(e);
        let idx_lo = view_proj_idx_lo(e);
        let idx_hi = view_proj_idx_hi(e);
        let p_slot = find_proj_visible(sn);
        if p_slot == NONE_U32 || idx_hi != 0u {
            halt_reject(REASON_PROJ_ERR);
            return;
        }
        let num_params = proj_field(p_slot, 2u);
        let num_fields = proj_field(p_slot, 4u);
        let tbl_lp_len = proj_field(p_slot, 8u);

        var pargc = 0u;
        var phd = tp_w;
        for (var i = 0u; i < 256u; i = i + 1u) {
            if word_tag(phd) != ETAG_APP { break; }
            phd = view_app_f(phd);
            pargc = pargc + 1u;
        }
        if word_tag(phd) != ETAG_CONST || view_const_n(phd) != sn {
            halt_reject(REASON_PROJ_ERR);
            return;
        }
        let pus = view_const_us(phd);
        if idx_lo >= num_fields || pargc != num_params || ls_len(pus) != tbl_lp_len {
            halt_reject(REASON_PROJ_ERR);
            return;
        }
        // Build aux block: [tp_w, p_slot, pus, args...(num_params + 1)]
        let aux = s_alloc(3u + num_params + 1u);
        if p_halt != 0u { return; }
        s_write(aux, tp_w);
        s_write(aux + 1u, p_slot);
        s_write(aux + 2u, pus);
        var w = tp_w;
        for (var j = 0u; j < num_params; j = j + 1u) {
            s_write(aux + 3u + (num_params - 1u - j), view_app_a(w));
            w = view_app_f(w);
        }
        s_write(aux + 3u + num_params, view_proj_e(e));
        f_write(top, 5u, aux);

        let ind_slot = find_const_visible(sn);
        if ind_slot == NONE_U32 || const_field(ind_slot, 0u) != CKIND_IND {
            halt_reject(REASON_PROJ_ERR);
            return;
        }
        if (const_field(ind_slot, 8u) & 2u) == 0u {
            // Possibly Prop: check sort of tp_w
            req_call(110u, infer_op, tp_w, depth, 0u, 0u);
            return;
        }
        f_write(top, 1u, 12u);
        return;
    }
    if phase == 110u {
        req_call(111u, OP_WHNF, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 111u {
        if word_tag(p_res0) != ETAG_SORT || !level_is_nonzero(view_sort_u(p_res0)) {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        f_write(top, 1u, 12u);
        return;
    }
    if phase == 12u {
        let aux = f_read(top, 5u);
        let p_slot = s_read(aux + 1u);
        let pus = s_read(aux + 2u);
        let b_off = proj_field(p_slot, 5u);
        let lp_off = proj_field(p_slot, 7u);
        let lp_len = proj_field(p_slot, 8u);
        let body = env_eidx_item(b_off, view_proj_idx_lo(e));
        req_call(121u, OP_INST_LP, body, lp_off, lp_len, pus);
        return;
    }
    if phase == 121u {
        let aux = f_read(top, 5u);
        let p_slot = s_read(aux + 1u);
        let num_params = proj_field(p_slot, 2u);
        req_call(1u, OP_INST_REV, p_res0, aux + 3u, num_params + 1u, 0u);
        return;
    }

    // Shared LAM / FORALL_E telescope phases 14..21
    if phase == 14u {
        let blk = f_read(top, 5u);
        let k = f_read(top, 6u);
        let i = s_read(blk + 3u * k);
        if i < k {
            let raw_ty = s_read(blk + 2u * k + i);
            req_call(15u, OP_INST_REV, raw_ty, blk, i, 0u);
            return;
        }
        // All k binders opened: inst_rev leaf body with fvs[0..k)
        let leaf = s_read(blk + 3u * k + 1u);
        req_call(18u, OP_INST_REV, leaf, blk, k, 0u);
        return;
    }
    if phase == 15u {
        let blk = f_read(top, 5u);
        let k = f_read(top, 6u);
        let i = s_read(blk + 3u * k);
        let tyo = p_res0;
        let fv = intern_s_fvar(depth + i, 0u, tyo);
        if p_halt != 0u { return; }
        s_write(blk + i, fv);
        s_write(blk + k + i, tyo);
        if io && tg == ETAG_LAM {
            s_write(blk + 3u * k, i + 1u);
            f_write(top, 1u, 14u);
            return;
        }
        req_call(16u, infer_op, tyo, depth + i, 0u, 0u);
        return;
    }
    if phase == 16u {
        let blk = f_read(top, 5u);
        let k = f_read(top, 6u);
        let i = s_read(blk + 3u * k);
        req_call(17u, OP_WHNF, p_res0, depth + i, 0u, 0u);
        return;
    }
    if phase == 17u {
        if word_tag(p_res0) != ETAG_SORT {
            halt_reject(REASON_NOT_SORT);
            return;
        }
        let blk = f_read(top, 5u);
        let k = f_read(top, 6u);
        let i = s_read(blk + 3u * k);
        if tg == ETAG_FORALL_E {
            s_write(blk + k + i, view_sort_u(p_res0));
        }
        s_write(blk + 3u * k, i + 1u);
        f_write(top, 1u, 14u);
        return;
    }
    if phase == 18u {
        let k = f_read(top, 6u);
        req_call(19u, infer_op, p_res0, depth + k, 0u, 0u);
        return;
    }
    if phase == 19u {
        let k = f_read(top, 6u);
        if tg == ETAG_FORALL_E {
            req_call(20u, OP_WHNF, p_res0, depth + k, 0u, 0u);
        } else {
            req_call(20u, OP_ABS_RANGE, p_res0, depth, k, 0u);
        }
        return;
    }
    if phase == 20u {
        let blk = f_read(top, 5u);
        let k = f_read(top, 6u);
        if tg == ETAG_FORALL_E {
            if word_tag(p_res0) != ETAG_SORT {
                halt_reject(REASON_NOT_SORT);
                return;
            }
            var v = view_sort_u(p_res0);
            for (var j = 0u; j < k; j = j + 1u) {
                let idx = k - 1u - j;
                v = level_mk_imax_simp(s_read(blk + k + idx), v);
                if p_halt != 0u { return; }
            }
            let out = intern_s_sort(v);
            if p_halt != 0u { return; }
            if !io { lds_infer_set(orig_e, out); }
            pop_ret(out, 0u);
            return;
        }
        f_write(top, 7u, p_res0); // cur
        s_write(blk + 3u * k, k); // remaining j countdown from k
        f_write(top, 1u, 21u);
        return;
    }
    if phase == 21u {
        let blk = f_read(top, 5u);
        let k = f_read(top, 6u);
        let rem = s_read(blk + 3u * k);
        let cur = f_read(top, 7u);
        if rem == 0u {
            if !io { lds_infer_set(orig_e, cur); }
            pop_ret(cur, 0u);
            return;
        }
        let j = rem - 1u;
        s_write(blk + 3u * k, j);
        req_call(211u, OP_ABS_RANGE, s_read(blk + k + j), depth, j, 0u);
        return;
    }
    // phase == 211u
    let cur = f_read(top, 7u);
    let wrapped = intern_s_bind(ETAG_FORALL_E, p_res0, cur);
    if p_halt != 0u { return; }
    f_write(top, 7u, wrapped);
    f_write(top, 1u, 21u);
}

// OP_JOB_FINISH: orchestrate check_constant_val + check_defn/thm/opaque
// Phases:
//   0: start infer(job.ty)
//   1: whnf(infer(job.ty))
//   2: check Sort(u), Thm Prop check, run_decl_guards(job.val), infer(job.val)
//   3: is_def_eq(val_ty, job.ty)
fn exec_job_finish(top: u32) {
    let phase = f_read(top, 1u);

    if phase == 0u {
        req_call(1u, OP_INFER, p_job_ty, 0u, 0u, 0u);
        return;
    }
    if phase == 1u {
        req_call(2u, OP_WHNF, p_res0, 0u, 0u, 0u);
        return;
    }
    if phase == 2u {
        if word_tag(p_res0) != ETAG_SORT {
            halt_reject(REASON_NOT_SORT);
            return;
        }
        if p_decl_kind == KIND_THM {
            req_raw(25u, OP_LEVEL_CMP, 0u, view_sort_u(p_res0), hdr.pin_zero_level, 0u, 0u);
            return;
        }
        f_write(top, 1u, 26u);
        return;
    }
    if phase == 25u {
        if p_res0 == 0u {
            halt_reject(REASON_THM_NOT_PROP);
            return;
        }
        f_write(top, 1u, 26u);
        return;
    }
    if phase == 26u {
        // Check value guards on job.val unless pre-certified by B.1 DAG summary
        if (p_job_flags & JOB_FLAG_VAL_GUARD_OK) == 0u {
            let gr = run_decl_guards(p_job_val, true);
            if gr == 0u { return; }
            if gr == 2u {
                halt_delegate(REASON_UNMODELED);
                return;
            }
        }
        if p_subst_gen == 0xFFFFFFFFu {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        p_subst_gen = p_subst_gen + 1u;
        req_call(3u, OP_INFER, p_job_val, 0u, 0u, 0u);
        return;
    }
    if phase == 3u {
        req_call(4u, OP_DEFEQ, p_res0, p_job_ty, 0u, 0u);
        return;
    }
    if phase == 4u {
        if p_res0 == 1u {
            p_status = STATUS_VERIFIED_GPU;
            p_reason = REASON_OK;
        } else {
            p_status = STATUS_REJECTED_GPU;
            p_reason = REASON_TYPE_MISMATCH;
        }
        p_halt = 1u;
    }
}

