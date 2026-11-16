// =========================================================================
// OP_DEFEQ_* helpers and main OP_DEFEQ
// =========================================================================

fn exec_defeq_bind_chain(top: u32, target_tag: u32) {
    // [2]=a, [3]=b, [4]=depth, [5]=blk ([fvs(k), tys_a(k), tys_b(k), leaf_a, leaf_b, i]), [6]=k
    let phase = f_read(top, 1u);
    let a = f_read(top, 2u);
    let b = f_read(top, 3u);
    let depth = f_read(top, 4u);

    if phase == 0u {
        var k = 0u;
        var wa = a;
        var wb = b;
        for (var i = 0u; i < 64u; i = i + 1u) {
            if word_tag(wa) != target_tag || word_tag(wb) != target_tag { break; }
            wa = view_bind_body(wa);
            wb = view_bind_body(wb);
            k = k + 1u;
        }
        let blk = s_alloc(k * 3u + 3u);
        if p_halt != 0u { return; }
        wa = a;
        wb = b;
        for (var i = 0u; i < k; i = i + 1u) {
            s_write(blk + k + i, view_bind_ty(wa));
            s_write(blk + 2u * k + i, view_bind_ty(wb));
            wa = view_bind_body(wa);
            wb = view_bind_body(wb);
        }
        s_write(blk + 3u * k, wa);
        s_write(blk + 3u * k + 1u, wb);
        s_write(blk + 3u * k + 2u, 0u);
        f_write(top, 5u, blk);
        f_write(top, 6u, k);
        f_write(top, 1u, 1u);
        return;
    }

    let blk = f_read(top, 5u);
    let k = f_read(top, 6u);
    let i = s_read(blk + 3u * k + 2u);

    if phase == 1u {
        if i < k {
            req_call(2u, OP_INST_REV, s_read(blk + k + i), blk, i, 0u);
            return;
        }
        req_call(5u, OP_INST_REV, s_read(blk + 3u * k), blk, k, 0u);
        return;
    }
    if phase == 2u {
        f_write(top, 7u, p_res0);
        req_call(3u, OP_INST_REV, s_read(blk + 2u * k + i), blk, i, 0u);
        return;
    }
    if phase == 3u {
        let tya_i = f_read(top, 7u);
        let tyb_i = p_res0;
        let fv = intern_s_fvar(depth + i, 0u, tya_i);
        if p_halt != 0u { return; }
        s_write(blk + i, fv);
        let check_dom = (target_tag == ETAG_FORALL_E) || (hdr.verified_mode != 0u);
        if check_dom && tya_i != tyb_i {
            req_call(4u, OP_DEFEQ, tya_i, tyb_i, depth + i, 0u);
            return;
        }
        s_write(blk + 3u * k + 2u, i + 1u);
        f_write(top, 1u, 1u);
        return;
    }
    if phase == 4u {
        if p_res0 == 0u {
            pop_ret(0u, 0u);
            return;
        }
        s_write(blk + 3u * k + 2u, i + 1u);
        f_write(top, 1u, 1u);
        return;
    }
    if phase == 5u {
        f_write(top, 7u, p_res0);
        req_call(6u, OP_INST_REV, s_read(blk + 3u * k + 1u), blk, k, 0u);
        return;
    }
    if phase == 6u {
        let la = f_read(top, 7u);
        let lb = p_res0;
        req_call(7u, OP_DEFEQ, la, lb, depth + k, 0u);
        return;
    }
    pop_ret(p_res0, 0u);
}

fn exec_defeq_spine(top: u32) {
    // Compare head and args of a and b ([2]=a, [3]=b, [4]=depth, [5]=blk, [6]=argc, [7]=idx)
    let phase = f_read(top, 1u);
    let a = f_read(top, 2u);
    let b = f_read(top, 3u);
    let depth = f_read(top, 4u);

    if phase == 0u {
        var ac = 0u;
        var ha = a;
        for (var i = 0u; i < 256u; i = i + 1u) {
            if word_tag(ha) != ETAG_APP { break; }
            ha = view_app_f(ha);
            ac = ac + 1u;
        }
        var bc = 0u;
        var hb = b;
        for (var i = 0u; i < 256u; i = i + 1u) {
            if word_tag(hb) != ETAG_APP { break; }
            hb = view_app_f(hb);
            bc = bc + 1u;
        }
        if word_tag(ha) == ETAG_APP || word_tag(hb) == ETAG_APP {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        if ac != bc {
            pop_ret(0u, 0u);
            return;
        }
        let blk = s_alloc(ac * 2u);
        if p_halt != 0u { return; }
        var wa = a;
        var wb = b;
        for (var i = 0u; i < ac; i = i + 1u) {
            let slot = ac - 1u - i;
            s_write(blk + slot, view_app_a(wa));
            s_write(blk + ac + slot, view_app_a(wb));
            wa = view_app_f(wa);
            wb = view_app_f(wb);
        }
        f_write(top, 5u, blk);
        f_write(top, 6u, ac);
        f_write(top, 7u, 0u);
        f_write(top, 1u, 1u);
        // Check head equality first
        if ha == hb {
            p_res0 = 1u;
            return;
        }
        if word_tag(ha) == ETAG_CONST && word_tag(hb) == ETAG_CONST {
            if view_const_n(ha) != view_const_n(hb) {
                p_res0 = 0u;
                return;
            }
            req_raw(1u, OP_LEVEL_CMP, 1u, view_const_us(ha), view_const_us(hb), 0u, 0u);
            return;
        }
        req_call(1u, OP_DEFEQ, ha, hb, depth, 0u);
        return;
    }

    if p_res0 == 0u {
        pop_ret(0u, 0u);
        return;
    }
    let idx = f_read(top, 7u);
    let argc = f_read(top, 6u);
    if idx >= argc {
        pop_ret(1u, 0u);
        return;
    }
    let blk = f_read(top, 5u);
    let arg_a = s_read(blk + idx);
    let arg_b = s_read(blk + argc + idx);
    f_write(top, 7u, idx + 1u);
    req_call(1u, OP_DEFEQ, arg_a, arg_b, depth, 0u);
}

fn exec_defeq_struct_eta(top: u32) {
    // [2]=a, [3]=b, [4]=depth, [5]=aux0 (sn), [6]=num_fields, [7]=field_idx
    let phase = f_read(top, 1u);
    let a = f_read(top, 2u);
    let b = f_read(top, 3u);
    let depth = f_read(top, 4u);

    if phase == 0u {
        req_call(1u, OP_INFER_IO, a, depth, 0u, 0u);
        return;
    }
    if phase == 1u {
        f_write(top, 5u, p_res0); // ta
        req_call(2u, OP_WHNF, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 2u {
        let ta_w = p_res0;
        let hd = extract_spine_head(ta_w);
        if word_tag(hd) != ETAG_CONST {
            if word_tag(ta_w) == ETAG_FORALL_E {
                halt_delegate(REASON_UNMODELED);
                return;
            }
            pop_ret(0u, 0u);
            return;
        }
        let sn = view_const_n(hd);
        let cslot = find_const_visible(sn);
        if cslot == NONE_U32 || const_field(cslot, 0u) != CKIND_IND || (const_field(cslot, 8u) & 1u) == 0u {
            pop_ret(0u, 0u);
            return;
        }
        var num_fields = 0u;
        let p_slot = find_proj_visible(sn);
        if p_slot != NONE_U32 {
            num_fields = proj_field(p_slot, 4u);
        } else {
            let n_ctors = const_field(cslot, 12u);
            if n_ctors != 1u {
                halt_delegate(REASON_UNMODELED);
                return;
            }
            let ctor_n = env_nidx_item(const_field(cslot, 11u), 0u);
            let ctor_s = find_const_visible(ctor_n);
            if ctor_s == NONE_U32 || const_field(ctor_s, 0u) != CKIND_CTOR || const_field(ctor_s, 10u) != 0u {
                halt_delegate(REASON_UNMODELED);
                return;
            }
            num_fields = 0u;
        }
        f_write(top, 6u, num_fields); // num_fields
        f_write(top, 7u, sn);
        // Check is_prop(ta): infer(ta) -> whnf
        req_call(3u, OP_INFER, f_read(top, 5u), depth, 0u, 0u);
        return;
    }
    if phase == 3u {
        req_call(4u, OP_WHNF, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 4u {
        if word_tag(p_res0) == ETAG_SORT && level_is_zero(view_sort_u(p_res0)) {
            pop_ret(0u, 0u);
            return;
        }
        req_call(5u, OP_INFER, b, depth, 0u, 0u);
        return;
    }
    if phase == 5u {
        req_call(6u, OP_DEFEQ, f_read(top, 5u), p_res0, depth, 0u);
        return;
    }
    if phase == 6u {
        if p_res0 == 0u {
            pop_ret(0u, 0u);
            return;
        }
        f_write(top, 5u, 0u); // field loop index
        f_write(top, 1u, 7u);
        return;
    }
    // phase == 7u or 8u: loop fields [0..num_fields)
    if phase == 8u {
        if p_res0 == 0u {
            pop_ret(0u, 0u);
            return;
        }
    }
    let idx = f_read(top, 5u);
    let nf = f_read(top, 6u);
    if idx >= nf {
        pop_ret(1u, 0u);
        return;
    }
    let sn = f_read(top, 7u);
    f_write(top, 5u, idx + 1u);
    let pa = intern_s_proj(sn, idx, 0u, a);
    let pb = intern_s_proj(sn, idx, 0u, b);
    if p_halt != 0u { return; }
    req_call(8u, OP_DEFEQ, pa, pb, depth, 0u);
}

fn head_is_proj(e: u32) -> bool {
    return word_tag(extract_spine_head(e)) == ETAG_PROJ;
}

fn is_nat_op_app(e: u32) -> bool {
    if word_tag(e) != ETAG_APP || !p_nat_ok { return false; }
    let f1 = view_app_f(e);
    if word_tag(f1) == ETAG_CONST {
        return view_const_n(f1) == hdr.pin_nat_succ && ls_len(view_const_us(f1)) == 0u;
    }
    if word_tag(f1) == ETAG_APP {
        let g1 = view_app_f(f1);
        if word_tag(g1) == ETAG_CONST {
            let cn = view_const_n(g1);
            if cn == hdr.pin_nat_pred || ls_len(view_const_us(g1)) != 0u { return false; }
            let cs = find_const_visible(cn);
            return cs != NONE_U32
                && ((const_field(cs, 14u) & 1u) != 0u
                    || (hdr.pin_nat_pow != 0u && cn == hdr.pin_nat_pow)
                    || (hdr.pin_nat_gcd != 0u && cn == hdr.pin_nat_gcd));
        }
    }
    return false;
}

fn definitely_not_proof(e_in: u32) -> bool {
    var cur = e_in;
    for (var i = 0u; i < 16u; i = i + 1u) {
        let tg = word_tag(cur);
        if tg == ETAG_LAM { cur = view_bind_body(cur); }
        else if tg == ETAG_LET_E { cur = view_let_body(cur); }
        else if tg == ETAG_APP { cur = view_app_f(cur); }
        else { break; }
    }
    let tg = word_tag(cur);
    if tg == ETAG_SORT || tg == ETAG_FORALL_E || tg == ETAG_LIT {
        return true;
    }
    if tg == ETAG_CONST {
        let cs = find_const_visible(view_const_n(cur));
        if cs != NONE_U32 {
            var ty = const_field(cs, 2u);
            for (var j = 0u; j < 32u; j = j + 1u) {
                if word_tag(ty) != ETAG_FORALL_E { break; }
                ty = view_bind_body(ty);
            }
            if word_tag(ty) == ETAG_SORT {
                return true;
            }
        }
    }
    return false;
}

// Main OP_DEFEQ:
// [2]=a, [3]=b, [4]=depth, [5]=a_cur, [6]=b_cur, [7]=aux (delta step count + flags)
fn exec_defeq(top: u32) {
    let phase = f_read(top, 1u);
    let a = f_read(top, 2u);
    let b = f_read(top, 3u);
    let depth = f_read(top, 4u);

    if phase == 0u {
        if a == b { pop_ret(1u, 0u); return; }
        let d_cached = defeq_memo_get(a, b, depth);
        if d_cached != NONE_U32 {
            pop_ret(d_cached, 0u);
            return;
        }
        let ta = word_tag(a);
        let tb = word_tag(b);
        if ta == ETAG_SORT && tb == ETAG_SORT {
            req_raw(4u, OP_LEVEL_CMP, 0u, view_sort_u(a), view_sort_u(b), 0u, 0u);
            return;
        }
        if ta == ETAG_LIT && tb == ETAG_LIT {
            pop_ret(select(0u, 1u, lit_eq(a, b)), 0u);
            return;
        }
        if ta == ETAG_FORALL_E && tb == ETAG_FORALL_E {
            req_raw(4u, OP_DEFEQ_FORALL_CHAIN, 0u, a, b, depth, 0u);
            return;
        }
        if ta == ETAG_LAM && tb == ETAG_LAM {
            req_raw(4u, OP_DEFEQ_LAM_CHAIN, 0u, a, b, depth, 0u);
            return;
        }
        if definitely_not_proof(a) || definitely_not_proof(b) {
            req_call(5u, OP_WHNF_CORE, a, depth, 1u, 0u);
            return;
        }
        // Check proof irrelevance for remaining pairs via infer_only
        req_call(1u, OP_INFER_IO, a, depth, 0u, 0u);
        return;
    }

    if phase == 1u {
        // p_res0 = infer_io(a)
        f_write(top, 5u, p_res0); // save ta
        req_call(2u, OP_INFER_IO, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 2u {
        if word_tag(p_res0) == ETAG_SORT {
            if level_is_zero(view_sort_u(p_res0)) {
                req_call(31u, OP_INFER_IO, b, depth, 0u, 0u);
            } else {
                req_call(5u, OP_WHNF_CORE, a, depth, 1u, 0u);
            }
            return;
        }
        req_call(3u, OP_WHNF, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 3u {
        // Check if whnf(infer_io(ta)) == Sort(0)
        if word_tag(p_res0) == ETAG_SORT && level_is_zero(view_sort_u(p_res0)) {
            req_call(31u, OP_INFER_IO, b, depth, 0u, 0u);
            return;
        }
        // Reduce both a and b with cheap whnf_core
        req_call(5u, OP_WHNF_CORE, a, depth, 1u, 0u);
        return;
    }
    if phase == 31u {
        // Proof irrel: compare ta vs tb
        req_call(4u, OP_DEFEQ, f_read(top, 5u), p_res0, depth, 0u);
        return;
    }
    if phase == 4u {
        pop_ret(p_res0, 0u);
        return;
    }
    if phase == 5u {
        f_write(top, 5u, p_res0); // a1
        req_call(6u, OP_WHNF_CORE, b, depth, 1u, 0u);
        return;
    }
    if phase == 6u {
        f_write(top, 6u, p_res0); // b1
        f_write(top, 7u, 0u); // delta iter count
        f_write(top, 1u, 10u);
        return;
    }

    // Lazy Delta Loop (phases 10..15)
    if phase == 10u {
        let a1 = f_read(top, 5u);
        let b1 = f_read(top, 6u);
        if a1 == b1 { pop_ret(1u, 0u); return; }
        let ta1 = word_tag(a1);
        let tb1 = word_tag(b1);
        if ta1 == ETAG_SORT && tb1 == ETAG_SORT {
            req_raw(4u, OP_LEVEL_CMP, 0u, view_sort_u(a1), view_sort_u(b1), 0u, 0u);
            return;
        }
        if ta1 == ETAG_LAM && tb1 == ETAG_LAM {
            req_raw(4u, OP_DEFEQ_LAM_CHAIN, 0u, a1, b1, depth, 0u);
            return;
        }
        if ta1 == ETAG_FORALL_E && tb1 == ETAG_FORALL_E {
            req_raw(4u, OP_DEFEQ_FORALL_CHAIN, 0u, a1, b1, depth, 0u);
            return;
        }

        let aux = f_read(top, 7u);
        if (aux & 0x40000u) == 0u && e_is_fvar_free(a1) && e_is_fvar_free(b1) && is_nat_op_app(a1) {
            f_write(top, 7u, aux | 0x40000u);
            req_raw(101u, OP_WHNF, 0u, a1, depth | 0x80000000u, a1, 0u);
            return;
        }
        if (aux & 0x80000u) == 0u && e_is_fvar_free(a1) && e_is_fvar_free(b1) && is_nat_op_app(b1) {
            f_write(top, 7u, aux | 0x80000u);
            req_raw(102u, OP_WHNF, 0u, b1, depth | 0x80000000u, b1, 0u);
            return;
        }

        let dcnt = aux & 0xFFFFu;
        let nat_flags = aux & 0xC0000u;
        if dcnt > 512u {
            halt_delegate(REASON_STEP_BUDGET);
            return;
        }
        let next_cnt = dcnt + 1u;

        let sa = head_const_slot(a1);
        let sb = head_const_slot(b1);
        if sa == NONE_U32 && sb == NONE_U32 {
            f_write(top, 1u, 20u);
            return;
        }
        if sa != NONE_U32 && sb == NONE_U32 {
            f_write(top, 7u, nat_flags | next_cnt);
            f_write(top, 1u, 11u);
            return;
        }
        if sa == NONE_U32 && sb != NONE_U32 {
            f_write(top, 7u, nat_flags | next_cnt | (1u << 16u));
            f_write(top, 1u, 11u);
            return;
        }
        let ha_k = const_field(sa, 6u);
        let ha_h = const_field(sa, 7u);
        let hb_k = const_field(sb, 6u);
        let hb_h = const_field(sb, 7u);
        if hint_lt(hb_k, hb_h, ha_k, ha_h) {
            f_write(top, 7u, nat_flags | next_cnt);
            f_write(top, 1u, 11u);
            return;
        }
        if hint_lt(ha_k, ha_h, hb_k, hb_h) {
            f_write(top, 7u, nat_flags | next_cnt | (1u << 16u));
            f_write(top, 1u, 11u);
            return;
        }
        if ha_k == hb_k && ha_h == hb_h && sa == sb {
            f_write(top, 7u, nat_flags | next_cnt);
            req_raw(13u, OP_DEFEQ_SPINE, 0u, a1, b1, depth, 0u);
            return;
        }
        f_write(top, 7u, nat_flags | next_cnt | (2u << 16u));
        f_write(top, 1u, 11u);
        return;
    }

    if phase == 101u {
        if p_res0 != NONE_U32 {
            f_write(top, 5u, p_res0);
            f_write(top, 7u, f_read(top, 7u) & ~0x40000u);
        }
        f_write(top, 1u, 10u);
        return;
    }
    if phase == 102u {
        if p_res0 != NONE_U32 {
            f_write(top, 6u, p_res0);
            f_write(top, 7u, f_read(top, 7u) & ~0x80000u);
        }
        f_write(top, 1u, 10u);
        return;
    }

    if phase == 11u || phase == 111u || phase == 112u {
        let aux = f_read(top, 7u);
        let umode = (aux >> 16u) & 3u;
        let is_b = umode == 1u;
        let slot_f = select(5u, 6u, is_b);
        if phase == 11u {
            let term = f_read(top, slot_f);
            let sc = head_const_slot(term);
            var argc = 0u;
            var hd = term;
            for (var i = 0u; i < 256u; i = i + 1u) {
                if word_tag(hd) != ETAG_APP { break; }
                hd = view_app_f(hd);
                argc = argc + 1u;
            }
            if word_tag(hd) == ETAG_APP { halt_delegate(REASON_UNMODELED); return; }
            let ap = s_alloc(argc + 1u);
            if p_halt != 0u { return; }
            var w = term;
            for (var i = 0u; i < argc; i = i + 1u) {
                s_write(ap + 1u + (argc - 1u - i), view_app_a(w));
                w = view_app_f(w);
            }
            s_write(ap, argc);
            f_write(top, slot_f, ap);
            req_call(111u, OP_INST_LP, const_field(sc, 3u), const_field(sc, 4u), const_field(sc, 5u), view_const_us(hd));
            return;
        }
        if phase == 111u {
            let ap = f_read(top, slot_f);
            let argc = s_read(ap);
            let un = mk_app_slice(p_res0, ap + 1u, 0u, argc);
            if p_halt != 0u { return; }
            req_call(112u, OP_WHNF_CORE, un, depth, 1u, 0u);
            return;
        }
        // phase == 112u
        f_write(top, slot_f, p_res0);
        let keep_nat = aux & select(~0x40000u, ~0x80000u, is_b) & 0xC0000u;
        if umode == 2u {
            f_write(top, 7u, keep_nat | (aux & 0xFFFFu) | (1u << 16u));
            f_write(top, 1u, 11u);
        } else {
            f_write(top, 7u, keep_nat | (aux & 0xFFFFu));
            f_write(top, 1u, 10u);
        }
        return;
    }

    if phase == 13u {
        if p_res0 != 0u {
            pop_ret(1u, 0u);
            return;
        }
        let aux = f_read(top, 7u);
        f_write(top, 7u, (aux & 0xC0000u) | (aux & 0xFFFFu) | (2u << 16u));
        f_write(top, 1u, 11u);
        return;
    }

    // Stuck Checks (phases 20..29)
    let a2 = f_read(top, 5u);
    let b2 = f_read(top, 6u);
    let ta2 = word_tag(a2);
    let tb2 = word_tag(b2);

    if phase == 20u {
        if a2 == b2 { pop_ret(1u, 0u); return; }
        // Non-cheap whnf_core projection rescue if either side has ETAG_PROJ head
        if head_is_proj(a2) || head_is_proj(b2) {
            f_write(top, 7u, f_read(top, 7u) & ~0x100000u);
            req_call(201u, OP_WHNF_CORE, a2, depth, 0u, 0u);
            return;
        }
        f_write(top, 1u, 21u);
        return;
    }
    if phase == 201u {
        let a3 = p_res0;
        if a3 != a2 {
            f_write(top, 5u, a3);
            f_write(top, 7u, (f_read(top, 7u) & ~0x40000u) | 0x100000u);
        }
        req_call(202u, OP_WHNF_CORE, b2, depth, 0u, 0u);
        return;
    }
    if phase == 202u {
        let b3 = p_res0;
        var aux = f_read(top, 7u);
        if b3 != b2 {
            f_write(top, 6u, b3);
            aux = (aux & ~0x80000u) | 0x100000u;
            f_write(top, 7u, aux);
        }
        if (aux & 0x100000u) != 0u {
            f_write(top, 1u, 10u);
        } else {
            f_write(top, 1u, 21u);
        }
        return;
    }

    if phase == 21u {
        if a2 == b2 { pop_ret(1u, 0u); return; }
        if ta2 == ETAG_LIT && tb2 == ETAG_LIT {
            pop_ret(select(0u, 1u, lit_eq(a2, b2)), 0u);
            return;
        }
        if ta2 == ETAG_FVAR && tb2 == ETAG_FVAR {
            if (view_fvar_lo(a2) == view_fvar_lo(b2)) && (view_fvar_hi(a2) == view_fvar_hi(b2)) {
                pop_ret(1u, 0u);
                return;
            }
            f_write(top, 1u, 28u);
            return;
        }
        if ta2 == ETAG_CONST && tb2 == ETAG_CONST {
            if view_const_n(a2) != view_const_n(b2) {
                f_write(top, 1u, 23u);
                return;
            }
            req_raw(22u, OP_LEVEL_CMP, 1u, view_const_us(a2), view_const_us(b2), 0u, 0u);
            return;
        }
        if ta2 == ETAG_PROJ && tb2 == ETAG_PROJ {
            if view_proj_sn(a2) == view_proj_sn(b2)
                && view_proj_idx_lo(a2) == view_proj_idx_lo(b2)
                && view_proj_idx_hi(a2) == view_proj_idx_hi(b2)
            {
                req_call(22u, OP_DEFEQ, view_proj_e(a2), view_proj_e(b2), depth, 0u);
                return;
            }
        }
        if ta2 == ETAG_APP && tb2 == ETAG_APP {
            req_raw(22u, OP_DEFEQ_SPINE, 0u, a2, b2, depth, 0u);
            return;
        }
        f_write(top, 1u, 23u);
        return;
    }
    if phase == 22u {
        if p_res0 != 0u {
            pop_ret(1u, 0u);
            return;
        }
        if ta2 == ETAG_PROJ && tb2 == ETAG_PROJ {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        f_write(top, 1u, 23u);
        return;
    }

    if phase == 23u {
        // Nat literal vs ctor conversion (one step)
        if ta2 == ETAG_LIT && view_lit_kind(a2) <= 1u && tb2 != ETAG_LIT && p_nat_ok {
            let ac = nat_lit_to_ctor(a2);
            if p_halt != 0u { return; }
            req_call(24u, OP_DEFEQ, ac, b2, depth, 0u);
            return;
        }
        if tb2 == ETAG_LIT && view_lit_kind(b2) <= 1u && ta2 != ETAG_LIT && p_nat_ok {
            let bc = nat_lit_to_ctor(b2);
            if p_halt != 0u { return; }
            req_call(24u, OP_DEFEQ, a2, bc, depth, 0u);
            return;
        }
        if (ta2 == ETAG_LIT && view_lit_kind(a2) == 2u && tb2 == ETAG_APP)
            || (tb2 == ETAG_LIT && view_lit_kind(b2) == 2u && ta2 == ETAG_APP)
        {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        f_write(top, 1u, 25u);
        return;
    }
    if phase == 24u {
        if p_res0 != 0u {
            pop_ret(1u, 0u);
            return;
        }
        f_write(top, 1u, 25u);
        return;
    }

    // Unified Lam Eta (left vs right stored in bit 0 of frame[7])
    if phase == 25u {
        if ta2 == ETAG_LAM && tb2 != ETAG_LAM {
            f_write(top, 7u, 0u);
            req_call(26u, OP_INFER_IO, b2, depth, 0u, 0u);
            return;
        }
        if tb2 == ETAG_LAM && ta2 != ETAG_LAM {
            f_write(top, 7u, 1u);
            req_call(26u, OP_INFER_IO, a2, depth, 0u, 0u);
            return;
        }
        f_write(top, 1u, 28u);
        return;
    }
    if phase == 26u {
        req_call(261u, OP_WHNF, p_res0, depth, 0u, 0u);
        return;
    }
    if phase == 261u {
        if word_tag(p_res0) == ETAG_FORALL_E {
            let swap = f_read(top, 7u) != 0u;
            let eta_fn = select(b2, a2, swap);
            let eta_t = intern_s_bind(ETAG_LAM, view_bind_ty(p_res0), intern_s_app(eta_fn, intern_s_bvar(0u, 0u)));
            if p_halt != 0u { return; }
            req_call(262u, OP_DEFEQ, select(a2, eta_t, swap), select(eta_t, b2, swap), depth, 0u);
            return;
        }
        f_write(top, 1u, 28u);
        return;
    }
    if phase == 262u {
        if p_res0 != 0u { pop_ret(1u, 0u); return; }
        f_write(top, 1u, 28u);
        return;
    }

    // phase == 28u: Struct Eta
    if phase == 28u {
        req_raw(4u, OP_DEFEQ_STRUCT_ETA, 0u, a2, b2, depth, 0u);
        return;
    }
}

