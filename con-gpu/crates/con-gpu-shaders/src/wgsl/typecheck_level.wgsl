// Evaluate level_leq(lhs, rhs) using iterative goal tree:
// Returns 1u = true, 0u = false, 2u = unmodeled (delegate).
// Uses a local goal stack of AND groups paired with OR backtracking via depth-2 alt stack.
fn level_subst_param(l: u32, param_n: u32, to_succ: bool) -> u32 {
    // Iterative tiny post-order evaluator for up to 15 level nodes using scratch [400..448)
    var sp = 1u;
    s_write(400u, l);
    s_write(416u, 0u);
    var out = l;
    var ok = true;
    for (var iter = 0u; iter < 64u; iter = iter + 1u) {
        let cur_idx = sp - 1u;
        let cur = s_read(400u + cur_idx);
        let st = s_read(416u + cur_idx);
        let tg = word_tag(cur);
        if st == 0u {
            if tg == LTAG_ZERO {
                out = cur;
            } else if tg == LTAG_PARAM {
                if view_l_op0(cur) == param_n {
                    if to_succ {
                        out = intern_s_l_succ(cur);
                    } else {
                        out = intern_s_l_zero();
                    }
                    if p_halt != 0u { ok = false; break; }
                } else {
                    out = cur;
                }
            } else {
                if sp >= 16u { ok = false; break; }
                s_write(416u + cur_idx, select(2u, 1u, tg == LTAG_SUCC));
                s_write(400u + sp, view_l_op0(cur));
                s_write(416u + sp, 0u);
                sp = sp + 1u;
                continue;
            }
            sp = sp - 1u;
            if sp == 0u { break; }
        } else if st == 1u {
            out = intern_s_l_succ(out);
            if p_halt != 0u { ok = false; break; }
            sp = sp - 1u;
            if sp == 0u { break; }
        } else if st == 2u {
            s_write(432u + cur_idx, out);
            s_write(416u + cur_idx, 3u);
            if sp >= 16u { ok = false; break; }
            s_write(400u + sp, view_l_op1(cur));
            s_write(416u + sp, 0u);
            sp = sp + 1u;
        } else {
            let left = s_read(432u + cur_idx);
            if tg == LTAG_MAX {
                out = level_mk_max_simp(left, out);
            } else {
                out = level_mk_imax_simp(left, out);
            }
            if p_halt != 0u { ok = false; break; }
            sp = sp - 1u;
            if sp == 0u { break; }
        }
    }
    return select(0u, out, ok && sp == 0u);
}

fn find_imax_right_param(l_in: u32) -> u32 {
    var cur = l_in;
    for (var i = 0u; i < 16u; i = i + 1u) {
        let tg = word_tag(cur);
        if tg == LTAG_PARAM { return view_l_op0(cur); }
        if tg == LTAG_IMAX || tg == LTAG_MAX {
            let r = view_l_op1(cur);
            if word_tag(r) == LTAG_PARAM { return view_l_op0(r); }
            cur = r;
            continue;
        }
        return NONE_U32;
    }
    return NONE_U32;
}

fn level_leq_core(a_init: u32, b_init: u32, splits_left: u32) -> u32 {
    // Goal stack and OR alt stack stored in scratch [256..368):
    //   ga[32]: [256..288), gb[32]: [288..320), alt_a[16]: [320..336), alt_b[16]: [336..352), alt_gtop[16]: [352..368)
    var gtop = 1u;
    s_write(256u, a_init);
    s_write(288u, b_init);

    var alt_sp = 0u;
    var case_splits = 0u;

    for (var step = 0u; step < 128u; step = step + 1u) {
        if gtop == 0u {
            return 1u;
        }
        gtop = gtop - 1u;
        var a = s_read(256u + gtop);
        var b = s_read(288u + gtop);

        // Quick local loop: strip matching Succ, simplify trivial Max/Zero
        var resolved = false;
        var failed = false;
        for (var k = 0u; k < 16u; k = k + 1u) {
            if a == b || level_is_zero(a) || level_struct_eq(a, b) {
                resolved = true;
                break;
            }
            if word_tag(a) == LTAG_IMAX {
                a = level_mk_imax_simp(view_l_op0(a), view_l_op1(a));
                if p_halt != 0u { return 2u; }
                continue;
            }
            if word_tag(b) == LTAG_IMAX {
                b = level_mk_imax_simp(view_l_op0(b), view_l_op1(b));
                if p_halt != 0u { return 2u; }
                continue;
            }
            if word_tag(a) == LTAG_SUCC && word_tag(b) == LTAG_SUCC {
                a = view_l_op0(a);
                b = view_l_op0(b);
                continue;
            }
            break;
        }
        if resolved {
            continue;
        }

        let ta = word_tag(a);
        let tb = word_tag(b);

        if ta == LTAG_MAX {
            if gtop + 2u > 32u { return 2u; }
            s_write(256u + gtop, view_l_op0(a));
            s_write(288u + gtop, b);
            gtop = gtop + 1u;
            s_write(256u + gtop, view_l_op1(a));
            s_write(288u + gtop, b);
            gtop = gtop + 1u;
            continue;
        }

        if ta == LTAG_IMAX || tb == LTAG_IMAX {
            if case_splits >= splits_left { return 2u; }
            let rhs = select(view_l_op1(b), view_l_op1(a), ta == LTAG_IMAX);
            let pn = find_imax_right_param(rhs);
            if pn == NONE_U32 || gtop + 2u > 32u { return 2u; }
            case_splits = case_splits + 1u;
            for (var arm = 0u; arm < 4u; arm = arm + 1u) {
                let tgt = select(a, b, (arm & 1u) != 0u);
                let v = level_subst_param(tgt, pn, arm >= 2u);
                if v == 0u || p_halt != 0u { return 2u; }
                s_write(448u + arm, v);
            }
            s_write(256u + gtop, s_read(448u)); s_write(288u + gtop, s_read(449u)); gtop = gtop + 1u;
            s_write(256u + gtop, s_read(450u)); s_write(288u + gtop, s_read(451u)); gtop = gtop + 1u;
            continue;
        }

        if ta == LTAG_SUCC {
            var depth_s = 0u;
            var base_a = a;
            for (var s = 0u; s < 16u; s = s + 1u) {
                if word_tag(base_a) != LTAG_SUCC { break; }
                base_a = view_l_op0(base_a);
                depth_s = depth_s + 1u;
            }
            if word_tag(base_a) == LTAG_MAX {
                if gtop + 2u > 32u { return 2u; }
                var lhs1 = view_l_op0(base_a);
                var lhs2 = view_l_op1(base_a);
                for (var s = 0u; s < depth_s; s = s + 1u) {
                    lhs1 = intern_s_l_succ(lhs1);
                    lhs2 = intern_s_l_succ(lhs2);
                    if p_halt != 0u { return 2u; }
                }
                s_write(256u + gtop, lhs1); s_write(288u + gtop, b); gtop = gtop + 1u;
                s_write(256u + gtop, lhs2); s_write(288u + gtop, b); gtop = gtop + 1u;
                continue;
            }
            if word_tag(base_a) == LTAG_IMAX {
                return 2u;
            }
        }

        if tb == LTAG_MAX {
            if alt_sp >= 16u || gtop >= 32u { return 2u; }
            s_write(320u + alt_sp, a);
            s_write(336u + alt_sp, view_l_op1(b));
            s_write(352u + alt_sp, gtop);
            alt_sp = alt_sp + 1u;
            s_write(256u + gtop, a);
            s_write(288u + gtop, view_l_op0(b));
            gtop = gtop + 1u;
            continue;
        }
        if tb == LTAG_SUCC {
            var depth_b = 0u;
            var base_b = b;
            for (var s = 0u; s < 16u; s = s + 1u) {
                if word_tag(base_b) != LTAG_SUCC { break; }
                base_b = view_l_op0(base_b);
                depth_b = depth_b + 1u;
            }
            if word_tag(base_b) == LTAG_MAX {
                if alt_sp >= 16u || gtop >= 32u { return 2u; }
                var rhs1 = view_l_op0(base_b);
                var rhs2 = view_l_op1(base_b);
                for (var s = 0u; s < depth_b; s = s + 1u) {
                    rhs1 = intern_s_l_succ(rhs1);
                    rhs2 = intern_s_l_succ(rhs2);
                    if p_halt != 0u { return 2u; }
                }
                s_write(320u + alt_sp, a);
                s_write(336u + alt_sp, rhs2);
                s_write(352u + alt_sp, gtop);
                alt_sp = alt_sp + 1u;
                s_write(256u + gtop, a);
                s_write(288u + gtop, rhs1);
                gtop = gtop + 1u;
                continue;
            }
            if word_tag(base_b) == LTAG_IMAX {
                return 2u;
            }
        }

        var ka = 0u;
        var ba = a;
        for (var s = 0u; s < 32u; s = s + 1u) {
            if word_tag(ba) != LTAG_SUCC { break; }
            ba = view_l_op0(ba);
            ka = ka + 1u;
        }
        var kb = 0u;
        var bb = b;
        for (var s = 0u; s < 32u; s = s + 1u) {
            if word_tag(bb) != LTAG_SUCC { break; }
            bb = view_l_op0(bb);
            kb = kb + 1u;
        }
        let bta = word_tag(ba);
        let btb = word_tag(bb);
        var ok_leaf = false;
        if bta == LTAG_ZERO && btb == LTAG_ZERO {
            ok_leaf = ka <= kb;
        } else if bta == LTAG_ZERO && btb == LTAG_PARAM {
            ok_leaf = ka <= kb;
        } else if bta == LTAG_PARAM && btb == LTAG_PARAM {
            ok_leaf = (view_l_op0(ba) == view_l_op0(bb)) && (ka <= kb);
        } else if bta == LTAG_IMAX || btb == LTAG_IMAX || bta == LTAG_MAX || btb == LTAG_MAX {
            return 2u;
        }

        if ok_leaf {
            continue;
        }
        failed = true;
        if failed {
            if alt_sp == 0u {
                return 0u;
            }
            alt_sp = alt_sp - 1u;
            gtop = s_read(352u + alt_sp);
            s_write(256u + gtop, s_read(320u + alt_sp));
            s_write(288u + gtop, s_read(336u + alt_sp));
            gtop = gtop + 1u;
        }
    }
    return 2u;
}

fn exec_level_cmp(top: u32) {
    let mode = f_read(top, 1u);
    let a = f_read(top, 2u);
    let b = f_read(top, 3u);
    if a == b {
        pop_ret(1u, 0u);
        return;
    }
    var n = 1u;
    if mode != 0u {
        n = ls_len(a);
        if n != ls_len(b) {
            pop_ret(0u, 0u);
            return;
        }
    }
    let total = n * 2u;
    var ok = 1u;
    for (var idx = 0u; idx < total; idx = idx + 1u) {
        let i = idx >> 1u;
        var l1 = a;
        var l2 = b;
        if mode != 0u {
            l1 = ls_item(a, i);
            l2 = ls_item(b, i);
        }
        let x = select(l1, l2, (idx & 1u) != 0u);
        let y = select(l2, l1, (idx & 1u) != 0u);
        if x != y && !level_struct_eq(x, y) {
            let r = level_leq_core(x, y, 2u);
            if r != 1u {
                ok = r;
                break;
            }
        }
    }
    if ok == 2u {
        halt_delegate(REASON_UNMODELED);
        return;
    }
    pop_ret(ok, 0u);
}

