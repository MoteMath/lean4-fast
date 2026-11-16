// 64-bit Nat helpers without u64
fn nat_add_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> vec3<u32> {
    let lo = alo + blo;
    var carry = 0u;
    if lo < alo { carry = 1u; }
    let hi = ahi + bhi + carry;
    var ovf = 0u;
    if hi < ahi || (ahi == 0xFFFFFFFFu && carry != 0u && bhi == 0u) || (bhi > 0u && hi < bhi) {
        ovf = 1u;
    }
    // Cleaner overflow check: check ahi + bhi + carry > u32::MAX
    let s1 = ahi + bhi;
    var ov1 = 0u;
    if s1 < ahi { ov1 = 1u; }
    let s2 = s1 + carry;
    var ov2 = 0u;
    if s2 < s1 { ov2 = 1u; }
    ovf = ov1 | ov2;
    return vec3<u32>(lo, s2, ovf);
}

// Exact 32x32 -> 64 mul using 16x16 splits
fn mul32x32(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xFFFFu;
    let a1 = a >> 16u;
    let b0 = b & 0xFFFFu;
    let b1 = b >> 16u;
    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;
    let mid = (p00 >> 16u) + (p01 & 0xFFFFu) + (p10 & 0xFFFFu);
    let lo = (p00 & 0xFFFFu) | (mid << 16u);
    let hi = p11 + (p01 >> 16u) + (p10 >> 16u) + (mid >> 16u);
    return vec2<u32>(lo, hi);
}

fn nat_mul_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> vec3<u32> {
    if ahi != 0u && bhi != 0u {
        return vec3<u32>(0u, 0u, 1u);
    }
    let p_ll = mul32x32(alo, blo);
    let p_lh = mul32x32(alo, bhi);
    let p_hl = mul32x32(ahi, blo);
    if p_lh.y != 0u || p_hl.y != 0u {
        return vec3<u32>(0u, 0u, 1u);
    }
    let hi1 = p_ll.y + p_lh.x;
    var ov = 0u;
    if hi1 < p_ll.y { ov = 1u; }
    let hi2 = hi1 + p_hl.x;
    if hi2 < hi1 { ov = 1u; }
    return vec3<u32>(p_ll.x, hi2, ov);
}

fn nat_cmp_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> i32 {
    if ahi < bhi { return -1; }
    if ahi > bhi { return 1; }
    if alo < blo { return -1; }
    if alo > blo { return 1; }
    return 0;
}

// Exact 64-bit unsigned division and remainder via restoring binary long division (vec2<u32>).
// Returns vec4<u32>(qlo, qhi, rlo, rhi). Matches Lean Nat semantics: div a 0 = 0, mod a 0 = a.
fn nat_divmod_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> vec4<u32> {
    if blo == 0u && bhi == 0u {
        return vec4<u32>(0u, 0u, alo, ahi);
    }
    if ahi == 0u && bhi == 0u {
        return vec4<u32>(alo / blo, 0u, alo % blo, 0u);
    }
    if nat_cmp_u64(alo, ahi, blo, bhi) < 0 {
        return vec4<u32>(0u, 0u, alo, ahi);
    }
    let top_bit = select(31u - countLeadingZeros(alo | 1u), 63u - countLeadingZeros(ahi | 1u), ahi != 0u);
    var bit = top_bit + 1u;
    var qlo = 0u;
    var qhi = 0u;
    var rlo = 0u;
    var rhi = 0u;
    while bit > 0u {
        bit = bit - 1u;
        let is_hi = bit >= 32u;
        let sh = bit & 31u;
        let next_bit = (select(alo, ahi, is_hi) >> sh) & 1u;
        let ov_r = (rhi >> 31u) & 1u;
        let nrhi = (rhi << 1u) | (rlo >> 31u);
        let nrlo = (rlo << 1u) | next_bit;
        let ge = (ov_r != 0u) || (nrhi > bhi) || (nrhi == bhi && nrlo >= blo);
        let borrow = select(0u, 1u, nrlo < blo);
        let sub_lo = nrlo - blo;
        let sub_hi = nrhi - bhi - borrow;
        rlo = select(nrlo, sub_lo, ge);
        rhi = select(nrhi, sub_hi, ge);
        let set_bit = select(0u, 1u << sh, ge);
        qlo = qlo | select(set_bit, 0u, is_hi);
        qhi = qhi | select(0u, set_bit, is_hi);
    }
    return vec4<u32>(qlo, qhi, rlo, rhi);
}

fn nat_shr_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> vec2<u32> {
    if bhi != 0u || blo >= 64u {
        return vec2<u32>(0u, 0u);
    }
    if blo == 0u {
        return vec2<u32>(alo, ahi);
    }
    if blo >= 32u {
        let sh = blo - 32u;
        return vec2<u32>(ahi >> sh, 0u);
    }
    return vec2<u32>((alo >> blo) | (ahi << (32u - blo)), ahi >> blo);
}

fn nat_shl_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> vec3<u32> {
    if alo == 0u && ahi == 0u {
        return vec3<u32>(0u, 0u, 0u);
    }
    if bhi != 0u || blo >= 64u {
        return vec3<u32>(0u, 0u, 1u);
    }
    if blo == 0u {
        return vec3<u32>(alo, ahi, 0u);
    }
    if blo >= 32u {
        if ahi != 0u {
            return vec3<u32>(0u, 0u, 1u);
        }
        let sh = blo - 32u;
        if sh > 0u && (alo >> (32u - sh)) != 0u {
            return vec3<u32>(0u, 0u, 1u);
        }
        return vec3<u32>(0u, alo << sh, 0u);
    }
    if (ahi >> (32u - blo)) != 0u {
        return vec3<u32>(0u, 0u, 1u);
    }
    return vec3<u32>(alo << blo, (ahi << blo) | (alo >> (32u - blo)), 0u);
}

fn ctz64(lo: u32, hi: u32) -> u32 {
    if lo != 0u {
        return countTrailingZeros(lo);
    }
    if hi != 0u {
        return 32u + countTrailingZeros(hi);
    }
    return 64u;
}

// Exact 64-bit Nat exponentiation (alo, ahi) ^ (blo, bhi); returns vec3(lo, hi, ovf).
fn nat_pow_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> vec3<u32> {
    // Lean 4's kernel refuses Nat.pow whenever the exponent does not fit in u32 (even for base 0 or 1).
    if bhi != 0u {
        return vec3<u32>(0u, 0u, 1u);
    }
    if blo == 0u {
        return vec3<u32>(1u, 0u, 0u);
    }
    if alo == 0u && ahi == 0u {
        return vec3<u32>(0u, 0u, 0u);
    }
    if alo == 1u && ahi == 0u {
        return vec3<u32>(1u, 0u, 0u);
    }
    if blo >= 64u {
        return vec3<u32>(0u, 0u, 1u);
    }
    var base_lo = alo;
    var base_hi = ahi;
    var res_lo = 1u;
    var res_hi = 0u;
    var exp = blo;
    while exp > 0u {
        if (exp & 1u) != 0u {
            let pm = nat_mul_u64(res_lo, res_hi, base_lo, base_hi);
            if pm.z != 0u {
                return vec3<u32>(0u, 0u, 1u);
            }
            res_lo = pm.x;
            res_hi = pm.y;
        }
        exp = exp >> 1u;
        if exp > 0u {
            let sq = nat_mul_u64(base_lo, base_hi, base_lo, base_hi);
            if sq.z != 0u {
                return vec3<u32>(0u, 0u, 1u);
            }
            base_lo = sq.x;
            base_hi = sq.y;
        }
    }
    return vec3<u32>(res_lo, res_hi, 0u);
}

// Exact 64-bit Nat greatest common divisor; returns vec3(lo, hi, ok) where ok=0 delegates cleanly.
fn nat_gcd_u64(alo: u32, ahi: u32, blo: u32, bhi: u32) -> vec3<u32> {
    if alo == 0u && ahi == 0u {
        return vec3<u32>(blo, bhi, 1u);
    }
    if blo == 0u && bhi == 0u {
        return vec3<u32>(alo, ahi, 1u);
    }
    if ahi == 0u && bhi == 0u {
        var x = alo;
        var y = blo;
        while y != 0u {
            let r = x % y;
            x = y;
            y = r;
        }
        return vec3<u32>(x, 0u, 1u);
    }
    let az = ctz64(alo, ahi);
    let bz = ctz64(blo, bhi);
    let k = min(az, bz);
    var u = nat_shr_u64(alo, ahi, az, 0u);
    var v = nat_shr_u64(blo, bhi, bz, 0u);
    for (var iter = 0u; iter < 128u; iter = iter + 1u) {
        let cmp = nat_cmp_u64(u.x, u.y, v.x, v.y);
        if cmp == 0 {
            let g = nat_shl_u64(u.x, u.y, k, 0u);
            if g.z != 0u {
                return vec3<u32>(0u, 0u, 0u);
            }
            return vec3<u32>(g.x, g.y, 1u);
        }
        if cmp > 0 {
            let diff = nat_sub_u64(u.x, u.y, v.x, v.y);
            let tz = ctz64(diff.x, diff.y);
            u = nat_shr_u64(diff.x, diff.y, tz, 0u);
        } else {
            let diff = nat_sub_u64(v.x, v.y, u.x, u.y);
            let tz = ctz64(diff.x, diff.y);
            v = nat_shr_u64(diff.x, diff.y, tz, 0u);
        }
    }
    return vec3<u32>(0u, 0u, 0u);
}

// Multi-limb BigNat exact arithmetic helpers (up to MAX_BIGNAT_LIMBS = 64u = 2048 bits).
// Load trimmed u32 limbs of literal `lit` into scratch workspace [work_base .. work_base + len).
// Returns limb count (0..=MAX_BIGNAT_LIMBS) or NONE_U32 if length exceeds MAX_BIGNAT_LIMBS.
fn load_bignat_work(lit: u32, work_base: u32) -> u32 {
    let k = view_lit_kind(lit);
    if k == 0u {
        let lo = view_lit_a(lit);
        let hi = view_lit_b(lit);
        if hi != 0u {
            s_write(work_base, lo);
            s_write(work_base + 1u, hi);
            return 2u;
        }
        if lo != 0u {
            s_write(work_base, lo);
            return 1u;
        }
        return 0u;
    }
    let la = bignat_trimmed_len(lit);
    if la > MAX_BIGNAT_LIMBS {
        halt_delegate(REASON_UNMODELED);
        return NONE_U32;
    }
    let off = view_lit_a(lit);
    for (var i = 0u; i < la; i = i + 1u) {
        s_write(work_base + i, bignat_raw_limb(off, i));
    }
    return la;
}

fn bignat_work_cmp(la: u32, lb: u32) -> i32 {
    if la < lb { return -1; }
    if la > lb { return 1; }
    var k = la;
    while k > 0u {
        k = k - 1u;
        let wa = s_read(BIGNAT_WORK_A + k);
        let wb = s_read(BIGNAT_WORK_B + k);
        if wa < wb { return -1; }
        if wa > wb { return 1; }
    }
    return 0;
}

fn bignat_add_u32(la: u32, rhs0: u32) -> u32 {
    if la == 0u {
        return intern_s_lit_u64(rhs0, 0u);
    }
    var carry = rhs0;
    for (var i = 0u; i < la; i = i + 1u) {
        let ai = s_read(BIGNAT_WORK_A + i);
        let s = ai + carry;
        let next_c = select(0u, 1u, s < ai);
        s_write(BIGNAT_WORK_OUT + i, s);
        carry = next_c;
    }
    var raw_len = la;
    if carry != 0u {
        if la >= MAX_BIGNAT_LIMBS {
            halt_delegate(REASON_UNMODELED);
            return NONE_U32;
        }
        s_write(BIGNAT_WORK_OUT + la, carry);
        raw_len = la + 1u;
    }
    return intern_s_bignat_from_work(BIGNAT_WORK_OUT, raw_len);
}

fn bignat_sub_u32(la: u32, rhs0: u32) -> u32 {
    if la == 0u {
        return intern_s_lit_u64(0u, 0u);
    }
    if la == 1u {
        let l0 = s_read(BIGNAT_WORK_A);
        if l0 <= rhs0 {
            return intern_s_lit_u64(0u, 0u);
        }
        return intern_s_lit_u64(l0 - rhs0, 0u);
    }
    var borrow = rhs0;
    for (var i = 0u; i < la; i = i + 1u) {
        let ai = s_read(BIGNAT_WORK_A + i);
        let d = ai - borrow;
        let next_b = select(0u, 1u, ai < borrow);
        s_write(BIGNAT_WORK_OUT + i, d);
        borrow = next_b;
    }
    return intern_s_bignat_from_work(BIGNAT_WORK_OUT, la);
}

fn bignat_work_add(la: u32, lb: u32) -> u32 {
    let m = max(la, lb);
    if m == 0u {
        return intern_s_lit_u64(0u, 0u);
    }
    var carry = 0u;
    for (var i = 0u; i < m; i = i + 1u) {
        let ai = select(0u, s_read(BIGNAT_WORK_A + i), i < la);
        let bi = select(0u, s_read(BIGNAT_WORK_B + i), i < lb);
        let s1 = ai + bi;
        let c1 = select(0u, 1u, s1 < ai);
        let s2 = s1 + carry;
        let c2 = select(0u, 1u, s2 < s1);
        s_write(BIGNAT_WORK_OUT + i, s2);
        carry = c1 | c2;
    }
    var raw_len = m;
    if carry != 0u {
        if m >= MAX_BIGNAT_LIMBS {
            halt_delegate(REASON_UNMODELED);
            return NONE_U32;
        }
        s_write(BIGNAT_WORK_OUT + m, carry);
        raw_len = m + 1u;
    }
    return intern_s_bignat_from_work(BIGNAT_WORK_OUT, raw_len);
}

fn bignat_work_sub(la: u32, lb: u32) -> u32 {
    if bignat_work_cmp(la, lb) <= 0 {
        return intern_s_lit_u64(0u, 0u);
    }
    var borrow = 0u;
    for (var i = 0u; i < la; i = i + 1u) {
        let ai = s_read(BIGNAT_WORK_A + i);
        let bi = select(0u, s_read(BIGNAT_WORK_B + i), i < lb);
        let s1 = ai - bi;
        let b1 = select(0u, 1u, ai < bi);
        let s2 = s1 - borrow;
        let b2 = select(0u, 1u, s1 < borrow);
        s_write(BIGNAT_WORK_OUT + i, s2);
        borrow = b1 | b2;
    }
    return intern_s_bignat_from_work(BIGNAT_WORK_OUT, la);
}

fn bignat_work_mul(la: u32, lb: u32) -> u32 {
    if la == 0u || lb == 0u {
        return intern_s_lit_u64(0u, 0u);
    }
    let out_cap = min(la + lb, MAX_BIGNAT_LIMBS);
    for (var k = 0u; k < out_cap; k = k + 1u) {
        s_write(BIGNAT_WORK_OUT + k, 0u);
    }
    var ovf = false;
    for (var i = 0u; i < la; i = i + 1u) {
        let ai = s_read(BIGNAT_WORK_A + i);
        if ai != 0u {
            var carry = 0u;
            for (var j = 0u; j < lb; j = j + 1u) {
                let bj = s_read(BIGNAT_WORK_B + j);
                let p = mul32x32(ai, bj);
                let k = i + j;
                if k >= MAX_BIGNAT_LIMBS {
                    if p.x != 0u || p.y != 0u || carry != 0u {
                        ovf = true;
                    }
                } else {
                    let cur = s_read(BIGNAT_WORK_OUT + k);
                    let s1 = cur + p.x;
                    let c1 = select(0u, 1u, s1 < cur);
                    let s2 = s1 + carry;
                    let c2 = select(0u, 1u, s2 < s1);
                    s_write(BIGNAT_WORK_OUT + k, s2);
                    carry = p.y + c1 + c2;
                }
            }
            if carry != 0u {
                let k_end = i + lb;
                if k_end >= MAX_BIGNAT_LIMBS {
                    ovf = true;
                } else {
                    s_write(BIGNAT_WORK_OUT + k_end, carry);
                }
            }
        }
    }
    if ovf {
        halt_delegate(REASON_UNMODELED);
        return NONE_U32;
    }
    return intern_s_bignat_from_work(BIGNAT_WORK_OUT, out_cap);
}

fn bignat_work_shl(la: u32, lb: u32, orig_a: u32) -> u32 {
    if la == 0u {
        return intern_s_lit_u64(0u, 0u);
    }
    if lb > 1u {
        halt_delegate(REASON_UNMODELED);
        return NONE_U32;
    }
    let sh = select(0u, s_read(BIGNAT_WORK_B), lb > 0u);
    if sh == 0u {
        if view_lit_kind(orig_a) == 0u {
            return orig_a;
        }
        for (var i = 0u; i < la; i = i + 1u) {
            s_write(BIGNAT_WORK_OUT + i, s_read(BIGNAT_WORK_A + i));
        }
        return intern_s_bignat_from_work(BIGNAT_WORK_OUT, la);
    }
    let word_sh = sh >> 5u;
    let bit_sh = sh & 31u;
    if word_sh >= MAX_BIGNAT_LIMBS || (la + word_sh) > MAX_BIGNAT_LIMBS {
        halt_delegate(REASON_UNMODELED);
        return NONE_U32;
    }
    for (var k = 0u; k < word_sh; k = k + 1u) {
        s_write(BIGNAT_WORK_OUT + k, 0u);
    }
    var carry = 0u;
    if bit_sh == 0u {
        for (var i = 0u; i < la; i = i + 1u) {
            s_write(BIGNAT_WORK_OUT + word_sh + i, s_read(BIGNAT_WORK_A + i));
        }
    } else {
        let rsh = 32u - bit_sh;
        for (var i = 0u; i < la; i = i + 1u) {
            let ai = s_read(BIGNAT_WORK_A + i);
            s_write(BIGNAT_WORK_OUT + word_sh + i, (ai << bit_sh) | carry);
            carry = ai >> rsh;
        }
    }
    var raw_len = word_sh + la;
    if carry != 0u {
        if raw_len >= MAX_BIGNAT_LIMBS {
            halt_delegate(REASON_UNMODELED);
            return NONE_U32;
        }
        s_write(BIGNAT_WORK_OUT + raw_len, carry);
        raw_len = raw_len + 1u;
    }
    return intern_s_bignat_from_work(BIGNAT_WORK_OUT, raw_len);
}

fn bignat_work_bitwise(la: u32, lb: u32, mode: u32) -> u32 {
    let m = select(max(la, lb), min(la, lb), mode == 0u);
    if m == 0u {
        return intern_s_lit_u64(0u, 0u);
    }
    for (var i = 0u; i < m; i = i + 1u) {
        let ai = select(0u, s_read(BIGNAT_WORK_A + i), i < la);
        let bi = select(0u, s_read(BIGNAT_WORK_B + i), i < lb);
        var res_w = ai ^ bi;
        if mode == 0u {
            res_w = ai & bi;
        } else if mode == 1u {
            res_w = ai | bi;
        }
        s_write(BIGNAT_WORK_OUT + i, res_w);
    }
    return intern_s_bignat_from_work(BIGNAT_WORK_OUT, m);
}

// Evaluate unary Nat operations on u64 & <=64-limb BigNat literals; promotes u64 overflow to BigNat.
fn eval_nat_unary(cn: u32, a: u32) -> u32 {
    let ka = view_lit_kind(a);
    if ka > 1u {
        halt_delegate(REASON_UNMODELED);
        return NONE_U32;
    }
    let is_succ = cn == hdr.pin_nat_succ;
    let is_pred = cn == hdr.pin_nat_pred && hdr.pin_nat_pred != 0u;
    if !is_succ && !is_pred {
        return NONE_U32;
    }
    if ka == 0u {
        let alo = view_lit_a(a);
        let ahi = view_lit_b(a);
        if is_pred {
            let diff = nat_sub_u64(alo, ahi, 1u, 0u);
            return intern_s_lit_u64(diff.x, diff.y);
        }
        let sum = nat_add_u64(alo, ahi, 1u, 0u);
        if sum.z == 0u {
            return intern_s_lit_u64(sum.x, sum.y);
        }
    }
    let la = load_bignat_work(a, BIGNAT_WORK_A);
    if p_halt != 0u { return NONE_U32; }
    if is_succ {
        return bignat_add_u32(la, 1u);
    }
    return bignat_sub_u32(la, 1u);
}

fn eval_nat_binary(cn: u32, a: u32, b: u32) -> u32 {
    let ka = view_lit_kind(a);
    let kb = view_lit_kind(b);
    if ka > 1u || kb > 1u {
        halt_delegate(REASON_UNMODELED);
        return NONE_U32;
    }
    if ka == 0u && kb == 0u {
        let alo = view_lit_a(a);
        let ahi = view_lit_b(a);
        let blo = view_lit_a(b);
        let bhi = view_lit_b(b);
        if cn == hdr.pin_nat_sub {
            let r = nat_sub_u64(alo, ahi, blo, bhi);
            return intern_s_lit_u64(r.x, r.y);
        }
        if cn == hdr.pin_nat_div || cn == hdr.pin_nat_mod {
            let r = nat_divmod_u64(alo, ahi, blo, bhi);
            let is_div = cn == hdr.pin_nat_div;
            return intern_s_lit_u64(select(r.z, r.x, is_div), select(r.w, r.y, is_div));
        }
        if cn == hdr.pin_nat_shr {
            let r = nat_shr_u64(alo, ahi, blo, bhi);
            return intern_s_lit_u64(r.x, r.y);
        }
        if cn == hdr.pin_nat_beq {
            if !p_bool_ok { return NONE_U32; }
            if alo == blo && ahi == bhi {
                return intern_s_const(hdr.pin_bool_true, hdr.pin_empty_levels);
            }
            return intern_s_const(hdr.pin_bool_false, hdr.pin_empty_levels);
        }
        if cn == hdr.pin_nat_ble {
            if !p_bool_ok { return NONE_U32; }
            if nat_cmp_u64(alo, ahi, blo, bhi) <= 0 {
                return intern_s_const(hdr.pin_bool_true, hdr.pin_empty_levels);
            }
            return intern_s_const(hdr.pin_bool_false, hdr.pin_empty_levels);
        }
        if cn == hdr.pin_nat_land {
            return intern_s_lit_u64(alo & blo, ahi & bhi);
        }
        if cn == hdr.pin_nat_lor {
            return intern_s_lit_u64(alo | blo, ahi | bhi);
        }
        if cn == hdr.pin_nat_xor {
            return intern_s_lit_u64(alo ^ blo, ahi ^ bhi);
        }
        if cn == hdr.pin_nat_pow && hdr.pin_nat_pow != 0u {
            let r = nat_pow_u64(alo, ahi, blo, bhi);
            if r.z != 0u {
                halt_delegate(REASON_UNMODELED);
                return NONE_U32;
            }
            return intern_s_lit_u64(r.x, r.y);
        }
        if cn == hdr.pin_nat_gcd && hdr.pin_nat_gcd != 0u {
            let r = nat_gcd_u64(alo, ahi, blo, bhi);
            if r.z == 0u {
                halt_delegate(REASON_UNMODELED);
                return NONE_U32;
            }
            return intern_s_lit_u64(r.x, r.y);
        }
        if cn == hdr.pin_nat_add {
            let r = nat_add_u64(alo, ahi, blo, bhi);
            if r.z == 0u {
                return intern_s_lit_u64(r.x, r.y);
            }
        } else if cn == hdr.pin_nat_mul {
            let r = nat_mul_u64(alo, ahi, blo, bhi);
            if r.z == 0u {
                return intern_s_lit_u64(r.x, r.y);
            }
        } else if cn == hdr.pin_nat_shl {
            let r = nat_shl_u64(alo, ahi, blo, bhi);
            if r.z == 0u {
                return intern_s_lit_u64(r.x, r.y);
            }
        } else {
            halt_delegate(REASON_UNMODELED);
            return NONE_U32;
        }
    }

    // BigNat or u64 overflow path: load operands into workspace ONCE, then call each op ONCE.
    let is_add = cn == hdr.pin_nat_add;
    let is_sub = cn == hdr.pin_nat_sub;
    let is_mul = cn == hdr.pin_nat_mul;
    let is_shl = cn == hdr.pin_nat_shl;
    let is_beq = cn == hdr.pin_nat_beq;
    let is_ble = cn == hdr.pin_nat_ble;
    let is_land = cn == hdr.pin_nat_land;
    let is_lor = cn == hdr.pin_nat_lor;
    let is_xor = cn == hdr.pin_nat_xor;
    if !is_add && !is_sub && !is_mul && !is_shl && !is_beq && !is_ble && !is_land && !is_lor && !is_xor {
        halt_delegate(REASON_UNMODELED);
        return NONE_U32;
    }
    if (is_beq || is_ble) && !p_bool_ok {
        return NONE_U32;
    }
    let la = load_bignat_work(a, BIGNAT_WORK_A);
    if p_halt != 0u { return NONE_U32; }
    let lb = load_bignat_work(b, BIGNAT_WORK_B);
    if p_halt != 0u { return NONE_U32; }

    if is_add { return bignat_work_add(la, lb); }
    if is_sub { return bignat_work_sub(la, lb); }
    if is_mul { return bignat_work_mul(la, lb); }
    if is_shl { return bignat_work_shl(la, lb, a); }
    if is_beq || is_ble {
        let cmp = bignat_work_cmp(la, lb);
        let truth = select(cmp <= 0, cmp == 0, is_beq);
        let b_name = select(hdr.pin_bool_false, hdr.pin_bool_true, truth);
        return intern_s_const(b_name, hdr.pin_empty_levels);
    }
    var bw_mode = 2u;
    if is_land { bw_mode = 0u; }
    else if is_lor { bw_mode = 1u; }
    return bignat_work_bitwise(la, lb, bw_mode);
}

// Check Level.isNeverZero using fixed scratch stack [560..592).
// Returns 1u = provably never zero, 0u = may be zero, 2u = unmodeled.
fn level_is_never_zero(u: u32) -> u32 {
    var sp = 1u;
    var step = 0u;
    s_write(560u, u);
    while sp > 0u && step < 64u {
        step = step + 1u;
        sp = sp - 1u;
        let cur = s_read(560u + sp);
        let tg = word_tag(cur);
        if tg == LTAG_SUCC {
            return 1u;
        } else if tg == LTAG_IMAX {
            if sp >= 32u { return 2u; }
            s_write(560u + sp, view_l_op1(cur));
            sp = sp + 1u;
        } else if tg == LTAG_MAX {
            if sp + 1u >= 32u { return 2u; }
            s_write(560u + sp, view_l_op0(cur));
            s_write(560u + sp + 1u, view_l_op1(cur));
            sp = sp + 2u;
        }
    }
    if sp == 0u {
        return 0u;
    }
    return 2u;
}

// OP_WHNF_CORE frame fields:
//   [2]=cur, [3]=depth, [4]=cheap, [5]=args_ptr/save0, [6]=argc/save1, [7]=head2/aux
fn exec_whnf_core(top: u32) {
    let phase = f_read(top, 1u);
    var cur = f_read(top, 2u);
    let depth = f_read(top, 3u);
    let cheap = f_read(top, 4u);

    if phase == 0u {
        // Head normalization loop entry for current term
        let tg = word_tag(cur);
        if is_stuck_head_tag(tg) || tg == ETAG_LAM {
            pop_ret(cur, 0u);
            return;
        }
        if tg == ETAG_BVAR {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        if tg == ETAG_LET_E {
            let v_ptr = s_alloc(1u);
            if p_halt != 0u { return; }
            s_write(v_ptr, view_let_val(cur));
            req_call(1u, OP_INST_REV, view_let_body(cur), v_ptr, 1u, 0u);
            return;
        }
        if tg == ETAG_PROJ {
            let pe = view_proj_e(cur);
            req_call(2u, select(OP_WHNF, OP_WHNF_CORE, cheap != 0u), pe, depth, 0u, 0u);
            return;
        }
        // ETAG_APP: count spine length first
        var argc = 0u;
        var hd = cur;
        for (var i = 0u; i < 256u; i = i + 1u) {
            if word_tag(hd) != ETAG_APP { break; }
            hd = view_app_f(hd);
            argc = argc + 1u;
        }
        if word_tag(hd) == ETAG_APP {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        let buf_ptr = s_alloc(argc * 2u);
        if p_halt != 0u { return; }
        let args_ptr = buf_ptr;
        let nodes_ptr = buf_ptr + argc;
        var walk = cur;
        for (var j = 0u; j < argc; j = j + 1u) {
            let slot = argc - 1u - j;
            s_write(nodes_ptr + slot, walk);
            s_write(args_ptr + slot, view_app_a(walk));
            walk = view_app_f(walk);
        }
        f_write(top, 5u, buf_ptr);
        f_write(top, 6u, argc);
        f_write(top, 7u, hd);

        if is_stuck_head_tag(word_tag(hd)) {
            // Skip whnf_core on head, go directly to phase 4 (iota / stuck check)
            p_res0 = hd;
            f_write(top, 1u, 4u);
            return;
        }
        req_call(3u, OP_WHNF_CORE, hd, depth, cheap, 0u);
        return;
    }

    if phase == 1u {
        // Zeta step complete
        f_write(top, 2u, p_res0);
        f_write(top, 1u, 0u);
        return;
    }

    if phase == 2u {
        // PROJ step: p_res0 is reduced scrutinee pe2
        let pe2 = p_res0;
        if word_tag(pe2) == ETAG_LIT && view_lit_kind(pe2) == 2u {
            // String literal expansion inside proj
            halt_delegate(REASON_UNMODELED);
            return;
        }
        let sn = view_proj_sn(cur);
        let idx_lo = view_proj_idx_lo(cur);
        let idx_hi = view_proj_idx_hi(cur);
        if idx_hi != 0u {
            pop_ret(cur, 0u);
            return;
        }
        let p_slot = find_proj_visible(sn);
        if p_slot == NONE_U32 {
            pop_ret(cur, 0u);
            return;
        }
        let num_params = proj_field(p_slot, 2u);
        let ctor_name = proj_field(p_slot, 3u);
        let num_fields = proj_field(p_slot, 4u);
        let tbl_lp_len = proj_field(p_slot, 8u);
        if idx_lo >= num_fields {
            pop_ret(cur, 0u);
            return;
        }
        // Check head and args of pe2
        var pargc = 0u;
        var phd = pe2;
        for (var i = 0u; i < 256u; i = i + 1u) {
            if word_tag(phd) != ETAG_APP { break; }
            phd = view_app_f(phd);
            pargc = pargc + 1u;
        }
        if word_tag(phd) != ETAG_CONST {
            pop_ret(cur, 0u);
            return;
        }
        if view_const_n(phd) != ctor_name
            || pargc != num_params + num_fields
            || ls_len(view_const_us(phd)) != tbl_lp_len
        {
            pop_ret(cur, 0u);
            return;
        }
        if hdr.verified_mode != 0u {
            let cs = find_const_visible(ctor_name);
            if cs == NONE_U32
                || const_field(cs, 0u) != CKIND_CTOR
                || pargc != const_field(cs, 9u) + const_field(cs, 10u)
            {
                pop_ret(cur, 0u);
                return;
            }
        }
        // Extract argument (num_params + idx_lo) from pe2
        let target_arg = num_params + idx_lo;
        let drops = pargc - 1u - target_arg;
        var w = pe2;
        for (var d = 0u; d < drops; d = d + 1u) {
            w = view_app_f(w);
        }
        f_write(top, 2u, view_app_a(w));
        f_write(top, 1u, 0u);
        return;
    }

    if phase == 3u {
        // Came back from whnf_core(hd)
        f_write(top, 1u, 4u);
        // Fall straight into phase 4 below!
    }

    if phase == 3u || phase == 4u {
        let hd2 = p_res0;
        let orig_hd = f_read(top, 7u);
        let buf_ptr = f_read(top, 5u);
        let argc = f_read(top, 6u);
        let args_ptr = buf_ptr;
        let nodes_ptr = buf_ptr + argc;

        if word_tag(hd2) == ETAG_LAM {
            // Batched beta reduction: peel min(argc, lambda chain length)
            var bcount = 0u;
            var body = hd2;
            for (var k = 0u; k < argc; k = k + 1u) {
                if word_tag(body) != ETAG_LAM { break; }
                body = view_bind_body(body);
                bcount = bcount + 1u;
            }
            f_write(top, 7u, bcount);
            req_call(5u, OP_INST_REV, body, args_ptr, bcount, 0u);
            return;
        }

        // Check iota reduction if head is Const RecInfo
        if word_tag(hd2) == ETAG_CONST {
            let cname = view_const_n(hd2);
            let cus = view_const_us(hd2);
            let cslot = find_const_visible(cname);
            if cslot != NONE_U32 && const_field(cslot, 0u) == CKIND_REC {
                let rec_lp_len = const_field(cslot, 5u);
                let major_idx = const_field(cslot, 9u);
                let rec_flags = const_field(cslot, 8u);
                if (rec_flags & 16u) != 0u
                    && ls_len(cus) == rec_lp_len
                    && argc >= major_idx + 1u
                {
                    let maj0 = s_read(args_ptr + major_idx);
                    f_write(top, 7u, hd2);
                    if (rec_flags & 4u) != 0u {
                        // is_k recursor: try raw maj0 directly in phase 6 without WHNF; delegates cleanly if rescue/reduction is needed.
                        p_res0 = maj0;
                        f_write(top, 1u, 6u);
                        return;
                    }
                    // Reduce major premise with full whnf:
                    req_call(6u, OP_WHNF, maj0, depth, 0u, 0u);
                    return;
                }
            }
        }

        // Neither beta nor iota: return rebuilt stuck application!
        let r = mk_app_slice_rebuilt(hd2, hd2 == orig_hd, args_ptr, nodes_ptr, argc);
        if p_halt != 0u { return; }
        pop_ret(r, 0u);
        return;
    }

    if phase == 5u {
        // Beta subst_rev completed
        let buf_ptr = f_read(top, 5u);
        let argc = f_read(top, 6u);
        let bcount = f_read(top, 7u);
        let e_next = mk_app_slice(p_res0, buf_ptr, bcount, argc);
        if p_halt != 0u { return; }
        f_write(top, 2u, e_next);
        f_write(top, 1u, 0u);
        return;
    }

    if phase == 6u {
        // Iota: p_res0 is whnf(major) (or raw major for is_k).
        var maj = p_res0;
        let hd2 = f_read(top, 7u);
        let buf_ptr = f_read(top, 5u);
        let argc = f_read(top, 6u);
        let args_ptr = buf_ptr;
        let rec_slot = find_const_visible(view_const_n(hd2));
        let rec_flags = const_field(rec_slot, 8u);
        let is_k = (rec_flags & 4u) != 0u;

        if word_tag(maj) == ETAG_LIT {
            if !is_k && view_lit_kind(maj) <= 1u && p_nat_ok {
                maj = nat_lit_to_ctor(maj);
                if p_halt != 0u { return; }
            } else {
                // StringLit, missing Nat, oversized BigNat, or raw is_k literal rescue
                if is_k || view_lit_kind(maj) > 1u {
                    halt_delegate(REASON_UNMODELED);
                    return;
                }
            }
        }

        // Match maj head & args against rec rules
        var m_argc = 0u;
        var m_hd = maj;
        for (var i = 0u; i < 128u; i = i + 1u) {
            if word_tag(m_hd) != ETAG_APP { break; }
            m_hd = view_app_f(m_hd);
            m_argc = m_argc + 1u;
        }
        let rec_us = view_const_us(hd2);
        let major_idx = const_field(rec_slot, 9u);
        let n_params_plus = const_field(rec_slot, 10u);
        let rules_off = const_field(rec_slot, 11u);
        let rules_len = const_field(rec_slot, 12u);

        var matched_rule = NONE_U32;
        if word_tag(m_hd) == ETAG_CONST {
            let m_ctor = view_const_n(m_hd);
            for (var r = 0u; r < rules_len; r = r + 1u) {
                if rec_rule_field(rules_off + r, 0u) == m_ctor {
                    matched_rule = rules_off + r;
                    break;
                }
            }
        }

        if matched_rule == NONE_U32 {
            if is_k {
                halt_delegate(REASON_UNMODELED);
                return;
            }
            if rules_len == 1u {
                let r0_ctor = rec_rule_field(rules_off, 0u);
                let cs0 = find_const_visible(r0_ctor);
                if cs0 != NONE_U32 && const_field(cs0, 0u) == CKIND_CTOR {
                    let is0 = find_const_visible(const_field(cs0, 11u));
                    if (is0 != NONE_U32 && (const_field(is0, 8u) & 1u) != 0u)
                        || (const_field(rec_slot, 14u) & 16u) != 0u
                    {
                        halt_delegate(REASON_UNMODELED);
                        return;
                    }
                }
            }
            // Iota did not fire: rebuild application via shared phase 65.
            f_write(top, 1u, 65u);
            return;
        }

        let fire_kind = rec_rule_field(matched_rule, 2u);
        let r_nfields = rec_rule_field(matched_rule, 1u);
        let r_rhs = rec_rule_field(matched_rule, 3u);
        let f_off = rec_rule_field(matched_rule, 4u);
        let f_len_raw = rec_rule_field(matched_rule, 5u);
        let ctor_slot = find_const_visible(rec_rule_field(matched_rule, 0u));
        if ctor_slot == NONE_U32 || const_field(ctor_slot, 0u) != CKIND_CTOR {
            if is_k { halt_delegate(REASON_UNMODELED); return; }
            f_write(top, 1u, 65u);
            return;
        }
        let c_np = const_field(ctor_slot, 9u);
        let c_nf = const_field(ctor_slot, 10u);
        if m_argc != c_np + c_nf || c_nf != r_nfields {
            if is_k { halt_delegate(REASON_UNMODELED); return; }
            f_write(top, 1u, 65u);
            return;
        }

        let c_ind = const_field(ctor_slot, 11u);
        let ind_slot = find_const_visible(c_ind);
        var fire_lp_count = const_field(ctor_slot, 5u);
        if fire_kind == 1u {
            fire_lp_count = f_len_raw;
        } else if fire_kind == 2u {
            fire_lp_count = f_len_raw & 0xFFFFu;
        }

        var no_cert = (hdr.verified_mode == 0u) || is_k;
        if !no_cert && ind_slot != NONE_U32 && const_field(ind_slot, 0u) == CKIND_IND {
            let ind_never_zero = (const_field(ind_slot, 8u) & 2u) != 0u;
            let ind_lp_len = const_field(ind_slot, 5u);
            if ind_never_zero && ind_lp_len == fire_lp_count {
                no_cert = true;
            }
        }

        let rec_lp_off = const_field(rec_slot, 4u);
        let rec_lp_len = const_field(rec_slot, 5u);

        if no_cert {
            let aux_ptr = s_alloc(3u);
            if p_halt != 0u { return; }
            s_write(aux_ptr, maj);
            s_write(aux_ptr + 1u, rec_slot);
            s_write(aux_ptr + 2u, matched_rule);
            f_write(top, 7u, aux_ptr);
            req_call(7u, OP_INST_LP, r_rhs, rec_lp_off, rec_lp_len, rec_us);
            return;
        }

        // Not `iota_no_cert`: check `iota_case3_at` (Cases 1/2 skip cert; Case 3 runs cert).
        if fire_kind == 2u
            || ind_slot == NONE_U32
            || const_field(ind_slot, 0u) != CKIND_IND
            || fire_lp_count > 16u
        {
            halt_delegate(REASON_UNMODELED);
            return;
        }

        let cmp_ls = s_alloc(2u + fire_lp_count);
        if p_halt != 0u { return; }
        let aux_nz = s_alloc(11u);
        if p_halt != 0u { return; }
        s_write(aux_nz, maj);
        s_write(aux_nz + 1u, rec_slot);
        s_write(aux_nz + 2u, matched_rule);
        s_write(aux_nz + 3u, hd2);
        s_write(aux_nz + 4u, cmp_ls);
        s_write(aux_nz + 5u, fire_lp_count);
        s_write(aux_nz + 6u, 0u);
        s_write(aux_nz + 7u, 0u);
        s_write(aux_nz + 8u, m_hd);
        s_write(aux_nz + 9u, m_argc);
        s_write(aux_nz + 10u, c_np);
        f_write(top, 7u, aux_nz);

        if fire_kind == 0u {
            var any_hp = 0u;
            var bad_map = false;
            let ctor_lp_off = const_field(ctor_slot, 4u);
            for (var j = 0u; j < fire_lp_count; j = j + 1u) {
                let target_nm = env_nidx_item(ctor_lp_off, j);
                var matched_k = NONE_U32;
                for (var k = 0u; k < rec_lp_len; k = k + 1u) {
                    if env_nidx_item(rec_lp_off, k) == target_nm {
                        matched_k = k;
                        break;
                    }
                }
                if matched_k == NONE_U32 {
                    bad_map = true;
                    break;
                }
                let lv = ls_item(rec_us, matched_k);
                if l_has_param(lv) { any_hp = 1u; }
                s_write(cmp_ls + 2u + j, lv);
            }
            if bad_map {
                halt_delegate(REASON_UNMODELED);
                return;
            }
            s_write(cmp_ls, any_hp);
            s_write(cmp_ls + 1u, fire_lp_count);
            f_write(top, 1u, 57u);
            return;
        }
        f_write(top, 1u, 56u);
        return;
    }

    if phase == 56u {
        let aux_nz = f_read(top, 7u);
        let cmp_ls = s_read(aux_nz + 4u);
        let fire_lp_count = s_read(aux_nz + 5u);
        let j = s_read(aux_nz + 6u);
        if j >= fire_lp_count {
            s_write(cmp_ls, s_read(aux_nz + 7u));
            s_write(cmp_ls + 1u, fire_lp_count);
            f_write(top, 1u, 57u);
            return;
        }
        let rec_slot = s_read(aux_nz + 1u);
        let matched_rule = s_read(aux_nz + 2u);
        let hd2 = s_read(aux_nz + 3u);
        let f_off = rec_rule_field(matched_rule, 4u);
        let orig_lv = env_tables[hdr.off_rec_fire + f_off + j];
        let sort_orig = intern_s_sort(orig_lv);
        if p_halt != 0u { return; }
        req_call(560u, OP_INST_LP, sort_orig, const_field(rec_slot, 4u), const_field(rec_slot, 5u), view_const_us(hd2));
        return;
    }

    if phase == 560u {
        let aux_nz = f_read(top, 7u);
        let cmp_ls = s_read(aux_nz + 4u);
        let j = s_read(aux_nz + 6u);
        let lv = view_sort_u(p_res0);
        if l_has_param(lv) {
            s_write(aux_nz + 7u, 1u);
        }
        s_write(cmp_ls + 2u + j, lv);
        s_write(aux_nz + 6u, j + 1u);
        f_write(top, 1u, 56u);
        return;
    }

    if phase == 57u {
        let aux_nz = f_read(top, 7u);
        let matched_rule = s_read(aux_nz + 2u);
        let cmp_ls = s_read(aux_nz + 4u);
        let fire_lp_count = s_read(aux_nz + 5u);
        let ctor_slot = find_const_visible(rec_rule_field(matched_rule, 0u));
        let ind_slot = find_const_visible(const_field(ctor_slot, 11u));
        let ind_lp_off = const_field(ind_slot, 4u);
        let ind_lp_len = const_field(ind_slot, 5u);
        var res_ty = const_field(ind_slot, 2u);
        for (var k = 0u; k < 64u; k = k + 1u) {
            if word_tag(res_ty) != ETAG_FORALL_E { break; }
            res_ty = view_bind_body(res_ty);
        }
        if word_tag(res_ty) == ETAG_SORT && ind_lp_len == fire_lp_count {
            let cmp_lvls = word_mk_s(0u, cmp_ls);
            req_call(58u, OP_INST_LP, res_ty, ind_lp_off, ind_lp_len, cmp_lvls);
            return;
        }
        f_write(top, 1u, 580u);
        return;
    }

    if phase == 58u {
        let aux_nz = f_read(top, 7u);
        let nz = level_is_never_zero(view_sort_u(p_res0));
        if nz == 2u {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        if nz == 1u {
            let rec_slot = s_read(aux_nz + 1u);
            let matched_rule = s_read(aux_nz + 2u);
            let hd2 = s_read(aux_nz + 3u);
            let r_rhs = rec_rule_field(matched_rule, 3u);
            req_call(7u, OP_INST_LP, r_rhs, const_field(rec_slot, 4u), const_field(rec_slot, 5u), view_const_us(hd2));
            return;
        }
        f_write(top, 1u, 580u);
        return;
    }

    if phase == 580u {
        let aux_nz = f_read(top, 7u);
        let maj = s_read(aux_nz);
        let rec_slot = s_read(aux_nz + 1u);
        let matched_rule = s_read(aux_nz + 2u);
        let hd2 = s_read(aux_nz + 3u);
        let cmp_ls = s_read(aux_nz + 4u);
        let fire_lp_count = s_read(aux_nz + 5u);
        let m_hd = s_read(aux_nz + 8u);
        let m_argc = s_read(aux_nz + 9u);
        let c_np = s_read(aux_nz + 10u);
        let major_idx = const_field(rec_slot, 9u);
        let n_params_plus = const_field(rec_slot, 10u);
        let ctor_slot = find_const_visible(rec_rule_field(matched_rule, 0u));

        // Case 3: handle full verification natively when `major_idx == n_params_plus` (no index cert needed, covers Quot.lift/Quot.ind/And/Or/Exists/False).
        if major_idx != n_params_plus || m_argc > 32u || fire_lp_count != const_field(ctor_slot, 5u) {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        let usj = view_const_us(m_hd);
        if ls_len(usj) != fire_lp_count {
            f_write(top, 7u, hd2);
            f_write(top, 1u, 65u);
            return;
        }

        let c3_ptr = s_alloc(9u + m_argc);
        if p_halt != 0u { return; }
        s_write(c3_ptr, maj);
        s_write(c3_ptr + 1u, rec_slot);
        s_write(c3_ptr + 2u, matched_rule);
        s_write(c3_ptr + 3u, hd2);
        s_write(c3_ptr + 4u, c_np);
        s_write(c3_ptr + 5u, m_argc);
        s_write(c3_ptr + 6u, 0u);
        s_write(c3_ptr + 7u, 0u);
        s_write(c3_ptr + 8u, usj);
        var mw = maj;
        for (var i = 0u; i < m_argc; i = i + 1u) {
            s_write(c3_ptr + 9u + (m_argc - 1u - i), view_app_a(mw));
            mw = view_app_f(mw);
        }
        f_write(top, 7u, c3_ptr);
        req_call(59u, OP_LEVEL_CMP, 1u, usj, word_mk_s(0u, cmp_ls), 0u);
        return;
    }

    if phase == 59u {
        let c3_ptr = f_read(top, 7u);
        let hd2 = s_read(c3_ptr + 3u);
        let buf_ptr = f_read(top, 5u);
        if p_res0 == 0u {
            f_write(top, 7u, hd2);
            f_write(top, 1u, 65u);
            return;
        }
        let c_np = s_read(c3_ptr + 4u);
        if c_np > 0u {
            req_call(60u, OP_DEFEQ, s_read(c3_ptr + 9u), s_read(buf_ptr), depth, 0u);
        } else {
            let matched_rule = s_read(c3_ptr + 2u);
            let ctor_slot = find_const_visible(rec_rule_field(matched_rule, 0u));
            let usj = s_read(c3_ptr + 8u);
            req_call(61u, OP_INST_LP, const_field(ctor_slot, 2u), const_field(ctor_slot, 4u), const_field(ctor_slot, 5u), usj);
        }
        return;
    }

    if phase == 60u {
        // Case 3 param defeq loop
        let c3_ptr = f_read(top, 7u);
        let hd2 = s_read(c3_ptr + 3u);
        let buf_ptr = f_read(top, 5u);
        if p_res0 == 0u {
            f_write(top, 7u, hd2);
            f_write(top, 1u, 65u);
            return;
        }
        let next_i = s_read(c3_ptr + 7u) + 1u;
        let c_np = s_read(c3_ptr + 4u);
        if next_i < c_np {
            s_write(c3_ptr + 7u, next_i);
            req_call(60u, OP_DEFEQ, s_read(c3_ptr + 9u + next_i), s_read(buf_ptr + next_i), depth, 0u);
            return;
        }
        let matched_rule = s_read(c3_ptr + 2u);
        let ctor_slot = find_const_visible(rec_rule_field(matched_rule, 0u));
        let usj = s_read(c3_ptr + 8u);
        s_write(c3_ptr + 7u, 0u);
        req_call(61u, OP_INST_LP, const_field(ctor_slot, 2u), const_field(ctor_slot, 4u), const_field(ctor_slot, 5u), usj);
        return;
    }

    if phase == 61u {
        // Case 3 iota_certs_full loop
        let c3_ptr = f_read(top, 7u);
        let cur_ty = p_res0;
        let idx = s_read(c3_ptr + 7u);
        let m_argc = s_read(c3_ptr + 5u);
        let hd2 = s_read(c3_ptr + 3u);
        if idx >= m_argc {
            let rec_slot = s_read(c3_ptr + 1u);
            let matched_rule = s_read(c3_ptr + 2u);
            let r_rhs = rec_rule_field(matched_rule, 3u);
            let rec_lp_off = const_field(rec_slot, 4u);
            let rec_lp_len = const_field(rec_slot, 5u);
            req_call(7u, OP_INST_LP, r_rhs, rec_lp_off, rec_lp_len, view_const_us(hd2));
            return;
        }
        if word_tag(cur_ty) == ETAG_BVAR {
            req_call(61u, OP_INST_REV, cur_ty, c3_ptr + 9u, idx, 0u);
            return;
        }
        if word_tag(cur_ty) != ETAG_FORALL_E {
            f_write(top, 7u, hd2);
            f_write(top, 1u, 65u);
            return;
        }
        s_write(c3_ptr + 6u, cur_ty);
        req_call(62u, OP_INST_REV, view_bind_ty(cur_ty), c3_ptr + 9u, idx, 0u);
        return;
    }

    if phase == 62u {
        let c3_ptr = f_read(top, 7u);
        s_write(c3_ptr + 8u, p_res0);
        let idx = s_read(c3_ptr + 7u);
        req_call(63u, OP_INFER, s_read(c3_ptr + 9u + idx), depth, 0u, 0u);
        return;
    }

    if phase == 63u {
        let c3_ptr = f_read(top, 7u);
        let ty2 = s_read(c3_ptr + 8u);
        req_call(64u, OP_DEFEQ, p_res0, ty2, depth, 0u);
        return;
    }

    if phase == 64u {
        let c3_ptr = f_read(top, 7u);
        let hd2 = s_read(c3_ptr + 3u);
        if p_res0 == 0u {
            f_write(top, 7u, hd2);
            f_write(top, 1u, 65u);
            return;
        }
        let cur_ty = s_read(c3_ptr + 6u);
        s_write(c3_ptr + 7u, s_read(c3_ptr + 7u) + 1u);
        p_res0 = view_bind_body(cur_ty);
        f_write(top, 1u, 61u);
        return;
    }

    if phase == 65u {
        let hd2 = f_read(top, 7u);
        let buf_ptr = f_read(top, 5u);
        let argc = f_read(top, 6u);
        let r = mk_app_slice(hd2, buf_ptr, 0u, argc);
        if p_halt != 0u { return; }
        pop_ret(r, 0u);
        return;
    }

    // phase == 7u: assemble iota reduct [rhs_inst, args[0..n_params_plus], ctor_fields[m_argc - r_nfields .. m_argc], args[major_idx + 1 .. argc]]
    let aux_ptr = f_read(top, 7u);
    let maj = s_read(aux_ptr);
    let rec_slot = s_read(aux_ptr + 1u);
    let matched_rule = s_read(aux_ptr + 2u);
    let major_idx = const_field(rec_slot, 9u);
    let n_params_plus = const_field(rec_slot, 10u);
    let r_nfields = rec_rule_field(matched_rule, 1u);
    let buf_ptr = f_read(top, 5u);
    let argc = f_read(top, 6u);
    let args_ptr = buf_ptr;

    var cur_term = mk_app_slice(p_res0, args_ptr, 0u, n_params_plus);
    if p_halt != 0u { return; }
    if r_nfields > 0u {
        let fslice = s_alloc(r_nfields);
        if p_halt != 0u { return; }
        var w = maj;
        for (var i = 0u; i < r_nfields; i = i + 1u) {
            s_write(fslice + (r_nfields - 1u - i), view_app_a(w));
            w = view_app_f(w);
        }
        cur_term = mk_app_slice(cur_term, fslice, 0u, r_nfields);
        if p_halt != 0u { return; }
    }
    cur_term = mk_app_slice(cur_term, args_ptr, major_idx + 1u, argc);
    if p_halt != 0u { return; }
    f_write(top, 2u, cur_term);
    f_write(top, 1u, 0u);
}

// =========================================================================
// OP_WHNF: [2]=cur, [3]=depth, [4]=orig_e, [5]=aux0, [6]=aux1, [7]=aux2
// =========================================================================

fn exec_whnf(top: u32) {
    let phase = f_read(top, 1u);
    let cur = f_read(top, 2u);
    let depth_raw = f_read(top, 3u);
    let nat_only = (depth_raw & 0x80000000u) != 0u;
    let depth = depth_raw & 0x7FFFFFFFu;
    let orig_e = f_read(top, 4u);

    if phase == 0u {
        if !nat_only {
            let cached = lds_whnf_get(cur);
            if cached != NONE_U32 {
                if cur == orig_e {
                    pop_ret(cached, 0u);
                    return;
                }
                lds_whnf_set(orig_e, cached);
                pop_ret(cached, 0u);
                return;
            }
        }
        req_call(1u, OP_WHNF_CORE, cur, depth, 0u, 0u);
        return;
    }

    if phase == 1u {
        let e1 = p_res0;
        // Check reduce_nat on e1
        if word_tag(e1) == ETAG_APP && p_nat_ok {
            let f1 = view_app_f(e1);
            let b1 = view_app_a(e1);
            if word_tag(f1) == ETAG_CONST {
                let cn = view_const_n(f1);
                let cus = view_const_us(f1);
                let is_pred_unary = !nat_only
                    && cn == hdr.pin_nat_pred
                    && hdr.pin_nat_pred != 0u
                    && find_const_visible(hdr.pin_nat_pred) != NONE_U32
                    && ls_len(cus) == 0u;
                if (cn == hdr.pin_nat_succ && ls_len(cus) == 0u) || is_pred_unary {
                    f_write(top, 5u, e1);
                    f_write(top, 6u, cn);
                    req_call(2u, OP_WHNF, b1, depth, 0u, 0u);
                    return;
                }
            } else if word_tag(f1) == ETAG_APP {
                let g1 = view_app_f(f1);
                let a1 = view_app_a(f1);
                if word_tag(g1) == ETAG_CONST {
                    let cn = view_const_n(g1);
                    let cus = view_const_us(g1);
                    let cs = find_const_visible(cn);
                    let is_nat_op = cs != NONE_U32
                        && ((const_field(cs, 14u) & 1u) != 0u
                            || (hdr.pin_nat_pow != 0u && cn == hdr.pin_nat_pow)
                            || (hdr.pin_nat_gcd != 0u && cn == hdr.pin_nat_gcd));
                    if is_nat_op && cn != hdr.pin_nat_pred && ls_len(cus) == 0u {
                        f_write(top, 5u, e1);
                        f_write(top, 6u, cn);
                        f_write(top, 7u, b1);
                        req_call(3u, OP_WHNF, a1, depth, 0u, 0u);
                        return;
                    }
                }
            }
        }
        if nat_only {
            pop_ret(NONE_U32, 0u);
            return;
        }
        f_write(top, 5u, e1);
        f_write(top, 1u, 5u);
        return;
    }

    if phase == 2u {
        // Nat unary (succ / pred) result
        let e1 = f_read(top, 5u);
        let cn = f_read(top, 6u);
        let wb = p_res0;
        if word_tag(wb) == ETAG_LIT {
            let res = eval_nat_unary(cn, wb);
            if p_halt != 0u { return; }
            if res != NONE_U32 {
                lds_whnf_set(orig_e, res);
                pop_ret(res, 0u);
                return;
            }
        }
        if nat_only {
            pop_ret(NONE_U32, 0u);
            return;
        }
        f_write(top, 1u, 5u);
        return;
    }

    if phase == 3u {
        // Nat binary op arg0 reduced -> reduce arg1
        let wa = p_res0;
        if word_tag(wa) == ETAG_LIT {
            let ap = s_alloc(2u);
            if p_halt != 0u { return; }
            s_write(ap, f_read(top, 5u));
            s_write(ap + 1u, wa);
            f_write(top, 5u, ap);
            let b1 = f_read(top, 7u);
            req_call(4u, OP_WHNF, b1, depth, 0u, 0u);
            return;
        }
        if nat_only {
            pop_ret(NONE_U32, 0u);
            return;
        }
        f_write(top, 1u, 5u);
        return;
    }

    if phase == 4u {
        let ap = f_read(top, 5u);
        let e1 = s_read(ap);
        let wa = s_read(ap + 1u);
        let wb = p_res0;
        let cn = f_read(top, 6u);
        if word_tag(wb) == ETAG_LIT {
            let res = eval_nat_binary(cn, wa, wb);
            if p_halt != 0u { return; }
            if res != NONE_U32 {
                if word_tag(res) == ETAG_LIT || nat_only {
                    lds_whnf_set(orig_e, res);
                    pop_ret(res, 0u);
                    return;
                }
                f_write(top, 2u, res);
                f_write(top, 1u, 0u);
                return;
            }
        }
        if nat_only {
            pop_ret(NONE_U32, 0u);
            return;
        }
        f_write(top, 5u, e1);
        f_write(top, 1u, 5u);
        return;
    }

    if phase == 5u {
        // Try unfold_definition on e1
        let e1 = f_read(top, 5u);
        let cslot = head_const_slot(e1);
        if cslot == NONE_U32 {
            lds_whnf_set(orig_e, e1);
            pop_ret(e1, 0u);
            return;
        }
        // Collect spine of e1 to extract Const us + args
        var argc = 0u;
        var hd = e1;
        for (var i = 0u; i < 256u; i = i + 1u) {
            if word_tag(hd) != ETAG_APP { break; }
            hd = view_app_f(hd);
            argc = argc + 1u;
        }
        if word_tag(hd) == ETAG_APP {
            halt_delegate(REASON_UNMODELED);
            return;
        }
        let args_ptr = s_alloc(argc);
        if p_halt != 0u { return; }
        var w = e1;
        for (var j = 0u; j < argc; j = j + 1u) {
            s_write(args_ptr + (argc - 1u - j), view_app_a(w));
            w = view_app_f(w);
        }
        f_write(top, 5u, args_ptr);
        f_write(top, 6u, argc);
        let val = const_field(cslot, 3u);
        let lp_off = const_field(cslot, 4u);
        let lp_len = const_field(cslot, 5u);
        let cus = view_const_us(hd);
        req_call(6u, OP_INST_LP, val, lp_off, lp_len, cus);
        return;
    }

    // phase == 6u: unfolded head ready in p_res0
    let args_ptr = f_read(top, 5u);
    let argc = f_read(top, 6u);
    let next_e = mk_app_slice(p_res0, args_ptr, 0u, argc);
    if p_halt != 0u { return; }
    f_write(top, 2u, next_e);
    f_write(top, 1u, 0u);
}

