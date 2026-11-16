// Exact multi-limb u32 GPU batch Nat arithmetic kernel (Pipeline B).
// ZERO f32/f64 and ZERO u64/SHADER_INT64 instructions; pure u32/vec2<u32> math.

struct BignumHeader {
    num_tasks: u32,
    in_stride: u32,
    out_stride: u32,
    pad0: u32,
}

struct BignumTask {
    op: u32,      // 0=Add, 1=Sub (saturating Nat.sub), 2=Mul, 3=Cmp, 4=Beq, 5=Ble
    a_len: u32,   // active u32 limbs of A
    b_len: u32,   // active u32 limbs of B
    flags: u32,
}

struct BignumResultMeta {
    out_len: u32,
    cmp_res: u32,   // 0=Lt, 1=Eq, 2=Gt
    bool_res: u32,  // 0/1
    overflow: u32,  // 1 if result exceeded out_stride (or Nat.sub underflowed when bit 0 wanted)
}

@group(0) @binding(0) var<uniform> hdr: BignumHeader;
@group(0) @binding(1) var<storage, read> tasks: array<BignumTask>;
@group(0) @binding(2) var<storage, read> a_limbs: array<u32>;
@group(0) @binding(3) var<storage, read> b_limbs: array<u32>;
@group(0) @binding(4) var<storage, read_write> out_limbs: array<u32>;
@group(0) @binding(5) var<storage, read_write> out_meta: array<BignumResultMeta>;

const OP_ADD: u32 = 0u;
const OP_SUB: u32 = 1u;
const OP_MUL: u32 = 2u;
const OP_CMP: u32 = 3u;
const OP_BEQ: u32 = 4u;
const OP_BLE: u32 = 5u;

// Exact 32x32 -> (lo, hi) using 16-bit half-limbs; mathematically overflow-free in u32.
fn mul32_wide(a: u32, b: u32) -> vec2<u32> {
    let a0 = a & 0xFFFFu;
    let a1 = a >> 16u;
    let b0 = b & 0xFFFFu;
    let b1 = b >> 16u;

    let p00 = a0 * b0;
    let p01 = a0 * b1;
    let p10 = a1 * b0;
    let p11 = a1 * b1;

    let mid = (p00 >> 16u) + (p01 & 0xFFFFu) + (p10 & 0xFFFFu);
    let lo = (p00 & 0xFFFFu) | ((mid & 0xFFFFu) << 16u);
    let hi = p11 + (p01 >> 16u) + (p10 >> 16u) + (mid >> 16u);
    return vec2<u32>(lo, hi);
}

fn trim_len_a(base: u32, len_in: u32) -> u32 {
    var l = min(len_in, hdr.in_stride);
    while l > 0u {
        if a_limbs[base + l - 1u] != 0u {
            break;
        }
        l -= 1u;
    }
    return l;
}

fn trim_len_b(base: u32, len_in: u32) -> u32 {
    var l = min(len_in, hdr.in_stride);
    while l > 0u {
        if b_limbs[base + l - 1u] != 0u {
            break;
        }
        l -= 1u;
    }
    return l;
}

fn trim_len_out(base: u32, max_len: u32) -> u32 {
    var l = max_len;
    while l > 0u {
        if out_limbs[base + l - 1u] != 0u {
            break;
        }
        l -= 1u;
    }
    return l;
}

fn cmp_limbs(a_base: u32, alen: u32, b_base: u32, blen: u32) -> u32 {
    if alen < blen {
        return 0u;
    }
    if alen > blen {
        return 2u;
    }
    var i = alen;
    while i > 0u {
        i -= 1u;
        let av = a_limbs[a_base + i];
        let bv = b_limbs[b_base + i];
        if av < bv {
            return 0u;
        }
        if av > bv {
            return 2u;
        }
    }
    return 1u;
}

@compute @workgroup_size(64)
fn main(@builtin(global_invocation_id) gid: vec3<u32>) {
    let tid = gid.x;
    if tid >= hdr.num_tasks {
        return;
    }

    let t = tasks[tid];
    let a_base = tid * hdr.in_stride;
    let b_base = tid * hdr.in_stride;
    let o_base = tid * hdr.out_stride;

    for (var z = 0u; z < hdr.out_stride; z += 1u) {
        out_limbs[o_base + z] = 0u;
    }

    let alen = trim_len_a(a_base, t.a_len);
    let blen = trim_len_b(b_base, t.b_len);
    let c = cmp_limbs(a_base, alen, b_base, blen);

    var out_len = 0u;
    var bool_res = 0u;
    var overflow = 0u;

    if t.op == OP_CMP {
        bool_res = select(0u, 1u, c == 1u);
    } else if t.op == OP_BEQ {
        bool_res = select(0u, 1u, c == 1u);
    } else if t.op == OP_BLE {
        bool_res = select(0u, 1u, c <= 1u);
    } else if t.op == OP_ADD {
        let max_ab = max(alen, blen);
        var carry = 0u;
        let lim = min(max_ab + 1u, hdr.out_stride);
        for (var i = 0u; i < lim; i += 1u) {
            let av = select(0u, a_limbs[a_base + i], i < alen);
            let bv = select(0u, b_limbs[b_base + i], i < blen);
            let s1 = av + bv;
            let c1 = select(0u, 1u, s1 < av);
            let s2 = s1 + carry;
            let c2 = select(0u, 1u, s2 < s1);
            out_limbs[o_base + i] = s2;
            carry = c1 + c2;
        }
        if (max_ab >= hdr.out_stride && carry != 0u) || (max_ab + 1u > hdr.out_stride && (alen > hdr.out_stride || blen > hdr.out_stride)) {
            overflow = 1u;
        }
        if carry != 0u && max_ab + 1u > hdr.out_stride {
            overflow = 1u;
        }
        out_len = trim_len_out(o_base, hdr.out_stride);
    } else if t.op == OP_SUB {
        if c == 0u {
            // Lean Nat.sub returns 0 when a < b.
            out_len = 0u;
        } else {
            var borrow = 0u;
            let lim = min(alen, hdr.out_stride);
            for (var i = 0u; i < lim; i += 1u) {
                let av = a_limbs[a_base + i];
                let bv = select(0u, b_limbs[b_base + i], i < blen);
                let sub_b = bv + borrow;
                let ov_b = select(0u, 1u, sub_b < bv);
                let new_borrow = select(0u, 1u, ov_b != 0u || av < sub_b);
                let diff = av - sub_b;
                out_limbs[o_base + i] = diff;
                borrow = new_borrow;
            }
            if alen > hdr.out_stride {
                overflow = 1u;
            }
            out_len = trim_len_out(o_base, hdr.out_stride);
        }
    } else if t.op == OP_MUL {
        if alen == 0u || blen == 0u {
            out_len = 0u;
        } else {
            for (var i = 0u; i < alen; i += 1u) {
                let av = a_limbs[a_base + i];
                var carry = 0u;
                for (var j = 0u; j < blen; j += 1u) {
                    let k = i + j;
                    let prod = mul32_wide(av, b_limbs[b_base + j]);
                    let lo1 = prod.x + carry;
                    let c1 = select(0u, 1u, lo1 < prod.x);
                    if k < hdr.out_stride {
                        let cur = out_limbs[o_base + k];
                        let sum = cur + lo1;
                        let c2 = select(0u, 1u, sum < cur);
                        out_limbs[o_base + k] = sum;
                        carry = prod.y + c1 + c2;
                    } else {
                        if lo1 != 0u || prod.y != 0u {
                            overflow = 1u;
                        }
                        carry = prod.y + c1;
                    }
                }
                var idx = i + blen;
                while carry != 0u {
                    if idx < hdr.out_stride {
                        let cur = out_limbs[o_base + idx];
                        let sum = cur + carry;
                        let c2 = select(0u, 1u, sum < cur);
                        out_limbs[o_base + idx] = sum;
                        carry = c2;
                        idx += 1u;
                    } else {
                        overflow = 1u;
                        carry = 0u;
                    }
                }
            }
            out_len = trim_len_out(o_base, hdr.out_stride);
        }
    }

    out_meta[tid] = BignumResultMeta(out_len, c, bool_res, overflow);
}
