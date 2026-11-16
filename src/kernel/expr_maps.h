/*
Copyright (c) 2013 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <cstdint>
#include <functional>
#include <vector>
#include "runtime/hash.h"
#include "util/alloc.h"
#include "kernel/expr.h"
#include "kernel/expr_eq_fn.h"

namespace lean {
// Maps based on structural equality. That is, two keys are equal iff they are structurally equal
template<typename T>
using expr_map = typename lean::unordered_map<expr, T, expr_hash, std::equal_to<expr>>;

namespace detail {
inline uint32_t mix_expr_hash32(uint32_t x) {
    x ^= x >> 16;
    x *= 0x85ebca6bu;
    x ^= x >> 13;
    x *= 0xc2b2ae35u;
    x ^= x >> 16;
    return x;
}

inline uint32_t hash_expr_pair32(uint32_t h1, uint32_t h2) {
    uint64_t combined = hash(static_cast<uint64_t>(h1), static_cast<uint64_t>(h2));
    return mix_expr_hash32(static_cast<uint32_t>(combined ^ (combined >> 32)));
}
} // namespace detail

/** \brief Flat open-addressed expression cache retaining backing storage across resets via O(|used|) generation stamping. */
class flat_expr_cache {
    static constexpr size_t INIT_CAP = 128;
    static constexpr size_t MAX_RETAINED_CAP = 32768;
    static constexpr size_t RETAINED_SHRINK_CAP = 1024;
    struct slot {
        uint32_t      m_gen{0};
        uint32_t      m_hash{0};
        lean_object * m_key{nullptr};
        lean_object * m_val{nullptr};
    };
    std::vector<slot>     m_slots;
    std::vector<uint32_t> m_used;
    uint32_t              m_gen{1};

    void clear_entries() {
        for (uint32_t idx : m_used) {
            slot & s = m_slots[idx];
            lean_dec(s.m_key);
            lean_dec(s.m_val);
            s.m_key = nullptr;
            s.m_val = nullptr;
            s.m_gen = 0;
        }
        m_used.clear();
    }

    void rehash(size_t new_cap) {
        std::vector<slot> new_slots(new_cap);
        std::vector<uint32_t> new_used;
        new_used.reserve(m_used.size());
        size_t const mask = new_cap - 1;
        uint32_t const gen = m_gen;
        for (uint32_t old_idx : m_used) {
            slot const & src = m_slots[old_idx];
            size_t idx = static_cast<size_t>(detail::mix_expr_hash32(src.m_hash)) & mask;
            while (new_slots[idx].m_gen == gen) {
                idx = (idx + 1) & mask;
            }
            new_slots[idx] = src;
            new_used.push_back(static_cast<uint32_t>(idx));
        }
        m_slots.swap(new_slots);
        m_used.swap(new_used);
    }
public:
    flat_expr_cache(): m_slots(INIT_CAP) {}
    ~flat_expr_cache() { clear_entries(); }
    flat_expr_cache(flat_expr_cache const &) = delete;
    flat_expr_cache & operator=(flat_expr_cache const &) = delete;

    void reset() {
        clear_entries();
        if (m_slots.size() > MAX_RETAINED_CAP) {
            std::vector<slot>(RETAINED_SHRINK_CAP).swap(m_slots);
            std::vector<uint32_t>().swap(m_used);
        }
        if (++m_gen == 0) {
            m_gen = 1;
        }
    }

    /** \brief Return borrowed cached value or `nullptr` if absent. */
    lean_object * find(expr const & k) const {
        uint32_t const h = hash(k);
        uint32_t const gen = m_gen;
        size_t const mask = m_slots.size() - 1;
        size_t idx = static_cast<size_t>(detail::mix_expr_hash32(h)) & mask;
        lean_object * const k_raw = k.raw();
        while (true) {
            slot const & s = m_slots[idx];
            if (s.m_gen != gen)
                return nullptr;
            if (s.m_hash == h && (s.m_key == k_raw || is_equal_raw(s.m_key, k_raw)))
                return s.m_val;
            idx = (idx + 1) & mask;
        }
    }

    void insert(expr const & k, expr const & v) {
        if ((m_used.size() + 1) * 10 > m_slots.size() * 7) {
            rehash(m_slots.size() * 2);
        }
        uint32_t const h = hash(k);
        uint32_t const gen = m_gen;
        size_t const mask = m_slots.size() - 1;
        size_t idx = static_cast<size_t>(detail::mix_expr_hash32(h)) & mask;
        lean_object * const k_raw = k.raw();
        while (true) {
            slot & s = m_slots[idx];
            if (s.m_gen != gen) {
                lean_assert(s.m_key == nullptr && s.m_val == nullptr);
                lean_object * v_raw = v.raw();
                lean_inc(k_raw);
                lean_inc(v_raw);
                s.m_gen = gen;
                s.m_hash = h;
                s.m_key = k_raw;
                s.m_val = v_raw;
                m_used.push_back(static_cast<uint32_t>(idx));
                return;
            }
            if (s.m_hash == h && (s.m_key == k_raw || is_equal_raw(s.m_key, k_raw))) {
                return;
            }
            idx = (idx + 1) & mask;
        }
    }
};

/** \brief Flat open-addressed cache for ordered pairs of expressions. */
class flat_expr_pair_cache {
    static constexpr size_t INIT_CAP = 128;
    static constexpr size_t MAX_RETAINED_CAP = 32768;
    static constexpr size_t RETAINED_SHRINK_CAP = 1024;
    struct pair_slot {
        uint32_t      m_gen{0};
        uint32_t      m_hash{0};
        uint32_t      m_hash1{0};
        uint32_t      m_hash2{0};
        lean_object * m_first{nullptr};
        lean_object * m_second{nullptr};
    };
    std::vector<pair_slot> m_slots;
    std::vector<uint32_t>  m_used;
    uint32_t               m_gen{1};

    void clear_entries() {
        for (uint32_t idx : m_used) {
            pair_slot & s = m_slots[idx];
            lean_dec(s.m_first);
            lean_dec(s.m_second);
            s.m_first = nullptr;
            s.m_second = nullptr;
            s.m_gen = 0;
        }
        m_used.clear();
    }

    void rehash(size_t new_cap) {
        std::vector<pair_slot> new_slots(new_cap);
        std::vector<uint32_t> new_used;
        new_used.reserve(m_used.size());
        size_t const mask = new_cap - 1;
        uint32_t const gen = m_gen;
        for (uint32_t old_idx : m_used) {
            pair_slot const & src = m_slots[old_idx];
            size_t idx = static_cast<size_t>(src.m_hash) & mask;
            while (new_slots[idx].m_gen == gen) {
                idx = (idx + 1) & mask;
            }
            new_slots[idx] = src;
            new_used.push_back(static_cast<uint32_t>(idx));
        }
        m_slots.swap(new_slots);
        m_used.swap(new_used);
    }
public:
    flat_expr_pair_cache(): m_slots(INIT_CAP) {}
    ~flat_expr_pair_cache() { clear_entries(); }
    flat_expr_pair_cache(flat_expr_pair_cache const &) = delete;
    flat_expr_pair_cache & operator=(flat_expr_pair_cache const &) = delete;

    void reset() {
        clear_entries();
        if (m_slots.size() > MAX_RETAINED_CAP) {
            std::vector<pair_slot>(RETAINED_SHRINK_CAP).swap(m_slots);
            std::vector<uint32_t>().swap(m_used);
        }
        if (++m_gen == 0) {
            m_gen = 1;
        }
    }

    bool contains(expr const & a, expr const & b) const {
        uint32_t const h1 = hash(a);
        uint32_t const h2 = hash(b);
        uint32_t const h = detail::hash_expr_pair32(h1, h2);
        uint32_t const gen = m_gen;
        size_t const mask = m_slots.size() - 1;
        size_t idx = static_cast<size_t>(h) & mask;
        lean_object * const a_raw = a.raw();
        lean_object * const b_raw = b.raw();
        while (true) {
            pair_slot const & s = m_slots[idx];
            if (s.m_gen != gen)
                return false;
            if (s.m_hash1 == h1 && s.m_hash2 == h2 &&
                (s.m_first == a_raw || is_equal_raw(s.m_first, a_raw)) &&
                (s.m_second == b_raw || is_equal_raw(s.m_second, b_raw)))
                return true;
            idx = (idx + 1) & mask;
        }
    }

    void insert(expr const & a, expr const & b) {
        if ((m_used.size() + 1) * 10 > m_slots.size() * 7) {
            rehash(m_slots.size() * 2);
        }
        uint32_t const h1 = hash(a);
        uint32_t const h2 = hash(b);
        uint32_t const h = detail::hash_expr_pair32(h1, h2);
        uint32_t const gen = m_gen;
        size_t const mask = m_slots.size() - 1;
        size_t idx = static_cast<size_t>(h) & mask;
        lean_object * const a_raw = a.raw();
        lean_object * const b_raw = b.raw();
        while (true) {
            pair_slot & s = m_slots[idx];
            if (s.m_gen != gen) {
                lean_assert(s.m_first == nullptr && s.m_second == nullptr);
                lean_inc(a_raw);
                lean_inc(b_raw);
                s.m_gen = gen;
                s.m_hash = h;
                s.m_hash1 = h1;
                s.m_hash2 = h2;
                s.m_first = a_raw;
                s.m_second = b_raw;
                m_used.push_back(static_cast<uint32_t>(idx));
                return;
            }
            if (s.m_hash1 == h1 && s.m_hash2 == h2 &&
                (s.m_first == a_raw || is_equal_raw(s.m_first, a_raw)) &&
                (s.m_second == b_raw || is_equal_raw(s.m_second, b_raw))) {
                return;
            }
            idx = (idx + 1) & mask;
        }
    }
};
};
