/*
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#include <algorithm>
#include <cstdint>
#include <mutex>
#include <string>
#include <vector>
#include <cstring>
#include <lean/lean.h>
#include "runtime/hash.h"
#include "runtime/compact.h"
#include "runtime/exception.h"
#include "util/alloc.h"

#ifdef LEAN_WINDOWS
#include <windows.h>  // must precede <psapi.h>: it relies on `WINBOOL`/`DWORD`/`WINAPI` from here
#include <psapi.h>
#else
#include <sys/mman.h>
#include <dlfcn.h>
#endif

#ifdef __APPLE__
#include <mach-o/dyld.h>
#include <mach-o/getsect.h>
#elif !defined(LEAN_WINDOWS)
#include <link.h>
#endif

#define LEAN_COMPACTOR_INIT_SZ 1024*1024

// uncomment to track the number of each kind of object in an .olean file
// #define LEAN_TAG_COUNTERS

namespace lean {

namespace {
constexpr size_t g_compactor_table_init_cap = 4096;

inline size_t hash_obj_ptr(object * o) {
    // Shift out 8-byte alignment zeros before Fibonacci hashing so low bits mix well.
    size_t x = reinterpret_cast<size_t>(o) >> 3;
    if constexpr (sizeof(size_t) >= 8) {
        x *= 11400714819323198485ULL;
        return x ^ (x >> 32);
    } else {
        x *= 2654435761U;
        return x ^ (x >> 16);
    }
}

inline uint32_t hash_compacted_bytes(void const * data, size_t sz) {
    uint8_t const * p = static_cast<uint8_t const *>(data);
    uint64_t h = 0x9e3779b97f4a7c15ULL ^ (static_cast<uint64_t>(sz) * 0xbf58476d1ce4e5b9ULL);
    size_t n_words = sz / 8;
    for (size_t i = 0; i < n_words; i++) {
        uint64_t w;
        memcpy(&w, p + i * 8, 8);
        w *= 0xc6a4a7935bd1e995ULL;
        w ^= w >> 47;
        w *= 0xc6a4a7935bd1e995ULL;
        h ^= w;
        h *= 0xc6a4a7935bd1e995ULL;
    }
    size_t rem = sz & 7;
    if (rem != 0) {
        uint64_t tail = 0;
        memcpy(&tail, p + n_words * 8, rem);
        tail *= 0xc6a4a7935bd1e995ULL;
        tail ^= tail >> 47;
        h ^= tail;
        h *= 0xc6a4a7935bd1e995ULL;
    }
    h ^= h >> 33;
    h *= 0xff51afd7ed558ccdULL;
    h ^= h >> 33;
    uint32_t h32 = static_cast<uint32_t>(h ^ (h >> 32));
    return h32 == 0 ? 1u : h32;
}

#if !defined(LEAN_WINDOWS) && !defined(__APPLE__)
struct loaded_libs_sig {
    size_t count = 0;
    uint64_t h1 = 0x9e3779b97f4a7c15ULL;
    uint64_t h2 = 0xc6a4a7935bd1e995ULL;
    bool operator==(loaded_libs_sig const & o) const {
        return count == o.count && h1 == o.h1 && h2 == o.h2;
    }
};

std::mutex g_loaded_libs_mutex;
bool g_loaded_libs_cached = false;
loaded_libs_sig g_loaded_libs_sig;
std::vector<lib_info> g_loaded_libs;

loaded_libs_sig compute_loaded_libs_sig() {
    loaded_libs_sig sig;
    dl_iterate_phdr([](struct dl_phdr_info * info, size_t, void * data) -> int {
        loaded_libs_sig * s = static_cast<loaded_libs_sig *>(data);
        s->count++;
        uint64_t addr = static_cast<uint64_t>(info->dlpi_addr);
        s->h1 = hash(s->h1, addr);
        s->h2 = hash(s->h2 ^ s->count, addr);
        char const * name = info->dlpi_name ? info->dlpi_name : "";
        size_t len = strlen(name);
        s->h1 = hash_str(len, reinterpret_cast<unsigned char const *>(name), s->h1);
        s->h2 = hash_str(len, reinterpret_cast<unsigned char const *>(name), s->h2 ^ 0x517cc1b727220a95ULL);
        return 0;
    }, &sig);
    return sig;
}
#endif
}

LEAN_EXPORT std::vector<lib_info> get_loaded_libs() {
#if !defined(LEAN_WINDOWS) && !defined(__APPLE__)
    loaded_libs_sig sig = compute_loaded_libs_sig();
    {
        std::lock_guard<std::mutex> lock(g_loaded_libs_mutex);
        if (g_loaded_libs_cached && g_loaded_libs_sig == sig) {
            return g_loaded_libs;
        }
    }
    struct build_ctx {
        std::vector<lib_info> libs;
        loaded_libs_sig sig;
    } ctx;
    dl_iterate_phdr([](struct dl_phdr_info * info, size_t, void * data) -> int {
        build_ctx * c = static_cast<build_ctx *>(data);
        char const * name = info->dlpi_name ? info->dlpi_name : "";
        c->libs.push_back({info->dlpi_addr, name});
        c->sig.count++;
        uint64_t addr = static_cast<uint64_t>(info->dlpi_addr);
        c->sig.h1 = hash(c->sig.h1, addr);
        c->sig.h2 = hash(c->sig.h2 ^ c->sig.count, addr);
        size_t len = strlen(name);
        c->sig.h1 = hash_str(len, reinterpret_cast<unsigned char const *>(name), c->sig.h1);
        c->sig.h2 = hash_str(len, reinterpret_cast<unsigned char const *>(name), c->sig.h2 ^ 0x517cc1b727220a95ULL);
        return 0;
    }, &ctx);
    std::sort(ctx.libs.begin(), ctx.libs.end(), [](lib_info const & a, lib_info const & b) { return a.base_addr < b.base_addr; });
    {
        std::lock_guard<std::mutex> lock(g_loaded_libs_mutex);
        g_loaded_libs_cached = true;
        g_loaded_libs_sig = ctx.sig;
        g_loaded_libs = ctx.libs;
    }
    return ctx.libs;
#else
    std::vector<lib_info> libs;
#ifdef LEAN_WINDOWS
    HANDLE proc = GetCurrentProcess();
    std::vector<HMODULE> mods(128);
    DWORD needed;
    if (!EnumProcessModules(proc, mods.data(), mods.size() * sizeof(HMODULE), &needed))
        return libs;
    unsigned n = needed / sizeof(HMODULE);
    if (n > mods.size()) {
        mods.resize(n);
        if (!EnumProcessModules(proc, mods.data(), mods.size() * sizeof(HMODULE), &needed))
            return libs;
    } else {
        mods.resize(n);
    }
    for (HMODULE h : mods) {
        MODULEINFO mi;
        if (!GetModuleInformation(proc, h, &mi, sizeof(mi))) continue;
        char path[MAX_PATH];
        if (!GetModuleFileNameA(h, path, sizeof(path))) continue;
        libs.push_back({reinterpret_cast<size_t>(mi.lpBaseOfDll), path});
    }
#elif defined(__APPLE__)
    uint32_t n = _dyld_image_count();
    for (uint32_t i = 0; i < n; i++) {
        const struct mach_header * hdr = _dyld_get_image_header(i);
        if (!hdr) continue;
        const char * name = _dyld_get_image_name(i);
        if (!name) continue;
        libs.push_back({reinterpret_cast<size_t>(hdr), name});
    }
#endif
    std::sort(libs.begin(), libs.end(), [](lib_info const & a, lib_info const & b) { return a.base_addr < b.base_addr; });
    return libs;
#endif
}

std::vector<lib_info> object_compactor::used_libs() const {
    // Mark each loaded library that contains a compacted closure's `m_fun` pointer. The recorded
    // offsets are relative to `m_begin`, and `m_fun` still holds the raw (un-relocated) code
    // pointer at this point, so it identifies the library directly.
    std::vector<bool> used(m_libs.size(), false);
    for (size_t off : m_closure_offsets) {
        size_t fn = reinterpret_cast<size_t>(
            *reinterpret_cast<void * const *>(static_cast<char const *>(m_begin) + off));
        std::vector<lib_info>::const_iterator it =
            std::upper_bound(m_libs.begin(), m_libs.end(), fn,
                [](size_t addr, lib_info const & lib) { return addr < lib.base_addr; });
        if (it == m_libs.begin())
            throw exception("closure function pointer does not belong to any loaded library");
        used[(it - 1) - m_libs.begin()] = true;
    }
    std::vector<lib_info> result;
    for (size_t i = 0; i < m_libs.size(); i++)
        if (used[i]) result.push_back(m_libs[i]);
    return result;
}

object_compactor::object_compactor(void * base_addr, std::vector<region_view> dep_regions,
                                   bool allow_closures):
    m_obj_slots(g_compactor_table_init_cap),
    m_max_sharing_slots(g_compactor_table_init_cap),
    m_dep_regions(std::move(dep_regions)),
    m_libs(allow_closures ? get_loaded_libs() : std::vector<lib_info>{}),
    m_allow_closures(allow_closures),
    m_base_addr(base_addr),
    m_begin(malloc(LEAN_COMPACTOR_INIT_SZ)),
    m_end(m_begin),
    m_capacity(static_cast<char*>(m_begin) + LEAN_COMPACTOR_INIT_SZ) {
    // Sort dep regions by `begin` address for binary search in `to_offset`.
    std::sort(m_dep_regions.begin(), m_dep_regions.end(),
              [](region_view const & a, region_view const & b) { return a.begin < b.begin; });
}

object_compactor::~object_compactor() {
    free(m_begin);
}

/*
  Remark: g_null_offset must NOT be a valid Lean scalar value (e.g., static_cast<size_t>(-1)).
  Recall that Lean scalar are odd size_t values. So, we use (static_cast<size_t>(-1) - 1) which is an even number.
  In the past we used `static_cast<size_t>(-1)`, and it caused nontermination in the object compactor.
*/
object_offset g_null_offset = reinterpret_cast<object_offset>(static_cast<size_t>(-1) - 1);

void * object_compactor::alloc(size_t sz) {
    size_t rem = sz % sizeof(void*);
    if (rem != 0)
        sz = sz + sizeof(void*) - rem;
    while (static_cast<char*>(m_end) + sz > m_capacity) {
        size_t new_capacity = capacity()*2;
        void * new_begin = malloc(new_capacity);
        memcpy(new_begin, m_begin, size());
        m_end      = static_cast<char*>(new_begin) + size();
        m_capacity = static_cast<char*>(new_begin) + new_capacity;
        free(m_begin);
        m_begin    = new_begin;
    }
    void * r = m_end;
    memset(r, 0, sz);
    m_end = static_cast<char*>(m_end) + sz;
    lean_assert(m_end <= m_capacity);
    return r;
}

void object_compactor::grow_obj_table() {
    size_t new_cap = m_obj_slots.size() * 2;
    std::vector<obj_slot> new_slots(new_cap);
    size_t mask = new_cap - 1;
    for (obj_slot const & s : m_obj_slots) {
        if (s.key == nullptr) continue;
        size_t idx = hash_obj_ptr(s.key) & mask;
        while (new_slots[idx].key != nullptr) {
            idx = (idx + 1) & mask;
        }
        new_slots[idx] = s;
    }
    m_obj_slots.swap(new_slots);
}

bool object_compactor::find_obj(object * o, object_offset & out) const {
    size_t mask = m_obj_slots.size() - 1;
    size_t idx = hash_obj_ptr(o) & mask;
    while (true) {
        obj_slot const & s = m_obj_slots[idx];
        if (s.key == o) {
            out = s.offset;
            return true;
        }
        if (s.key == nullptr)
            return false;
        idx = (idx + 1) & mask;
    }
}

void object_compactor::insert_obj(object * o, object_offset off) {
    lean_assert(o != nullptr);
    if ((m_obj_count + 1) * 10 > m_obj_slots.size() * 7)
        grow_obj_table();
    size_t mask = m_obj_slots.size() - 1;
    size_t idx = hash_obj_ptr(o) & mask;
    while (true) {
        obj_slot & s = m_obj_slots[idx];
        if (s.key == nullptr) {
            s.key = o;
            s.offset = off;
            m_obj_count++;
            return;
        }
        if (s.key == o)
            return;
        idx = (idx + 1) & mask;
    }
}

void object_compactor::grow_max_sharing_table() {
    size_t new_cap = m_max_sharing_slots.size() * 2;
    std::vector<max_sharing_slot> new_slots(new_cap);
    size_t mask = new_cap - 1;
    for (max_sharing_slot const & s : m_max_sharing_slots) {
        if (s.hash32 == 0) continue;
        size_t idx = static_cast<size_t>(s.hash32) & mask;
        while (new_slots[idx].hash32 != 0) {
            idx = (idx + 1) & mask;
        }
        new_slots[idx] = s;
    }
    m_max_sharing_slots.swap(new_slots);
}

object_offset object_compactor::save(object * o, object * new_o) {
    lean_assert(m_begin <= new_o && new_o < m_end);
    object_offset off = reinterpret_cast<object_offset>(reinterpret_cast<char*>(new_o) - reinterpret_cast<char*>(m_begin) + reinterpret_cast<size_t>(m_base_addr));
    insert_obj(o, off);
    return off;
}

object_offset object_compactor::save_max_sharing(object * o, object * new_o, size_t new_o_sz) {
    if (new_o_sz <= UINT32_MAX) {
        uint32_t sz32 = static_cast<uint32_t>(new_o_sz);
        uint64_t off = static_cast<uint64_t>(reinterpret_cast<char*>(new_o) - reinterpret_cast<char*>(m_begin));
        uint32_t h32 = hash_compacted_bytes(new_o, new_o_sz);
        char const * base = static_cast<char const *>(m_begin);
        size_t mask = m_max_sharing_slots.size() - 1;
        size_t idx = static_cast<size_t>(h32) & mask;
        while (true) {
            max_sharing_slot & s = m_max_sharing_slots[idx];
            if (s.hash32 == 0) {
                if ((m_max_sharing_count + 1) * 10 > m_max_sharing_slots.size() * 7) {
                    grow_max_sharing_table();
                    size_t nmask = m_max_sharing_slots.size() - 1;
                    idx = static_cast<size_t>(h32) & nmask;
                    while (m_max_sharing_slots[idx].hash32 != 0) {
                        idx = (idx + 1) & nmask;
                    }
                }
                m_max_sharing_slots[idx] = {off, sz32, h32};
                m_max_sharing_count++;
                break;
            }
            if (s.hash32 == h32 && s.size == sz32 && memcmp(base + s.offset, new_o, new_o_sz) == 0) {
                // Keep the first-inserted offset so compacted .olean bytes remain bit-identical.
                m_end = new_o;
                new_o = reinterpret_cast<lean_object*>(reinterpret_cast<char*>(m_begin) + s.offset);
                break;
            }
            idx = (idx + 1) & mask;
        }
    }
    return save(o, new_o);
}

object_offset object_compactor::to_offset(object * o) {
    if (lean_is_scalar(o)) {
        return o;
    } else {
        object_offset cached;
        if (find_obj(o, cached)) {
            return cached;
        }
        // Only check dep regions for non-heap objects
        if (!m_dep_regions.empty() && !lean_has_rc(o)) {
            // Binary search dep regions (sorted by begin)
            char * addr = reinterpret_cast<char *>(o);
            // Find the first region whose begin > addr, then step back
            std::vector<region_view>::iterator upper = std::upper_bound(
                m_dep_regions.begin(), m_dep_regions.end(), addr,
                [](char * a, region_view const & r) { return a < static_cast<char *>(r.begin); });
            if (upper != m_dep_regions.begin()) {
                region_view const & region = *(upper - 1);
                char * region_end = static_cast<char *>(region.begin) + region.size;
                if (addr < region_end) {
                    // Object is in this dep region, compute its base_addr-relative pointer
                    object_offset off = reinterpret_cast<object_offset>(
                        reinterpret_cast<size_t>(region.base_addr) + (addr - static_cast<char *>(region.begin)));
                    insert_obj(o, off);
                    return off;
                }
            }
        }
        return compact(o);
    }
}

object_offset object_compactor::compact(object * o) {
    lean_assert(!lean_is_scalar(o));
#ifdef LEAN_TAG_COUNTERS
    g_tag_counters[lean_ptr_tag(o)]++;
#endif
    switch (lean_ptr_tag(o)) {
    case LeanClosure:         return insert_closure(o);
    case LeanArray:           return insert_array(o);
    case LeanScalarArray:     return insert_sarray(o);
    case LeanString:          return insert_string(o);
    case LeanMPZ:             return insert_mpz(o);
    case LeanThunk:           return insert_thunk(o);
    case LeanTask:            return insert_task(o);
    case LeanPromise:         return insert_promise(o);
    case LeanRef:             return insert_ref(o);
    case LeanExternal:        throw exception("external objects cannot be compacted");
    case LeanReserved:        lean_unreachable();
    default:                  return insert_constructor(o);
    }
}

object * object_compactor::copy_object(object * o, size_t sz) {
    if (sz == 0) sz = lean_object_byte_size(o);
    void * mem = alloc(sz);
    memcpy(mem, o, sz);
    object * r = static_cast<object*>(mem);
    lean_set_non_heap_header(r, sz, lean_ptr_tag(o), lean_ptr_other(o));
    lean_assert(!lean_has_rc(r));
    lean_assert(lean_ptr_tag(r) == lean_ptr_tag(o));
    lean_assert(lean_ptr_other(r) == lean_ptr_other(o));
    return r;
}

object_offset object_compactor::insert_sarray(object * o) {
    size_t sz        = lean_sarray_size(o);
    unsigned elem_sz = lean_sarray_elem_size(o);
    size_t obj_sz = lean_usize_add_checked(sizeof(lean_sarray_object), lean_usize_mul_checked(elem_sz, sz));
    lean_sarray_object * new_o = (lean_sarray_object*)alloc(obj_sz);
    lean_set_non_heap_header_for_big((lean_object*)new_o, LeanScalarArray, elem_sz);
    new_o->m_size     = sz;
    new_o->m_capacity = sz;
    memcpy(new_o->m_data, lean_to_sarray(o)->m_data, elem_sz*sz);
    return save_max_sharing(o, (lean_object*)new_o, obj_sz);
}

object_offset object_compactor::insert_string(object * o) {
    size_t sz        = lean_string_size(o);
    size_t len       = lean_string_len(o);
    size_t obj_sz = lean_usize_add_checked(sizeof(lean_string_object), sz);
    lean_string_object * new_o = (lean_string_object*)alloc(obj_sz);
    lean_set_non_heap_header_for_big((lean_object*)new_o, LeanString, 0);
    new_o->m_size     = sz;
    new_o->m_capacity = sz;
    new_o->m_length   = len;
    memcpy(new_o->m_data, lean_to_string(o)->m_data, sz);
    return save_max_sharing(o, (lean_object*)new_o, obj_sz);
}

// #define ShowCtors

// `m_tmp` is used as a recursion stack: each `insert_*` with children reserves a
// window `[base, base + n)` for its child offsets and pops it before returning, so
// nested calls never share slots and arbitrarily large arrays stay off the C stack.
object_offset object_compactor::insert_constructor(object * o) {
    unsigned num_objs = lean_ctor_num_objs(o);
    size_t base = m_tmp.size();
    m_tmp.resize(base + num_objs);
    for (unsigned i = 0; i < num_objs; i++) {
        object_offset c = to_offset(cnstr_get(o, i));
        m_tmp[base + i] = c;
    }
    object * new_o = copy_object(o);
    for (unsigned i = 0; i < num_objs; i++)
        lean_ctor_set(new_o, i, m_tmp[base + i]);
    m_tmp.resize(base);
    return save_max_sharing(o, new_o, lean_object_byte_size(o));
}

object_offset object_compactor::insert_array(object * o) {
    size_t sz = array_size(o);
    size_t base = m_tmp.size();
    m_tmp.resize(base + sz);
    for (size_t i = 0; i < sz; i++) {
        object_offset c = to_offset(array_get(o, i));
        m_tmp[base + i] = c;
    }
    size_t obj_sz = lean_usize_add_checked(sizeof(lean_array_object), lean_usize_mul_checked(sizeof(void*), sz));
    lean_array_object * new_o = (lean_array_object*)alloc(obj_sz);
    lean_set_non_heap_header_for_big((lean_object*)new_o, LeanArray, 0);
    new_o->m_size     = sz;
    new_o->m_capacity = sz;
    for (size_t i = 0; i < sz; i++)
        lean_array_set_core((lean_object*)new_o, i, m_tmp[base + i]);
    m_tmp.resize(base);
    return save_max_sharing(o, (lean_object*)new_o, obj_sz);
}

object_offset object_compactor::insert_thunk(object * o) {
    object_offset c = to_offset(lean_thunk_get(o));
    size_t sz = sizeof(lean_thunk_object);
    object * r = copy_object(o, sz);
    lean_to_thunk(r)->m_value = c;
    return save_max_sharing(o, r, sz);
}

object_offset object_compactor::insert_ref(object * o) {
    object_offset c = to_offset(lean_to_ref(o)->m_value);
    size_t sz = sizeof(lean_ref_object);
    object * r = copy_object(o, sz);
    lean_to_ref(r)->m_value = c;
    // must NOT be max-shared
    return save(o, r);
}

object_offset object_compactor::insert_task(object * o) {
    object_offset c = to_offset(lean_task_get(o));
    size_t sz = sizeof(lean_task_object);
    object * r = copy_object(o, sz);
    lean_assert(lean_to_task(r)->m_imp == nullptr);
    lean_to_task(r)->m_value = c;
    return save_max_sharing(o, r, sz);
}

object_offset object_compactor::insert_closure(object * o) {
    if (!m_allow_closures) {
        throw exception("Closures cannot be compacted (unless explicitly calling "
                        "`CompactedRegion.save (allowClosures := true)`). One possible cause of this error is "
                        "trying to store a function in a persistent environment extension.");
    }
    unsigned n = lean_closure_num_fixed(o);
    size_t base = m_tmp.size();
    m_tmp.resize(base + n);
    for (unsigned i = 0; i < n; i++) {
        object_offset c = to_offset(lean_closure_arg_cptr(o)[i]);
        m_tmp[base + i] = c;
    }
    object * r = copy_object(o);
    for (unsigned i = 0; i < n; i++)
        lean_closure_arg_cptr(r)[i] = m_tmp[base + i];
    m_tmp.resize(base);
    // Record the buffer-relative offset of `r`'s `m_fun` field so the reader can patch
    // closure fn pointers on load without scanning the compacted region.
    size_t fn_field_off = reinterpret_cast<char *>(&lean_to_closure(r)->m_fun)
                          - reinterpret_cast<char *>(m_begin);
    m_closure_offsets.push_back(fn_field_off);
    return save(o, r);
}

object_offset object_compactor::insert_promise(object * o) {
    object_offset c = to_offset((object *)lean_to_promise(o)->m_result);
    size_t sz = sizeof(lean_promise_object);
    object * r = copy_object(o, sz);
    lean_to_promise(r)->m_result = (lean_task_object *)c;
    return save_max_sharing(o, r, sz);
}

object_offset object_compactor::insert_mpz(object * o) {
#ifdef LEAN_USE_GMP
    size_t nlimbs = mpz_size(to_mpz(o)->m_value.m_val);
    size_t data_sz = lean_usize_mul_checked(sizeof(mp_limb_t), nlimbs);
    size_t sz = lean_usize_add_checked(sizeof(mpz_object), data_sz);
    mpz_object * new_o = (mpz_object *)alloc(sz);
    memcpy((void*)new_o, to_mpz(o), sizeof(mpz_object));
    lean_set_non_heap_header((lean_object*)new_o, sz, LeanMPZ, 0);
    __mpz_struct & m = new_o->m_value.m_val[0];
    // we assume the limb array is the only indirection in an `__mpz_struct` and everything else can be bitcopied
    void * data = reinterpret_cast<char*>(new_o) + sizeof(mpz_object);
    memcpy(data, m._mp_d, data_sz);
    m._mp_d = reinterpret_cast<mp_limb_t *>(reinterpret_cast<char *>(data) - reinterpret_cast<char *>(m_begin) + reinterpret_cast<ptrdiff_t>(m_base_addr));
    m._mp_alloc = nlimbs;
    return save(o, (lean_object*)new_o);
#else
    size_t data_sz = lean_usize_mul_checked(sizeof(mpn_digit), to_mpz(o)->m_value.m_size);
    size_t sz      = lean_usize_add_checked(sizeof(mpz_object), data_sz);
    mpz_object * new_o = (mpz_object *)alloc(sz);
    // Manually copy the `mpz_object` to ensure `mpz` struct padding is left as
    // zero as prepared by `object_compactor::alloc`. `memcpy` would copy the
    // padding and lead to non-deterministic outputs.
    new_o->m_header = to_mpz(o)->m_header;
    new_o->m_value.m_sign = to_mpz(o)->m_value.m_sign;
    new_o->m_value.m_size = to_mpz(o)->m_value.m_size;
    lean_set_non_heap_header((lean_object*)new_o, sz, LeanMPZ, 0);
    void * data = reinterpret_cast<char*>(new_o) + sizeof(mpz_object);
    memcpy(data, to_mpz(o)->m_value.m_digits, data_sz);
    new_o->m_value.m_digits = reinterpret_cast<mpn_digit *>(reinterpret_cast<char *>(data) - reinterpret_cast<char *>(m_begin) + reinterpret_cast<ptrdiff_t>(m_base_addr));
    return save(o, (lean_object*)new_o);
#endif
}

#ifdef LEAN_TAG_COUNTERS

static size_t g_tag_counters[256];

struct tag_counter_manager {
    static void display_kind(char const * msg, unsigned k) {
        if (g_tag_counters[k] != 0)
            std::cout << msg << " " << g_tag_counters[k] << "\n";
    }

    tag_counter_manager() {
        for (unsigned i = 0; i < 256; i++) g_tag_counters[i] = 0;
    }

    ~tag_counter_manager() {
        display_kind("#closure:  ", LeanClosure);
        display_kind("#array:    ", LeanArray);
        display_kind("#sarray:   ", LeanStructArray);
        display_kind("#scarray:  ", LeanScalarArray);
        display_kind("#string:   ", LeanString);
        display_kind("#mpz:      ", LeanMPZ);
        display_kind("#thunk:    ", LeanThunk);
        display_kind("#task:     ", LeanTask);
        display_kind("#promise:  ", LeanPromise);
        display_kind("#ref:      ", LeanRef);
        display_kind("#external: ", LeanExternal);

        size_t num_ctors = 0;
        for (unsigned i = 0; i <= LeanMaxCtorTag; i++)
            num_ctors += g_tag_counters[i];
        std::cout << "#ctors:     " << num_ctors << "\n";
    }
};

tag_counter_manager g_tag_counter_manager;

#endif

void object_compactor::operator()(object * o) {
    lean_assert(m_tmp.empty());
    // Allocate the root-address slot first (see below). We store an offset rather
    // than a pointer because `m_begin` may be reallocated while compacting `o`.
    size_t root_offset =
      static_cast<char *>(alloc(sizeof(object_offset))) - static_cast<char *>(m_begin);
    object_offset off = to_offset(o);
    object_offset * root = reinterpret_cast<object_offset *>(static_cast<char *>(m_begin) + root_offset);
    *root = off;
}

region_reader::region_reader(size_t sz, void * data, void * base_addr,
                             std::vector<region_view> dep_regions,
                             std::vector<std::pair<size_t, ptrdiff_t>> lib_relocs,
                             std::vector<size_t> closure_offsets):
    m_size(sz),
    m_base_addr(base_addr),
    m_begin(data),
    m_next(data),
    m_end(static_cast<char*>(data)+sz),
    m_dep_regions(std::move(dep_regions)),
    m_lib_relocs(std::move(lib_relocs)),
    m_closure_offsets(std::move(closure_offsets)) {
    // Sort + overlap validation are deferred to `sort_and_validate_dep_regions()`: needed only
    // before the fixup walk; the fast path in `read()` skips both. Doing them eagerly here was
    // an O(N log N) per construction over a `dep_regions` array that grows linearly across
    // successive `CompactedRegion.read` calls (e.g. `--incr-load` chaining 9000+ dep oleans).
}

void region_reader::sort_and_validate_dep_regions() {
    // Sort dep regions by `base_addr` for binary search in `fix_object_ptr`
    std::sort(m_dep_regions.begin(), m_dep_regions.end(),
              [](region_view const & a, region_view const & b) { return a.base_addr < b.base_addr; });
    // Reject overlapping saved address ranges: `fix_object_ptr` resolves cross-region pointers
    // by binary-searching `base_addr`s, and would silently translate via the wrong region if
    // two deps overlap (or if a dep overlaps our own range). This should not happen with regular
    // .olean use as we use only use `read`'s `prev` instead of `dep_regions` there.
    for (size_t i = 1; i < m_dep_regions.size(); i++) {
        region_view const & prev = m_dep_regions[i - 1];
        region_view const & curr = m_dep_regions[i];
        if (reinterpret_cast<size_t>(prev.base_addr) + prev.size
                > reinterpret_cast<size_t>(curr.base_addr)) {
            throw exception("region_reader: dep regions have overlapping `base_addr` ranges");
        }
    }
    size_t self_base = reinterpret_cast<size_t>(m_base_addr);
    size_t self_end = self_base + m_size;
    for (region_view const & dep : m_dep_regions) {
        size_t dep_base = reinterpret_cast<size_t>(dep.base_addr);
        size_t dep_end = dep_base + dep.size;
        if (self_base < dep_end && dep_base < self_end) {
            throw exception("region_reader: own region overlaps a dep region's `base_addr` range");
        }
    }
}


inline object * region_reader::fix_object_ptr(object * o) {
    if (lean_is_scalar(o)) return o;
    size_t addr = reinterpret_cast<size_t>(o);
    size_t self_base = reinterpret_cast<size_t>(m_base_addr);
    // Check own region first (most common case)
    if (addr >= self_base && addr < self_base + m_size) {
        return reinterpret_cast<object*>(static_cast<char*>(m_begin) + (addr - self_base));
    }
    // Binary search dep regions (sorted by `base_addr`)
    char * addr_ptr = reinterpret_cast<char *>(addr);
    // Find the first region whose base_addr > addr, then step back
    std::vector<region_view>::iterator upper = std::upper_bound(
        m_dep_regions.begin(), m_dep_regions.end(), addr_ptr,
        [](char * a, region_view const & r) { return a < static_cast<char *>(r.base_addr); });
    if (upper != m_dep_regions.begin()) {
        region_view const & dep = *(upper - 1);
        size_t dep_base = reinterpret_cast<size_t>(dep.base_addr);
        if (addr < dep_base + dep.size) {
            return reinterpret_cast<object*>(static_cast<char*>(dep.begin) + (addr - dep_base));
        }
    }
    lean_unreachable();
}

inline void region_reader::move(size_t d) {
    lean_assert(m_next < m_end);
    size_t rem = d % sizeof(void*);
    if (rem != 0)
        d = d + sizeof(void*) - rem;
    m_next = static_cast<char*>(m_next) + d;
}

inline void region_reader::move(object * o) {
    return move(lean_object_byte_size(o));
}

inline void region_reader::fix_constructor(object * o) {
    lean_assert(!lean_has_rc(o));
    object ** it  = lean_ctor_obj_cptr(o);
    object ** end = it + lean_ctor_num_objs(o);
    for (; it != end; it++) {
        *it = fix_object_ptr(*it);
    }
    lean_assert(lean_object_byte_size(o) < 4192);
    move(o);
}

inline void region_reader::fix_array(object * o) {
    object ** it  = lean_array_cptr(o);
    object ** end = it + lean_array_size(o);
    for (; it != end; it++) {
        *it = fix_object_ptr(*it);
    }
    move(o);
}

inline void region_reader::fix_thunk(object * o) {
    lean_to_thunk(o)->m_value = fix_object_ptr(lean_to_thunk(o)->m_value);
    move(sizeof(lean_thunk_object));
}

inline void region_reader::fix_ref(object * o) {
    lean_to_ref(o)->m_value = fix_object_ptr(lean_to_ref(o)->m_value);
    move(sizeof(lean_ref_object));
}

inline void region_reader::fix_task(object * o) {
    lean_to_task(o)->m_value = fix_object_ptr(lean_to_task(o)->m_value);
    move(sizeof(lean_task_object));
}

inline void region_reader::fix_promise(object * o) {
    lean_to_promise(o)->m_result = (lean_task_object *)fix_object_ptr((lean_object *)lean_to_promise(o)->m_result);
    move(sizeof(lean_promise_object));
}

void region_reader::fix_mpz(object * o) {
#ifdef LEAN_USE_GMP
    __mpz_struct & m = to_mpz(o)->m_value.m_val[0];
    m._mp_d = reinterpret_cast<mp_limb_t *>(static_cast<char *>(m_begin) + reinterpret_cast<size_t>(m._mp_d) - reinterpret_cast<size_t>(m_base_addr));
    move(sizeof(mpz_object) + sizeof(mp_limb_t) * mpz_size(to_mpz(o)->m_value.m_val));
#else
    to_mpz(o)->m_value.m_digits = reinterpret_cast<mpn_digit*>(reinterpret_cast<char*>(o) + sizeof(mpz_object));
    move(sizeof(mpz_object) + sizeof(mpn_digit) * to_mpz(o)->m_value.m_size);
#endif
}

void region_reader::fix_closure(object * o) {
    // Fix captured object pointers. The closure's `m_fun` is relocated separately
    // via `m_closure_offsets` before the walk runs.
    object ** it = lean_closure_arg_cptr(o);
    object ** end = it + lean_closure_num_fixed(o);
    for (; it != end; it++)
        *it = fix_object_ptr(*it);
    move(o);
}

object * region_reader::read() {
    if (m_next == m_end)
        return nullptr; /* all objects have been read */

    // Check if any closure fn ptr relocation is actually needed
    bool needs_fn_reloc = false;
    for (std::pair<size_t, ptrdiff_t> const & reloc : m_lib_relocs) {
        if (reloc.second != 0) { needs_fn_reloc = true; break; }
    }

    // Apply closure fn-pointer relocations directly via the offset list rather than
    // by scanning the compacted region for closure tags.
    if (needs_fn_reloc && !m_closure_offsets.empty()) {
        char * begin = static_cast<char *>(m_begin);
        for (size_t off : m_closure_offsets) {
            void ** fn_field = reinterpret_cast<void **>(begin + off);
            size_t fn = reinterpret_cast<size_t>(*fn_field);
            std::vector<std::pair<size_t, ptrdiff_t>>::const_iterator upper =
                std::upper_bound(m_lib_relocs.begin(), m_lib_relocs.end(), fn,
                    [](size_t addr, std::pair<size_t, ptrdiff_t> const & e) { return addr < e.first; });
            if (upper != m_lib_relocs.begin()) {
                ptrdiff_t delta = (upper - 1)->second;
                if (delta != 0)
                    *fn_field = reinterpret_cast<void *>(static_cast<ptrdiff_t>(fn) + delta);
            }
        }
    }

    if (m_begin == m_base_addr) {
        bool needs_dep_reloc = false;
        for (region_view const & dep : m_dep_regions) {
            if (dep.begin != dep.base_addr) { needs_dep_reloc = true; break; }
        }
        if (!needs_dep_reloc) {
            // Fast path: own pointers and all dep pointers are already correct, so the saved root
            // pointer needs no fixup and the structural walk can be skipped entirely. This also
            // lets us avoid sorting and validating `m_dep_regions` (the dominant cost when chaining
            // many dep oleans into a single `region_reader`).
            object * root = *static_cast<object_offset *>(m_next);
            m_end = m_next;
            return root;
        }
    }

    // Slow path: dep-region fixup needed. Sort and validate dep regions now.
    sort_and_validate_dep_regions();
    object * root = fix_object_ptr(*static_cast<object_offset *>(m_next));
    move(sizeof(object_offset));

    while (m_next < m_end) {
        object * curr = reinterpret_cast<object*>(m_next);
        uint8 tag = lean_ptr_tag(curr);
        if (tag <= LeanMaxCtorTag) {
            fix_constructor(curr);
        } else {
            switch (tag) {
            case LeanClosure:         fix_closure(curr); break;
            case LeanArray:           fix_array(curr); break;
            case LeanScalarArray:     move(lean_sarray_byte_size(curr)); break;
            case LeanString:          move(lean_string_byte_size(curr)); break;
            case LeanMPZ:             fix_mpz(curr); break;
            case LeanThunk:           fix_thunk(curr); break;
            case LeanRef:             fix_ref(curr); break;
            case LeanTask:            fix_task(curr); break;
            case LeanPromise:         fix_promise(curr); break;
            case LeanExternal:        lean_unreachable();
            default:                  lean_unreachable();
            }
        }
    }
    return root;
}

}
