use std::collections::HashMap;
use std::fs::{self, File};
use std::io::{BufWriter, Write};
use std::path::Path;
use std::time::Instant;

use bytemuck;
use con_ron_core::arena::cons_map::ConsHandle;
use con_ron_core::arena::env::{
    i_constant_info_name, IConstantInfo, IConstantVal, IDeclaration, IIndCaps, IProjTable,
    IRecRule, IRecRuleFire,
};
use con_ron_core::arena::handle::{
    EIdx, LIdx, LsIdx, NIdx, ETAG_BVAR, ETAG_CONST, ETAG_FORALL_E, ETAG_FVAR, ETAG_LAM,
    ETAG_LET_E, ETAG_LIT, ETAG_PROJ, ETAG_SORT, LSTAG_LIST, LTAG_IMAX, LTAG_MAX, LTAG_PARAM,
    LTAG_SUCC, LTAG_ZERO, NTAG_ANONYMOUS, NTAG_NUM, NTAG_STR, TIER_P,
};
use con_ron_core::arena::nat_op_pin_set::INatOpPinSet;
use con_ron_core::arena::pins::Pins;
use con_ron_core::arena::store::{
    AnonNode, AppNode, BVarNode, BinLNode, BindNode, ConstNode, DerDefault, ETables, FVarNode,
    LDer, LTables, LetNode, ListNode, LitNode, LsTables, NTables, NumNode, ParamNode, PersTier,
    ProjNode, SortNode, StrNode, SuccNode, Tbl, ZeroNode,
};
use con_ron_core::arena::stream_index::IStreamIndex;
use con_ron_core::kernel::env::{QuotKind, ReducibilityHint};
use con_ron_core::kernel::expr::{literal_nat, literal_str, Literal};
use con_ron_core::ron::hashmap::{Dup, Eq2, Hashable};
use con_ron_core::ron::hashmap2::HashMap2;
use con_ron_core::ron::nat::Nat;

use crate::fs::{
    combine_chunk_hashes128, compute_chunked_checksum128, hash128_bytes_with_seed,
    validate_closure_manifest, ClosureTarget, SnapshotManifestEntry, CHUNK_CHECKSUM_BYTES,
};
use crate::loader::LoadedEnvironment;
use crate::soa_pack::{ArenaHeader, GpuArenaPacket, GpuJob};

pub const SNAPSHOT_MAGIC: [u8; 8] = *b"CGSNAP03";
const SNAPSHOT_FIXED_HEADER_BYTES: usize = 160;
const SNAPSHOT_CHECKSUM_BYTES: usize = 16;

pub struct LoadedSnapshot {
    pub env: LoadedEnvironment,
    pub packet: GpuArenaPacket,
    pub closure_hash: [u8; 16],
    pub file_records: usize,
    pub start_decl: usize,
    pub load_ns: u128,
}

pub struct CpuLoadedSnapshot {
    pub env: LoadedEnvironment,
    pub closure_hash: [u8; 16],
    pub file_records: usize,
    pub start_decl: usize,
    pub eligible_jobs_count: usize,
    pub total_jobs: usize,
    pub load_ns: u128,
}

/// Deferred host-section decoder returned by [`GpuFirstSnapshot::split_for_hybrid`].
pub struct SnapshotHostDecoder {
    pub closure_hash: [u8; 16],
    pub closure_roots: Vec<String>,
    pub closure_manifest: Vec<SnapshotManifestEntry>,
    pub file_records: usize,
    pub start_decl: usize,
    pub preverified_prefix: usize,
    pub synthesized: u64,
    pub hoisted: usize,
    pub thm_materialized_count: usize,
    pub load_gpu_first_ns: u128,
    host_bytes: Vec<u8>,
}

impl SnapshotHostDecoder {
    /// Decodes the `HostSection` columns and rebuilds `PersTier` cons maps + `IStreamIndex` hashes.
    pub fn decode(self) -> Result<LoadedEnvironment, String> {
        decode_host_section_and_env(
            &self.host_bytes,
            self.closure_hash,
            self.closure_roots,
            self.closure_manifest,
            self.file_records,
            self.preverified_prefix,
            self.synthesized,
            self.hoisted,
            self.thm_materialized_count,
            self.load_gpu_first_ns,
        )
    }
}

/// Stage-1 snapshot handle holding the verified `GpuArenaPacket` + raw `HostSection` bytes.
/// GPU upload and execution can start immediately after checksum + manifest validation while
/// `into_host_env()` / `SnapshotHostDecoder::decode()` decodes `PersTier`/`env` and rebuilds
/// `ConsMap` hash indices concurrently.
pub struct GpuFirstSnapshot {
    pub packet: GpuArenaPacket,
    pub closure_hash: [u8; 16],
    pub closure_roots: Vec<String>,
    pub closure_manifest: Vec<SnapshotManifestEntry>,
    pub file_records: usize,
    pub start_decl: usize,
    pub preverified_prefix: usize,
    pub synthesized: u64,
    pub hoisted: usize,
    pub thm_materialized_count: usize,
    pub load_gpu_first_ns: u128,
    host_bytes: Vec<u8>,
}

impl GpuFirstSnapshot {
    /// Splits ownership of `GpuArenaPacket` and the deferred host-section decoder so GPU
    /// verification can run immediately while host `PersTier`/`ConsMap` decoding overlaps.
    pub fn split_for_hybrid(self) -> (GpuArenaPacket, SnapshotHostDecoder) {
        let dec = SnapshotHostDecoder {
            closure_hash: self.closure_hash,
            closure_roots: self.closure_roots,
            closure_manifest: self.closure_manifest,
            file_records: self.file_records,
            start_decl: self.start_decl,
            preverified_prefix: self.preverified_prefix,
            synthesized: self.synthesized,
            hoisted: self.hoisted,
            thm_materialized_count: self.thm_materialized_count,
            load_gpu_first_ns: self.load_gpu_first_ns,
            host_bytes: self.host_bytes,
        };
        (self.packet, dec)
    }

    /// Decodes the `HostSection` columns and rebuilds `PersTier` cons maps + `IStreamIndex` hashes.
    pub fn into_host_env(self) -> Result<LoadedEnvironment, String> {
        self.split_for_hybrid().1.decode()
    }
}

struct ChunkedSnapWriter {
    w: BufWriter<File>,
    chunk_buf: Vec<u8>,
    chunk_hashes: Vec<[u8; 16]>,
    total_bytes: u64,
}

impl ChunkedSnapWriter {
    fn new(f: File) -> Self {
        Self {
            w: BufWriter::with_capacity(4 << 20, f),
            chunk_buf: Vec::with_capacity(CHUNK_CHECKSUM_BYTES),
            chunk_hashes: Vec::new(),
            total_bytes: 0,
        }
    }

    #[inline]
    fn hash_and_flush_chunk(&mut self, chunk: &[u8]) -> Result<(), String> {
        let chunk_idx = self.chunk_hashes.len() as u64;
        let s1 = 0xcbf29ce484222325u64 ^ chunk_idx.wrapping_mul(0x9e3779b97f4a7c15);
        let s2 = 0x517cc1b727220a95u64 ^ (chunk.len() as u64);
        let h = hash128_bytes_with_seed(chunk, s1, s2);
        self.chunk_hashes.push(h);
        self.total_bytes = self.total_bytes.wrapping_add(chunk.len() as u64);
        self.w
            .write_all(chunk)
            .map_err(|e| format!("snapshot write failed: {e}"))
    }

    fn write_bytes(&mut self, mut bytes: &[u8]) -> Result<(), String> {
        if !self.chunk_buf.is_empty() {
            let need = CHUNK_CHECKSUM_BYTES - self.chunk_buf.len();
            let take = need.min(bytes.len());
            self.chunk_buf.extend_from_slice(&bytes[..take]);
            bytes = &bytes[take..];
            if self.chunk_buf.len() == CHUNK_CHECKSUM_BYTES {
                let mut tmp = Vec::new();
                std::mem::swap(&mut tmp, &mut self.chunk_buf);
                self.hash_and_flush_chunk(&tmp)?;
                tmp.clear();
                self.chunk_buf = tmp;
            }
        }
        while bytes.len() >= CHUNK_CHECKSUM_BYTES {
            self.hash_and_flush_chunk(&bytes[..CHUNK_CHECKSUM_BYTES])?;
            bytes = &bytes[CHUNK_CHECKSUM_BYTES..];
        }
        if !bytes.is_empty() {
            self.chunk_buf.extend_from_slice(bytes);
        }
        Ok(())
    }

    fn finish(mut self, path: &Path) -> Result<(), String> {
        if !self.chunk_buf.is_empty() {
            let mut tmp = Vec::new();
            std::mem::swap(&mut tmp, &mut self.chunk_buf);
            self.hash_and_flush_chunk(&tmp)?;
        }
        let checksum = combine_chunk_hashes128(&self.chunk_hashes, self.total_bytes);
        self.w
            .write_all(&checksum)
            .map_err(|e| format!("snapshot checksum write failed {}: {e}", path.display()))?;
        self.w
            .flush()
            .map_err(|e| format!("snapshot flush failed {}: {e}", path.display()))
    }

    #[inline]
    fn write_u8(&mut self, v: u8) -> Result<(), String> {
        self.write_bytes(&[v])
    }

    #[inline]
    fn write_u32(&mut self, v: u32) -> Result<(), String> {
        self.write_bytes(&v.to_le_bytes())
    }

    #[inline]
    fn write_u64(&mut self, v: u64) -> Result<(), String> {
        self.write_bytes(&v.to_le_bytes())
    }

    fn write_u32_slice_raw(&mut self, xs: &[u32]) -> Result<(), String> {
        assert!(cfg!(target_endian = "little"));
        if !xs.is_empty() {
            self.write_bytes(bytemuck::cast_slice(xs))?;
        }
        Ok(())
    }

    fn write_u64_slice_raw(&mut self, xs: &[u64]) -> Result<(), String> {
        assert!(cfg!(target_endian = "little"));
        if !xs.is_empty() {
            self.write_bytes(bytemuck::cast_slice(xs))?;
        }
        Ok(())
    }

    fn write_u32_vec(&mut self, xs: &[u32]) -> Result<(), String> {
        self.write_u32(
            u32::try_from(xs.len()).map_err(|_| "u32 slice length overflow".to_string())?,
        )?;
        self.write_u32_slice_raw(xs)
    }

    fn write_u64_vec(&mut self, xs: &[u64]) -> Result<(), String> {
        self.write_u32(
            u32::try_from(xs.len()).map_err(|_| "u64 slice length overflow".to_string())?,
        )?;
        self.write_u64_slice_raw(xs)
    }

    fn write_u8_col<T, F>(&mut self, items: &[T], mut f: F) -> Result<(), String>
    where
        F: FnMut(&T) -> u8,
    {
        let mut scratch = [0u8; 8192];
        let mut idx = 0usize;
        for item in items {
            scratch[idx] = f(item);
            idx += 1;
            if idx == scratch.len() {
                self.write_bytes(&scratch)?;
                idx = 0;
            }
        }
        if idx > 0 {
            self.write_bytes(&scratch[..idx])?;
        }
        Ok(())
    }

    fn write_u32_col<T, F>(&mut self, items: &[T], mut f: F) -> Result<(), String>
    where
        F: FnMut(&T) -> u32,
    {
        assert!(cfg!(target_endian = "little"));
        let mut scratch = [0u32; 8192];
        let mut idx = 0usize;
        for item in items {
            scratch[idx] = f(item);
            idx += 1;
            if idx == scratch.len() {
                self.write_bytes(bytemuck::cast_slice(&scratch))?;
                idx = 0;
            }
        }
        if idx > 0 {
            self.write_bytes(bytemuck::cast_slice(&scratch[..idx]))?;
        }
        Ok(())
    }

    fn write_u64_col<T, F>(&mut self, items: &[T], mut f: F) -> Result<(), String>
    where
        F: FnMut(&T) -> u64,
    {
        assert!(cfg!(target_endian = "little"));
        let mut scratch = [0u64; 4096];
        let mut idx = 0usize;
        for item in items {
            scratch[idx] = f(item);
            idx += 1;
            if idx == scratch.len() {
                self.write_bytes(bytemuck::cast_slice(&scratch))?;
                idx = 0;
            }
        }
        if idx > 0 {
            self.write_bytes(bytemuck::cast_slice(&scratch[..idx]))?;
        }
        Ok(())
    }

    fn write_nidx_vec(&mut self, xs: &[NIdx]) -> Result<(), String> {
        self.write_u32(
            u32::try_from(xs.len()).map_err(|_| "nidx vec overflow".to_string())?,
        )?;
        self.write_u32_col(xs, |x| x.word)
    }

    fn write_lidx_vec(&mut self, xs: &[LIdx]) -> Result<(), String> {
        self.write_u32(
            u32::try_from(xs.len()).map_err(|_| "lidx vec overflow".to_string())?,
        )?;
        self.write_u32_col(xs, |x| x.word)
    }

    fn write_eidx_vec(&mut self, xs: &[EIdx]) -> Result<(), String> {
        self.write_u32(
            u32::try_from(xs.len()).map_err(|_| "eidx vec overflow".to_string())?,
        )?;
        self.write_u32_col(xs, |x| x.word)
    }

    fn write_pair_n_e_vec(&mut self, xs: &[(NIdx, EIdx)]) -> Result<(), String> {
        self.write_u32(
            u32::try_from(xs.len()).map_err(|_| "pair vec overflow".to_string())?,
        )?;
        for (n, e) in xs {
            self.write_u32(n.word)?;
            self.write_u32(e.word)?;
        }
        Ok(())
    }

    fn write_cv(&mut self, cv: &IConstantVal) -> Result<(), String> {
        self.write_u32(cv.name.word)?;
        self.write_nidx_vec(&cv.level_params)?;
        self.write_u32(cv.ty.word)
    }

    fn write_hint(&mut self, h: &ReducibilityHint) -> Result<(), String> {
        match h {
            ReducibilityHint::Opaque => self.write_u8(0),
            ReducibilityHint::Abbrev => self.write_u8(1),
            ReducibilityHint::Regular(height) => {
                self.write_u8(2)?;
                self.write_u64(*height)
            }
        }
    }

    fn write_ind_caps(&mut self, caps: &IIndCaps) -> Result<(), String> {
        self.write_u8(if caps.eta { 1 } else { 0 })?;
        self.write_nidx_vec(&caps.all)?;
        self.write_u64(caps.nparams)?;
        self.write_u64(caps.n_idx)?;
        self.write_nidx_vec(&caps.ctors)?;
        self.write_u8(if caps.never_zero { 1 } else { 0 })
    }

    fn write_const_info(&mut self, ci: &IConstantInfo) -> Result<(), String> {
        match ci {
            IConstantInfo::AxiomInfo(cv) => {
                self.write_u8(0)?;
                self.write_cv(cv)
            }
            IConstantInfo::DefnInfo(cv, v, hint) => {
                self.write_u8(1)?;
                self.write_cv(cv)?;
                self.write_u32(v.word)?;
                self.write_hint(hint)
            }
            IConstantInfo::ThmInfo(cv) => {
                self.write_u8(2)?;
                self.write_cv(cv)
            }
            IConstantInfo::IndInfo(cv, caps) => {
                self.write_u8(3)?;
                self.write_cv(cv)?;
                self.write_ind_caps(caps)
            }
            IConstantInfo::CtorInfo(cv, a, b, ind) => {
                self.write_u8(4)?;
                self.write_cv(cv)?;
                self.write_u64(*a)?;
                self.write_u64(*b)?;
                self.write_u32(ind.word)
            }
            IConstantInfo::RecInfo(cv, a, b, k, rules) => {
                self.write_u8(5)?;
                self.write_cv(cv)?;
                self.write_u64(*a)?;
                self.write_u64(*b)?;
                self.write_u8(if *k { 1 } else { 0 })?;
                self.write_u32(
                    u32::try_from(rules.len()).map_err(|_| "rec rules overflow".to_string())?,
                )?;
                for r in rules {
                    self.write_u32(r.ctor.word)?;
                    self.write_u64(r.nfields)?;
                    match &r.fire {
                        IRecRuleFire::Plain => self.write_u8(0)?,
                        IRecRuleFire::Levels(lvls) => {
                            self.write_u8(1)?;
                            self.write_lidx_vec(lvls)?;
                        }
                        IRecRuleFire::Nested(lvls, pins) => {
                            self.write_u8(2)?;
                            self.write_lidx_vec(lvls)?;
                            self.write_eidx_vec(pins)?;
                        }
                    }
                    self.write_u32(r.rhs.word)?;
                }
                Ok(())
            }
        }
    }
}

struct ColReader<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> ColReader<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    #[inline]
    fn remaining(&self) -> usize {
        self.bytes.len().saturating_sub(self.pos)
    }

    #[inline]
    fn take_bytes(&mut self, len: usize, what: &str) -> Result<&'a [u8], String> {
        let end = self
            .pos
            .checked_add(len)
            .ok_or_else(|| format!("snapshot {what} offset overflow"))?;
        if end > self.bytes.len() {
            return Err(format!("snapshot truncated inside {what}"));
        }
        let s = &self.bytes[self.pos..end];
        self.pos = end;
        Ok(s)
    }

    #[inline]
    fn read_u8(&mut self) -> Result<u8, String> {
        let s = self.take_bytes(1, "u8")?;
        Ok(s[0])
    }

    #[inline]
    fn read_bool(&mut self) -> Result<bool, String> {
        Ok(self.read_u8()? != 0)
    }

    #[inline]
    fn read_u32(&mut self) -> Result<u32, String> {
        let s = self.take_bytes(4, "u32")?;
        Ok(u32::from_le_bytes([s[0], s[1], s[2], s[3]]))
    }

    #[inline]
    fn read_u64(&mut self) -> Result<u64, String> {
        let s = self.take_bytes(8, "u64")?;
        Ok(u64::from_le_bytes([
            s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7],
        ]))
    }

    #[inline]
    fn check_count(&self, count: u64, elem_bytes: usize, what: &str) -> Result<usize, String> {
        let n = usize::try_from(count).map_err(|_| format!("{what} len overflow"))?;
        let need = n
            .checked_mul(elem_bytes)
            .ok_or_else(|| format!("{what} byte size overflow"))?;
        if need > self.remaining() {
            return Err(format!("snapshot truncated / corrupt {what} length"));
        }
        Ok(n)
    }

    #[inline]
    fn read_checked_count(&mut self, min_elem_bytes: usize, what: &str) -> Result<usize, String> {
        let c = self.read_u64()?;
        self.check_count(c, min_elem_bytes, what)
    }

    #[inline]
    fn read_col_slice(&mut self, count: usize, elem_bytes: usize, what: &str) -> Result<&'a [u8], String> {
        let byte_len = count
            .checked_mul(elem_bytes)
            .ok_or_else(|| format!("{what} column size overflow"))?;
        self.take_bytes(byte_len, what)
    }

    fn read_u32_vec_len(&mut self, len: usize) -> Result<Vec<u32>, String> {
        let src = self.read_col_slice(len, 4, "u32 vec")?;
        let mut out = vec![0u32; len];
        if !out.is_empty() {
            assert!(cfg!(target_endian = "little"));
            bytemuck::cast_slice_mut::<u32, u8>(&mut out).copy_from_slice(src);
        }
        Ok(out)
    }

    fn read_u64_vec_len(&mut self, len: usize) -> Result<Vec<u64>, String> {
        let src = self.read_col_slice(len, 8, "u64 vec")?;
        let mut out = vec![0u64; len];
        if !out.is_empty() {
            assert!(cfg!(target_endian = "little"));
            bytemuck::cast_slice_mut::<u64, u8>(&mut out).copy_from_slice(src);
        }
        Ok(out)
    }

    fn read_u32_vec(&mut self) -> Result<Vec<u32>, String> {
        let len = self.read_u32()? as usize;
        self.read_u32_vec_len(len)
    }

    fn read_u64_vec(&mut self) -> Result<Vec<u64>, String> {
        let len = self.read_u32()? as usize;
        self.read_u64_vec_len(len)
    }

    fn read_string(&mut self, what: &str) -> Result<String, String> {
        let len = self.read_u32()? as usize;
        let b = self.take_bytes(len, what)?;
        std::str::from_utf8(b)
            .map(|s| s.to_string())
            .map_err(|_| format!("invalid UTF-8 {what} in snapshot"))
    }

    fn read_nidx_vec(&mut self) -> Result<Vec<NIdx>, String> {
        let len = self.read_u32()? as usize;
        let src = self.read_col_slice(len, 4, "nidx vec")?;
        let mut out = Vec::with_capacity(len);
        for i in 0..len {
            out.push(NIdx::of_word(col_u32(src, i)));
        }
        Ok(out)
    }

    fn read_lidx_vec(&mut self) -> Result<Vec<LIdx>, String> {
        let len = self.read_u32()? as usize;
        let src = self.read_col_slice(len, 4, "lidx vec")?;
        let mut out = Vec::with_capacity(len);
        for i in 0..len {
            out.push(LIdx::of_word(col_u32(src, i)));
        }
        Ok(out)
    }

    fn read_eidx_vec(&mut self) -> Result<Vec<EIdx>, String> {
        let len = self.read_u32()? as usize;
        let src = self.read_col_slice(len, 4, "eidx vec")?;
        let mut out = Vec::with_capacity(len);
        for i in 0..len {
            out.push(EIdx::of_word(col_u32(src, i)));
        }
        Ok(out)
    }

    fn read_pair_n_e_vec(&mut self) -> Result<Vec<(NIdx, EIdx)>, String> {
        let len = self.read_u32()? as usize;
        let src = self.read_col_slice(len, 8, "pair vec")?;
        let mut out = Vec::with_capacity(len);
        for i in 0..len {
            let off = i * 8;
            let n = NIdx::of_word(u32::from_le_bytes([
                src[off],
                src[off + 1],
                src[off + 2],
                src[off + 3],
            ]));
            let e = EIdx::of_word(u32::from_le_bytes([
                src[off + 4],
                src[off + 5],
                src[off + 6],
                src[off + 7],
            ]));
            out.push((n, e));
        }
        Ok(out)
    }

    fn read_cv(&mut self) -> Result<IConstantVal, String> {
        let name = NIdx::of_word(self.read_u32()?);
        let level_params = self.read_nidx_vec()?;
        let ty = EIdx::of_word(self.read_u32()?);
        Ok(IConstantVal {
            name,
            level_params,
            ty,
        })
    }

    fn read_hint(&mut self) -> Result<ReducibilityHint, String> {
        match self.read_u8()? {
            0 => Ok(ReducibilityHint::Opaque),
            1 => Ok(ReducibilityHint::Abbrev),
            2 => Ok(ReducibilityHint::Regular(self.read_u64()?)),
            other => Err(format!("invalid ReducibilityHint tag {other}")),
        }
    }

    fn read_ind_caps(&mut self) -> Result<IIndCaps, String> {
        let eta = self.read_bool()?;
        let all = self.read_nidx_vec()?;
        let nparams = self.read_u64()?;
        let n_idx = self.read_u64()?;
        let ctors = self.read_nidx_vec()?;
        let never_zero = self.read_bool()?;
        Ok(IIndCaps {
            eta,
            all,
            nparams,
            n_idx,
            ctors,
            never_zero,
        })
    }

    fn read_const_info(&mut self) -> Result<IConstantInfo, String> {
        match self.read_u8()? {
            0 => Ok(IConstantInfo::AxiomInfo(self.read_cv()?)),
            1 => {
                let cv = self.read_cv()?;
                let v = EIdx::of_word(self.read_u32()?);
                let hint = self.read_hint()?;
                Ok(IConstantInfo::DefnInfo(cv, v, hint))
            }
            2 => Ok(IConstantInfo::ThmInfo(self.read_cv()?)),
            3 => {
                let cv = self.read_cv()?;
                let caps = self.read_ind_caps()?;
                Ok(IConstantInfo::IndInfo(cv, caps))
            }
            4 => {
                let cv = self.read_cv()?;
                let a = self.read_u64()?;
                let b = self.read_u64()?;
                let ind = NIdx::of_word(self.read_u32()?);
                Ok(IConstantInfo::CtorInfo(cv, a, b, ind))
            }
            5 => {
                let cv = self.read_cv()?;
                let a = self.read_u64()?;
                let b = self.read_u64()?;
                let k = self.read_bool()?;
                let rlen = self.read_u32()? as usize;
                let mut rules = Vec::with_capacity(self.check_count(rlen as u64, 17, "rec rules")?);
                for _ in 0..rlen {
                    let ctor = NIdx::of_word(self.read_u32()?);
                    let nfields = self.read_u64()?;
                    let fire = match self.read_u8()? {
                        0 => IRecRuleFire::Plain,
                        1 => IRecRuleFire::Levels(self.read_lidx_vec()?),
                        2 => {
                            let lvls = self.read_lidx_vec()?;
                            let pins = self.read_eidx_vec()?;
                            IRecRuleFire::Nested(lvls, pins)
                        }
                        other => return Err(format!("invalid IRecRuleFire tag {other}")),
                    };
                    let rhs = EIdx::of_word(self.read_u32()?);
                    rules.push(IRecRule {
                        ctor,
                        nfields,
                        fire,
                        rhs,
                    });
                }
                Ok(IConstantInfo::RecInfo(cv, a, b, k, rules))
            }
            other => Err(format!("invalid IConstantInfo tag {other}")),
        }
    }
}

#[inline(always)]
fn col_u32(slice: &[u8], i: usize) -> u32 {
    let o = i * 4;
    u32::from_le_bytes([slice[o], slice[o + 1], slice[o + 2], slice[o + 3]])
}

#[inline(always)]
fn col_u64(slice: &[u8], i: usize) -> u64 {
    let o = i * 8;
    u64::from_le_bytes([
        slice[o],
        slice[o + 1],
        slice[o + 2],
        slice[o + 3],
        slice[o + 4],
        slice[o + 5],
        slice[o + 6],
        slice[o + 7],
    ])
}

#[inline]
fn read_u32_le(bytes: &[u8], off: usize) -> u32 {
    u32::from_le_bytes([bytes[off], bytes[off + 1], bytes[off + 2], bytes[off + 3]])
}

#[inline]
fn read_u64_le(bytes: &[u8], off: usize) -> u64 {
    u64::from_le_bytes([
        bytes[off],
        bytes[off + 1],
        bytes[off + 2],
        bytes[off + 3],
        bytes[off + 4],
        bytes[off + 5],
        bytes[off + 6],
        bytes[off + 7],
    ])
}

fn rebuild_tbl_cons<A, I, D, F>(tbl: &mut Tbl<A, I, D>, mk_handle: F)
where
    A: Hashable + Eq2 + Dup,
    I: Dup + ConsHandle,
    D: Dup + DerDefault,
    F: Fn(u32) -> I,
{
    for (row_idx, (node, _)) in tbl.rows.iter().enumerate() {
        let h = mk_handle(row_idx as u32);
        let _ = tbl.cons.insert(&tbl.rows, node, h);
    }
}

fn encode_manifest_section(
    roots: &[String],
    manifest: &[SnapshotManifestEntry],
) -> Result<Vec<u8>, String> {
    let mut out = Vec::with_capacity(256 + manifest.len() * 96);
    out.extend_from_slice(
        &(u32::try_from(roots.len()).map_err(|_| "manifest roots overflow".to_string())?)
            .to_le_bytes(),
    );
    for r in roots {
        let b = r.as_bytes();
        out.extend_from_slice(
            &(u32::try_from(b.len()).map_err(|_| "manifest root str overflow".to_string())?)
                .to_le_bytes(),
        );
        out.extend_from_slice(b);
    }
    out.extend_from_slice(
        &(u32::try_from(manifest.len()).map_err(|_| "manifest entries overflow".to_string())?)
            .to_le_bytes(),
    );
    for m in manifest {
        let kb = m.norm_key.as_bytes();
        let pb = m.path.as_bytes();
        out.extend_from_slice(
            &(u32::try_from(kb.len()).map_err(|_| "manifest norm_key overflow".to_string())?)
                .to_le_bytes(),
        );
        out.extend_from_slice(kb);
        out.extend_from_slice(
            &(u32::try_from(pb.len()).map_err(|_| "manifest path overflow".to_string())?)
                .to_le_bytes(),
        );
        out.extend_from_slice(pb);
        out.extend_from_slice(&m.byte_len.to_le_bytes());
        out.extend_from_slice(&m.mtime_secs.to_le_bytes());
        out.extend_from_slice(&m.mtime_nanos.to_le_bytes());
        out.extend_from_slice(&m.content_hash128);
    }
    Ok(out)
}

fn decode_manifest_section(
    bytes: &[u8],
) -> Result<(Vec<String>, Vec<SnapshotManifestEntry>), String> {
    let mut cr = ColReader::new(bytes);
    let n_roots = cr.read_u32()? as usize;
    let mut roots = Vec::with_capacity(cr.check_count(n_roots as u64, 4, "manifest roots")?);
    for _ in 0..n_roots {
        roots.push(cr.read_string("manifest root")?);
    }
    let n_entries = cr.read_u32()? as usize;
    let mut entries =
        Vec::with_capacity(cr.check_count(n_entries as u64, 44, "manifest entries")?);
    for _ in 0..n_entries {
        let norm_key = cr.read_string("manifest norm_key")?;
        let path = cr.read_string("manifest path")?;
        let byte_len = cr.read_u64()?;
        let mtime_secs = cr.read_u64()?;
        let mtime_nanos = cr.read_u32()?;
        let hslice = cr.take_bytes(16, "manifest hash128")?;
        let mut content_hash128 = [0u8; 16];
        content_hash128.copy_from_slice(hslice);
        entries.push(SnapshotManifestEntry {
            norm_key,
            path,
            byte_len,
            mtime_secs,
            mtime_nanos,
            content_hash128,
        });
    }
    if cr.remaining() != 0 {
        return Err("trailing garbage in snapshot ManifestSection".to_string());
    }
    Ok((roots, entries))
}

fn decode_gpu_section(bytes: &[u8], eligible_jobs_count: usize) -> Result<GpuArenaPacket, String> {
    let mut cr = ColReader::new(bytes);
    let e_nodes_len = cr.read_checked_count(4, "e_nodes")?;
    let meta_nodes_len = cr.read_checked_count(4, "meta_nodes")?;
    let env_tables_len = cr.read_checked_count(4, "env_tables")?;
    let jobs_len = cr.read_checked_count(std::mem::size_of::<GpuJob>(), "jobs")?;

    let mut header = ArenaHeader::default();
    let hdr_bytes = cr.take_bytes(std::mem::size_of::<ArenaHeader>(), "ArenaHeader")?;
    bytemuck::bytes_of_mut(&mut header).copy_from_slice(hdr_bytes);

    let e_nodes = cr.read_u32_vec_len(e_nodes_len)?;
    let meta_nodes = cr.read_u32_vec_len(meta_nodes_len)?;
    let env_tables = cr.read_u32_vec_len(env_tables_len)?;
    let job_bytes = cr.read_col_slice(jobs_len, std::mem::size_of::<GpuJob>(), "jobs")?;
    let mut jobs = vec![GpuJob::default(); jobs_len];
    if !jobs.is_empty() {
        assert!(cfg!(target_endian = "little"));
        bytemuck::cast_slice_mut::<GpuJob, u8>(&mut jobs).copy_from_slice(job_bytes);
    }
    if cr.remaining() != 0 {
        return Err("trailing garbage in snapshot GpuSection".to_string());
    }
    if header.num_jobs as usize != jobs.len() {
        return Err(format!(
            "snapshot ArenaHeader num_jobs mismatch ({} != {})",
            header.num_jobs,
            jobs.len()
        ));
    }

    Ok(GpuArenaPacket {
        header,
        e_nodes,
        meta_nodes,
        env_tables,
        jobs,
        eligible_jobs_count,
        pack_ns: 0,
    })
}

fn write_host_section(sw: &mut ChunkedSnapWriter, env: &LoadedEnvironment) -> Result<(), String> {
    let pers = &env.pers;

    // pers.n.anons
    sw.write_u64(pers.n.anons.rows.len() as u64)?;
    sw.write_u64_col(&pers.n.anons.rows, |(_, d)| *d)?;

    // pers.n.strs (columnar + flat s_words)
    sw.write_u64(pers.n.strs.rows.len() as u64)?;
    sw.write_u32_col(&pers.n.strs.rows, |(n, _)| n.pre.word)?;
    sw.write_u64_col(&pers.n.strs.rows, |(_, d)| *d)?;
    sw.write_u32_col(&pers.n.strs.rows, |(n, _)| n.s.len() as u32)?;
    let total_str_words: u64 = pers.n.strs.rows.iter().map(|(n, _)| n.s.len() as u64).sum();
    sw.write_u64(total_str_words)?;
    for (n, _) in &pers.n.strs.rows {
        sw.write_u32_slice_raw(&n.s)?;
    }

    // pers.n.nums (columnar)
    sw.write_u64(pers.n.nums.rows.len() as u64)?;
    sw.write_u32_col(&pers.n.nums.rows, |(n, _)| n.pre.word)?;
    sw.write_u64_col(&pers.n.nums.rows, |(n, _)| n.n)?;
    sw.write_u64_col(&pers.n.nums.rows, |(_, d)| *d)?;

    // pers.l
    sw.write_u64(pers.l.zeros.rows.len() as u64)?;
    sw.write_u64_col(&pers.l.zeros.rows, |(_, d)| d.hash)?;
    sw.write_u8_col(&pers.l.zeros.rows, |(_, d)| if d.has_param { 1 } else { 0 })?;

    sw.write_u64(pers.l.succs.rows.len() as u64)?;
    sw.write_u32_col(&pers.l.succs.rows, |(n, _)| n.u.word)?;
    sw.write_u64_col(&pers.l.succs.rows, |(_, d)| d.hash)?;
    sw.write_u8_col(&pers.l.succs.rows, |(_, d)| if d.has_param { 1 } else { 0 })?;

    sw.write_u64(pers.l.maxs.rows.len() as u64)?;
    sw.write_u32_col(&pers.l.maxs.rows, |(n, _)| n.u.word)?;
    sw.write_u32_col(&pers.l.maxs.rows, |(n, _)| n.v.word)?;
    sw.write_u64_col(&pers.l.maxs.rows, |(_, d)| d.hash)?;
    sw.write_u8_col(&pers.l.maxs.rows, |(_, d)| if d.has_param { 1 } else { 0 })?;

    sw.write_u64(pers.l.imaxs.rows.len() as u64)?;
    sw.write_u32_col(&pers.l.imaxs.rows, |(n, _)| n.u.word)?;
    sw.write_u32_col(&pers.l.imaxs.rows, |(n, _)| n.v.word)?;
    sw.write_u64_col(&pers.l.imaxs.rows, |(_, d)| d.hash)?;
    sw.write_u8_col(&pers.l.imaxs.rows, |(_, d)| if d.has_param { 1 } else { 0 })?;

    sw.write_u64(pers.l.params.rows.len() as u64)?;
    sw.write_u32_col(&pers.l.params.rows, |(n, _)| n.n.word)?;
    sw.write_u64_col(&pers.l.params.rows, |(_, d)| d.hash)?;
    sw.write_u8_col(&pers.l.params.rows, |(_, d)| if d.has_param { 1 } else { 0 })?;

    // pers.ls (columnar + flat us)
    sw.write_u64(pers.ls.lists.rows.len() as u64)?;
    sw.write_u32_col(&pers.ls.lists.rows, |(n, _)| n.us.len() as u32)?;
    sw.write_u64_col(&pers.ls.lists.rows, |(_, d)| d.hash)?;
    sw.write_u8_col(&pers.ls.lists.rows, |(_, d)| if d.has_param { 1 } else { 0 })?;
    let total_ls_words: u64 = pers.ls.lists.rows.iter().map(|(n, _)| n.us.len() as u64).sum();
    sw.write_u64(total_ls_words)?;
    for (n, _) in &pers.ls.lists.rows {
        sw.write_u32_col(&n.us, |u| u.word)?;
    }

    // pers.e (pure columnar)
    sw.write_u64(pers.e.bvars.rows.len() as u64)?;
    sw.write_u64_col(&pers.e.bvars.rows, |(n, _)| n.i)?;
    sw.write_u64_col(&pers.e.bvars.rows, |(_, d)| *d)?;

    sw.write_u64(pers.e.fvars.rows.len() as u64)?;
    sw.write_u64_col(&pers.e.fvars.rows, |(n, _)| n.idx)?;
    sw.write_u32_col(&pers.e.fvars.rows, |(n, _)| n.ty.word)?;
    sw.write_u64_col(&pers.e.fvars.rows, |(_, d)| *d)?;

    sw.write_u64(pers.e.sorts.rows.len() as u64)?;
    sw.write_u32_col(&pers.e.sorts.rows, |(n, _)| n.u.word)?;
    sw.write_u64_col(&pers.e.sorts.rows, |(_, d)| *d)?;

    sw.write_u64(pers.e.consts.rows.len() as u64)?;
    sw.write_u32_col(&pers.e.consts.rows, |(n, _)| n.n.word)?;
    sw.write_u32_col(&pers.e.consts.rows, |(n, _)| n.us.word)?;
    sw.write_u64_col(&pers.e.consts.rows, |(_, d)| *d)?;

    sw.write_u64(pers.e.apps.rows.len() as u64)?;
    sw.write_u32_col(&pers.e.apps.rows, |(n, _)| n.f.word)?;
    sw.write_u32_col(&pers.e.apps.rows, |(n, _)| n.a.word)?;
    sw.write_u64_col(&pers.e.apps.rows, |(_, d)| *d)?;

    sw.write_u64(pers.e.lams.rows.len() as u64)?;
    sw.write_u32_col(&pers.e.lams.rows, |(n, _)| n.ty.word)?;
    sw.write_u32_col(&pers.e.lams.rows, |(n, _)| n.body.word)?;
    sw.write_u64_col(&pers.e.lams.rows, |(_, d)| *d)?;

    sw.write_u64(pers.e.foralls.rows.len() as u64)?;
    sw.write_u32_col(&pers.e.foralls.rows, |(n, _)| n.ty.word)?;
    sw.write_u32_col(&pers.e.foralls.rows, |(n, _)| n.body.word)?;
    sw.write_u64_col(&pers.e.foralls.rows, |(_, d)| *d)?;

    sw.write_u64(pers.e.lets.rows.len() as u64)?;
    sw.write_u32_col(&pers.e.lets.rows, |(n, _)| n.ty.word)?;
    sw.write_u32_col(&pers.e.lets.rows, |(n, _)| n.val.word)?;
    sw.write_u32_col(&pers.e.lets.rows, |(n, _)| n.body.word)?;
    sw.write_u64_col(&pers.e.lets.rows, |(_, d)| *d)?;

    // pers.e.lits (columnar + flat nat_limbs / str_words)
    sw.write_u64(pers.e.lits.rows.len() as u64)?;
    sw.write_u8_col(&pers.e.lits.rows, |(n, _)| match &n.l {
        Literal::NatVal(_) => 0,
        Literal::StrVal(_) => 1,
    })?;
    sw.write_u32_col(&pers.e.lits.rows, |(n, _)| match &n.l {
        Literal::NatVal(nat) => nat.limbs.len() as u32,
        Literal::StrVal(s) => s.len() as u32,
    })?;
    sw.write_u64_col(&pers.e.lits.rows, |(_, d)| *d)?;
    let total_lit_nat_limbs: u64 = pers
        .e
        .lits
        .rows
        .iter()
        .map(|(n, _)| match &n.l {
            Literal::NatVal(nat) => nat.limbs.len() as u64,
            Literal::StrVal(_) => 0,
        })
        .sum();
    let total_lit_str_words: u64 = pers
        .e
        .lits
        .rows
        .iter()
        .map(|(n, _)| match &n.l {
            Literal::NatVal(_) => 0,
            Literal::StrVal(s) => s.len() as u64,
        })
        .sum();
    sw.write_u64(total_lit_nat_limbs)?;
    for (n, _) in &pers.e.lits.rows {
        if let Literal::NatVal(nat) = &n.l {
            sw.write_u64_slice_raw(&nat.limbs)?;
        }
    }
    sw.write_u64(total_lit_str_words)?;
    for (n, _) in &pers.e.lits.rows {
        if let Literal::StrVal(s) = &n.l {
            sw.write_u32_slice_raw(s)?;
        }
    }

    // pers.e.projs (columnar)
    sw.write_u64(pers.e.projs.rows.len() as u64)?;
    sw.write_u32_col(&pers.e.projs.rows, |(n, _)| n.n.word)?;
    sw.write_u64_col(&pers.e.projs.rows, |(n, _)| n.i)?;
    sw.write_u32_col(&pers.e.projs.rows, |(n, _)| n.e.word)?;
    sw.write_u64_col(&pers.e.projs.rows, |(_, d)| *d)?;

    // pers.env
    sw.write_u64(pers.env.consts.len() as u64)?;
    for ci in &pers.env.consts {
        sw.write_const_info(ci)?;
    }
    sw.write_u64(pers.env.tables.len() as u64)?;
    for (slot_idx, tbl) in pers.env.tables.iter().enumerate() {
        let rec_pos = pers
            .env
            .tbls
            .get(&tbl.struct_name)
            .map(|(r, _)| *r)
            .unwrap_or(slot_idx as u64);
        sw.write_u64(rec_pos)?;
        sw.write_u32(tbl.struct_name.word)?;
        sw.write_nidx_vec(&tbl.level_params)?;
        sw.write_u64(tbl.num_params)?;
        sw.write_u32(tbl.ctor.word)?;
        sw.write_u64(tbl.num_fields)?;
        sw.write_eidx_vec(&tbl.bodies)?;
    }
    sw.write_u64_vec(&pers.env.firsts)?;
    sw.write_u64(pers.env.next)?;

    // pins (columnar)
    sw.write_nidx_vec(&env.pins.names)?;
    sw.write_nidx_vec(&env.pins.reserved)?;
    sw.write_u32(env.pins.empty_levels.word)?;
    sw.write_u32(env.pins.zero_level.word)?;
    sw.write_u32(env.pins.sort_one.word)?;
    sw.write_u64_vec(&env.pins.max_nat_size.limbs)?;

    // ipins
    sw.write_u64(env.ipins.len() as u64)?;
    for p in &env.ipins {
        sw.write_u32_vec(&p.toolchain)?;
        sw.write_u32(p.div_pin.word)?;
        sw.write_u32(p.mod_pin.word)?;
        sw.write_u32(p.gcd_pin.word)?;
        sw.write_u32(p.land_pin.word)?;
        sw.write_u32(p.lor_pin.word)?;
        sw.write_u32(p.xor_pin.word)?;
        sw.write_u32(p.shift_left_pin.word)?;
        sw.write_u32(p.shift_right_pin.word)?;
        sw.write_eidx_vec(&p.div_proofs)?;
        sw.write_eidx_vec(&p.mod_proofs)?;
        sw.write_eidx_vec(&p.gcd_proofs)?;
        sw.write_eidx_vec(&p.land_proofs)?;
        sw.write_eidx_vec(&p.lor_proofs)?;
        sw.write_eidx_vec(&p.xor_proofs)?;
        sw.write_eidx_vec(&p.shift_left_proofs)?;
        sw.write_eidx_vec(&p.shift_right_proofs)?;
        sw.write_pair_n_e_vec(&p.div_type_pins)?;
        sw.write_pair_n_e_vec(&p.mod_type_pins)?;
        sw.write_pair_n_e_vec(&p.gcd_type_pins)?;
        sw.write_pair_n_e_vec(&p.land_type_pins)?;
        sw.write_pair_n_e_vec(&p.lor_type_pins)?;
        sw.write_pair_n_e_vec(&p.xor_type_pins)?;
        sw.write_pair_n_e_vec(&p.shift_left_type_pins)?;
        sw.write_pair_n_e_vec(&p.shift_right_type_pins)?;
    }

    // decls (columnar for Axiom/Defn/Thm/Opaque/Quot + flat Ind blocks)
    sw.write_u64(env.decls.len() as u64)?;
    sw.write_u8_col(&env.decls, |d| match d {
        IDeclaration::AxiomDecl(_) => 0,
        IDeclaration::DefnDecl(_, _, _) => 1,
        IDeclaration::ThmDecl(_, _) => 2,
        IDeclaration::OpaqueDecl(_, _) => 3,
        IDeclaration::IndDecl(_, _) => 4,
        IDeclaration::QuotDecl(_, _) => 5,
    })?;
    sw.write_u8_col(&env.decls, |d| match d {
        IDeclaration::DefnDecl(_, _, hint) => match hint {
            ReducibilityHint::Opaque => 0,
            ReducibilityHint::Abbrev => 1,
            ReducibilityHint::Regular(_) => 2,
        },
        IDeclaration::QuotDecl(qk, _) => match qk {
            QuotKind::Type => 0,
            QuotKind::Ctor => 1,
            QuotKind::Lift => 2,
            QuotKind::Ind => 3,
            QuotKind::Sound => 4,
        },
        _ => 0,
    })?;
    sw.write_u32_col(&env.decls, |d| match d {
        IDeclaration::DefnDecl(_, v, _)
        | IDeclaration::ThmDecl(_, v)
        | IDeclaration::OpaqueDecl(_, v) => v.word,
        IDeclaration::IndDecl(block, _) => block.len() as u32,
        _ => 0,
    })?;
    sw.write_u64_col(&env.decls, |d| match d {
        IDeclaration::DefnDecl(_, _, ReducibilityHint::Regular(h)) => *h,
        IDeclaration::IndDecl(_, nparams) => *nparams,
        _ => 0,
    })?;
    let cv_count: u64 = env
        .decls
        .iter()
        .filter(|d| !matches!(d, IDeclaration::IndDecl(_, _)))
        .count() as u64;
    let total_cv_lparams: u64 = env
        .decls
        .iter()
        .map(|d| match d {
            IDeclaration::AxiomDecl(cv)
            | IDeclaration::DefnDecl(cv, _, _)
            | IDeclaration::ThmDecl(cv, _)
            | IDeclaration::OpaqueDecl(cv, _)
            | IDeclaration::QuotDecl(_, cv) => cv.level_params.len() as u64,
            IDeclaration::IndDecl(_, _) => 0,
        })
        .sum();
    let total_ind_cis: u64 = env
        .decls
        .iter()
        .map(|d| match d {
            IDeclaration::IndDecl(b, _) => b.len() as u64,
            _ => 0,
        })
        .sum();
    sw.write_u64(cv_count)?;
    sw.write_u64(total_cv_lparams)?;
    sw.write_u64(total_ind_cis)?;

    for d in &env.decls {
        if let IDeclaration::AxiomDecl(cv)
        | IDeclaration::DefnDecl(cv, _, _)
        | IDeclaration::ThmDecl(cv, _)
        | IDeclaration::OpaqueDecl(cv, _)
        | IDeclaration::QuotDecl(_, cv) = d
        {
            sw.write_u32(cv.name.word)?;
        }
    }
    for d in &env.decls {
        if let IDeclaration::AxiomDecl(cv)
        | IDeclaration::DefnDecl(cv, _, _)
        | IDeclaration::ThmDecl(cv, _)
        | IDeclaration::OpaqueDecl(cv, _)
        | IDeclaration::QuotDecl(_, cv) = d
        {
            sw.write_u32(cv.ty.word)?;
        }
    }
    for d in &env.decls {
        if let IDeclaration::AxiomDecl(cv)
        | IDeclaration::DefnDecl(cv, _, _)
        | IDeclaration::ThmDecl(cv, _)
        | IDeclaration::OpaqueDecl(cv, _)
        | IDeclaration::QuotDecl(_, cv) = d
        {
            sw.write_u32(cv.level_params.len() as u32)?;
        }
    }
    for d in &env.decls {
        if let IDeclaration::AxiomDecl(cv)
        | IDeclaration::DefnDecl(cv, _, _)
        | IDeclaration::ThmDecl(cv, _)
        | IDeclaration::OpaqueDecl(cv, _)
        | IDeclaration::QuotDecl(_, cv) = d
        {
            for lp in &cv.level_params {
                sw.write_u32(lp.word)?;
            }
        }
    }
    for d in &env.decls {
        if let IDeclaration::IndDecl(block, _) = d {
            for ci in block {
                sw.write_const_info(ci)?;
            }
        }
    }

    // module_hashes
    sw.write_u64(env.module_hashes.len() as u64)?;
    for (mname, hash) in &env.module_hashes {
        let b = mname.as_bytes();
        sw.write_u32(u32::try_from(b.len()).map_err(|_| "module name overflow".to_string())?)?;
        sw.write_bytes(b)?;
        sw.write_bytes(hash)?;
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn decode_host_section_and_env(
    host_bytes: &[u8],
    closure_hash: [u8; 16],
    closure_roots: Vec<String>,
    closure_manifest: Vec<SnapshotManifestEntry>,
    file_records: usize,
    preverified_prefix: usize,
    synthesized: u64,
    hoisted: usize,
    thm_materialized_count: usize,
    load_ns: u128,
) -> Result<LoadedEnvironment, String> {
    let mut cr = ColReader::new(host_bytes);

    // pers.n.anons
    let n_anons = cr.read_checked_count(8, "anons")?;
    let anon_ders = cr.read_col_slice(n_anons, 8, "anons.der")?;
    let mut anons: Tbl<AnonNode, NIdx, u64> = Tbl::empty();
    anons.rows.reserve_exact(n_anons);
    for i in 0..n_anons {
        anons.rows.push((AnonNode {}, col_u64(anon_ders, i)));
    }

    // pers.n.strs
    let n_strs = cr.read_checked_count(16, "strs")?;
    let str_pres = cr.read_col_slice(n_strs, 4, "strs.pre")?;
    let str_ders = cr.read_col_slice(n_strs, 8, "strs.der")?;
    let str_lens = cr.read_col_slice(n_strs, 4, "strs.len")?;
    let total_str_words = cr.read_checked_count(4, "strs.flat")?;
    let str_flat = cr.read_col_slice(total_str_words, 4, "strs.words")?;
    let mut strs: Tbl<StrNode, NIdx, u64> = Tbl::empty();
    strs.rows.reserve_exact(n_strs);
    let mut flat_pos = 0usize;
    for i in 0..n_strs {
        let slen = col_u32(str_lens, i) as usize;
        if flat_pos + slen > total_str_words {
            return Err("corrupt strs flat slice bounds in snapshot".to_string());
        }
        let mut s = Vec::with_capacity(slen);
        for k in 0..slen {
            s.push(col_u32(str_flat, flat_pos + k));
        }
        flat_pos += slen;
        strs.rows.push((
            StrNode {
                pre: NIdx::of_word(col_u32(str_pres, i)),
                s,
            },
            col_u64(str_ders, i),
        ));
    }

    // pers.n.nums
    let n_nums = cr.read_checked_count(20, "nums")?;
    let num_pres = cr.read_col_slice(n_nums, 4, "nums.pre")?;
    let num_ns = cr.read_col_slice(n_nums, 8, "nums.n")?;
    let num_ders = cr.read_col_slice(n_nums, 8, "nums.der")?;
    let mut nums: Tbl<NumNode, NIdx, u64> = Tbl::empty();
    nums.rows.reserve_exact(n_nums);
    for i in 0..n_nums {
        nums.rows.push((
            NumNode {
                pre: NIdx::of_word(col_u32(num_pres, i)),
                n: col_u64(num_ns, i),
            },
            col_u64(num_ders, i),
        ));
    }

    // pers.l
    let n_zeros = cr.read_checked_count(9, "zeros")?;
    let z_hashes = cr.read_col_slice(n_zeros, 8, "zeros.hash")?;
    let z_hp = cr.read_col_slice(n_zeros, 1, "zeros.hp")?;
    let mut zeros: Tbl<ZeroNode, LIdx, LDer> = Tbl::empty();
    zeros.rows.reserve_exact(n_zeros);
    for i in 0..n_zeros {
        zeros.rows.push((
            ZeroNode {},
            LDer {
                hash: col_u64(z_hashes, i),
                has_param: z_hp[i] != 0,
            },
        ));
    }

    let n_succs = cr.read_checked_count(13, "succs")?;
    let sc_us = cr.read_col_slice(n_succs, 4, "succs.u")?;
    let sc_hashes = cr.read_col_slice(n_succs, 8, "succs.hash")?;
    let sc_hp = cr.read_col_slice(n_succs, 1, "succs.hp")?;
    let mut succs: Tbl<SuccNode, LIdx, LDer> = Tbl::empty();
    succs.rows.reserve_exact(n_succs);
    for i in 0..n_succs {
        succs.rows.push((
            SuccNode {
                u: LIdx::of_word(col_u32(sc_us, i)),
            },
            LDer {
                hash: col_u64(sc_hashes, i),
                has_param: sc_hp[i] != 0,
            },
        ));
    }

    let n_maxs = cr.read_checked_count(17, "maxs")?;
    let mx_us = cr.read_col_slice(n_maxs, 4, "maxs.u")?;
    let mx_vs = cr.read_col_slice(n_maxs, 4, "maxs.v")?;
    let mx_hashes = cr.read_col_slice(n_maxs, 8, "maxs.hash")?;
    let mx_hp = cr.read_col_slice(n_maxs, 1, "maxs.hp")?;
    let mut maxs: Tbl<BinLNode, LIdx, LDer> = Tbl::empty();
    maxs.rows.reserve_exact(n_maxs);
    for i in 0..n_maxs {
        maxs.rows.push((
            BinLNode {
                u: LIdx::of_word(col_u32(mx_us, i)),
                v: LIdx::of_word(col_u32(mx_vs, i)),
            },
            LDer {
                hash: col_u64(mx_hashes, i),
                has_param: mx_hp[i] != 0,
            },
        ));
    }

    let n_imaxs = cr.read_checked_count(17, "imaxs")?;
    let imx_us = cr.read_col_slice(n_imaxs, 4, "imaxs.u")?;
    let imx_vs = cr.read_col_slice(n_imaxs, 4, "imaxs.v")?;
    let imx_hashes = cr.read_col_slice(n_imaxs, 8, "imaxs.hash")?;
    let imx_hp = cr.read_col_slice(n_imaxs, 1, "imaxs.hp")?;
    let mut imaxs: Tbl<BinLNode, LIdx, LDer> = Tbl::empty();
    imaxs.rows.reserve_exact(n_imaxs);
    for i in 0..n_imaxs {
        imaxs.rows.push((
            BinLNode {
                u: LIdx::of_word(col_u32(imx_us, i)),
                v: LIdx::of_word(col_u32(imx_vs, i)),
            },
            LDer {
                hash: col_u64(imx_hashes, i),
                has_param: imx_hp[i] != 0,
            },
        ));
    }

    let n_params = cr.read_checked_count(13, "params")?;
    let pr_ns = cr.read_col_slice(n_params, 4, "params.n")?;
    let pr_hashes = cr.read_col_slice(n_params, 8, "params.hash")?;
    let pr_hp = cr.read_col_slice(n_params, 1, "params.hp")?;
    let mut params: Tbl<ParamNode, LIdx, LDer> = Tbl::empty();
    params.rows.reserve_exact(n_params);
    for i in 0..n_params {
        params.rows.push((
            ParamNode {
                n: NIdx::of_word(col_u32(pr_ns, i)),
            },
            LDer {
                hash: col_u64(pr_hashes, i),
                has_param: pr_hp[i] != 0,
            },
        ));
    }

    // pers.ls
    let n_lists = cr.read_checked_count(13, "lists")?;
    let ls_lens = cr.read_col_slice(n_lists, 4, "lists.len")?;
    let ls_hashes = cr.read_col_slice(n_lists, 8, "lists.hash")?;
    let ls_hp = cr.read_col_slice(n_lists, 1, "lists.hp")?;
    let total_ls_words = cr.read_checked_count(4, "lists.flat")?;
    let ls_flat = cr.read_col_slice(total_ls_words, 4, "lists.words")?;
    let mut lists: Tbl<ListNode, LsIdx, LDer> = Tbl::empty();
    lists.rows.reserve_exact(n_lists);
    let mut ls_pos = 0usize;
    for i in 0..n_lists {
        let ulen = col_u32(ls_lens, i) as usize;
        if ls_pos + ulen > total_ls_words {
            return Err("corrupt lists flat slice bounds in snapshot".to_string());
        }
        let mut us = Vec::with_capacity(ulen);
        for k in 0..ulen {
            us.push(LIdx::of_word(col_u32(ls_flat, ls_pos + k)));
        }
        ls_pos += ulen;
        lists.rows.push((
            ListNode { us },
            LDer {
                hash: col_u64(ls_hashes, i),
                has_param: ls_hp[i] != 0,
            },
        ));
    }

    // pers.e
    let n_bvars = cr.read_checked_count(16, "bvars")?;
    let bv_is = cr.read_col_slice(n_bvars, 8, "bvars.i")?;
    let bv_ders = cr.read_col_slice(n_bvars, 8, "bvars.der")?;
    let mut bvars: Tbl<BVarNode, EIdx, u64> = Tbl::empty();
    bvars.rows.reserve_exact(n_bvars);
    for i in 0..n_bvars {
        bvars
            .rows
            .push((BVarNode { i: col_u64(bv_is, i) }, col_u64(bv_ders, i)));
    }

    let n_fvars = cr.read_checked_count(20, "fvars")?;
    let fv_idxs = cr.read_col_slice(n_fvars, 8, "fvars.idx")?;
    let fv_tys = cr.read_col_slice(n_fvars, 4, "fvars.ty")?;
    let fv_ders = cr.read_col_slice(n_fvars, 8, "fvars.der")?;
    let mut fvars: Tbl<FVarNode, EIdx, u64> = Tbl::empty();
    fvars.rows.reserve_exact(n_fvars);
    for i in 0..n_fvars {
        fvars.rows.push((
            FVarNode {
                idx: col_u64(fv_idxs, i),
                ty: EIdx::of_word(col_u32(fv_tys, i)),
            },
            col_u64(fv_ders, i),
        ));
    }

    let n_sorts = cr.read_checked_count(12, "sorts")?;
    let sr_us = cr.read_col_slice(n_sorts, 4, "sorts.u")?;
    let sr_ders = cr.read_col_slice(n_sorts, 8, "sorts.der")?;
    let mut sorts: Tbl<SortNode, EIdx, u64> = Tbl::empty();
    sorts.rows.reserve_exact(n_sorts);
    for i in 0..n_sorts {
        sorts.rows.push((
            SortNode {
                u: LIdx::of_word(col_u32(sr_us, i)),
            },
            col_u64(sr_ders, i),
        ));
    }

    let n_e_consts = cr.read_checked_count(16, "e_consts")?;
    let ec_ns = cr.read_col_slice(n_e_consts, 4, "e_consts.n")?;
    let ec_uss = cr.read_col_slice(n_e_consts, 4, "e_consts.us")?;
    let ec_ders = cr.read_col_slice(n_e_consts, 8, "e_consts.der")?;
    let mut e_consts: Tbl<ConstNode, EIdx, u64> = Tbl::empty();
    e_consts.rows.reserve_exact(n_e_consts);
    for i in 0..n_e_consts {
        e_consts.rows.push((
            ConstNode {
                n: NIdx::of_word(col_u32(ec_ns, i)),
                us: LsIdx::of_word(col_u32(ec_uss, i)),
            },
            col_u64(ec_ders, i),
        ));
    }

    let n_apps = cr.read_checked_count(16, "apps")?;
    let ap_fs = cr.read_col_slice(n_apps, 4, "apps.f")?;
    let ap_as = cr.read_col_slice(n_apps, 4, "apps.a")?;
    let ap_ders = cr.read_col_slice(n_apps, 8, "apps.der")?;
    let mut apps: Tbl<AppNode, EIdx, u64> = Tbl::empty();
    apps.rows.reserve_exact(n_apps);
    for i in 0..n_apps {
        apps.rows.push((
            AppNode {
                f: EIdx::of_word(col_u32(ap_fs, i)),
                a: EIdx::of_word(col_u32(ap_as, i)),
            },
            col_u64(ap_ders, i),
        ));
    }

    let n_lams = cr.read_checked_count(16, "lams")?;
    let lm_tys = cr.read_col_slice(n_lams, 4, "lams.ty")?;
    let lm_bodies = cr.read_col_slice(n_lams, 4, "lams.body")?;
    let lm_ders = cr.read_col_slice(n_lams, 8, "lams.der")?;
    let mut lams: Tbl<BindNode, EIdx, u64> = Tbl::empty();
    lams.rows.reserve_exact(n_lams);
    for i in 0..n_lams {
        lams.rows.push((
            BindNode {
                ty: EIdx::of_word(col_u32(lm_tys, i)),
                body: EIdx::of_word(col_u32(lm_bodies, i)),
            },
            col_u64(lm_ders, i),
        ));
    }

    let n_foralls = cr.read_checked_count(16, "foralls")?;
    let fa_tys = cr.read_col_slice(n_foralls, 4, "foralls.ty")?;
    let fa_bodies = cr.read_col_slice(n_foralls, 4, "foralls.body")?;
    let fa_ders = cr.read_col_slice(n_foralls, 8, "foralls.der")?;
    let mut foralls: Tbl<BindNode, EIdx, u64> = Tbl::empty();
    foralls.rows.reserve_exact(n_foralls);
    for i in 0..n_foralls {
        foralls.rows.push((
            BindNode {
                ty: EIdx::of_word(col_u32(fa_tys, i)),
                body: EIdx::of_word(col_u32(fa_bodies, i)),
            },
            col_u64(fa_ders, i),
        ));
    }

    let n_lets = cr.read_checked_count(20, "lets")?;
    let lt_tys = cr.read_col_slice(n_lets, 4, "lets.ty")?;
    let lt_vals = cr.read_col_slice(n_lets, 4, "lets.val")?;
    let lt_bodies = cr.read_col_slice(n_lets, 4, "lets.body")?;
    let lt_ders = cr.read_col_slice(n_lets, 8, "lets.der")?;
    let mut lets: Tbl<LetNode, EIdx, u64> = Tbl::empty();
    lets.rows.reserve_exact(n_lets);
    for i in 0..n_lets {
        lets.rows.push((
            LetNode {
                ty: EIdx::of_word(col_u32(lt_tys, i)),
                val: EIdx::of_word(col_u32(lt_vals, i)),
                body: EIdx::of_word(col_u32(lt_bodies, i)),
            },
            col_u64(lt_ders, i),
        ));
    }

    // pers.e.lits
    let n_lits = cr.read_checked_count(13, "lits")?;
    let lit_tags = cr.read_col_slice(n_lits, 1, "lits.tag")?;
    let lit_lens = cr.read_col_slice(n_lits, 4, "lits.len")?;
    let lit_ders = cr.read_col_slice(n_lits, 8, "lits.der")?;
    let total_lit_nats = cr.read_checked_count(8, "lits.nat_flat")?;
    let lit_nat_flat = cr.read_col_slice(total_lit_nats, 8, "lits.nat_words")?;
    let total_lit_strs = cr.read_checked_count(4, "lits.str_flat")?;
    let lit_str_flat = cr.read_col_slice(total_lit_strs, 4, "lits.str_words")?;
    let mut lits: Tbl<LitNode, EIdx, u64> = Tbl::empty();
    lits.rows.reserve_exact(n_lits);
    let mut nat_pos = 0usize;
    let mut str_pos = 0usize;
    for i in 0..n_lits {
        let len = col_u32(lit_lens, i) as usize;
        let lit = match lit_tags[i] {
            0 => {
                if nat_pos + len > total_lit_nats {
                    return Err("corrupt lits nat flat bounds in snapshot".to_string());
                }
                let mut limbs = Vec::with_capacity(len);
                for k in 0..len {
                    limbs.push(col_u64(lit_nat_flat, nat_pos + k));
                }
                nat_pos += len;
                literal_nat(Nat { limbs })
            }
            1 => {
                if str_pos + len > total_lit_strs {
                    return Err("corrupt lits str flat bounds in snapshot".to_string());
                }
                let mut s = Vec::with_capacity(len);
                for k in 0..len {
                    s.push(col_u32(lit_str_flat, str_pos + k));
                }
                str_pos += len;
                literal_str(s)
            }
            other => return Err(format!("invalid Literal tag {other}")),
        };
        lits.rows.push((LitNode { l: lit }, col_u64(lit_ders, i)));
    }

    // pers.e.projs
    let n_projs = cr.read_checked_count(24, "projs")?;
    let pj_ns = cr.read_col_slice(n_projs, 4, "projs.n")?;
    let pj_is = cr.read_col_slice(n_projs, 8, "projs.i")?;
    let pj_es = cr.read_col_slice(n_projs, 4, "projs.e")?;
    let pj_ders = cr.read_col_slice(n_projs, 8, "projs.der")?;
    let mut projs: Tbl<ProjNode, EIdx, u64> = Tbl::empty();
    projs.rows.reserve_exact(n_projs);
    for i in 0..n_projs {
        projs.rows.push((
            ProjNode {
                n: NIdx::of_word(col_u32(pj_ns, i)),
                i: col_u64(pj_is, i),
                e: EIdx::of_word(col_u32(pj_es, i)),
            },
            col_u64(pj_ders, i),
        ));
    }

    // pers.env
    let n_env_consts = cr.read_checked_count(13, "env consts")?;
    let mut env_consts = Vec::with_capacity(n_env_consts);
    for _ in 0..n_env_consts {
        env_consts.push(cr.read_const_info()?);
    }

    let n_env_tables = cr.read_checked_count(36, "env tables")?;
    let mut table_pairs: Vec<(u64, IProjTable)> = Vec::with_capacity(n_env_tables);
    for _ in 0..n_env_tables {
        let rec_pos = cr.read_u64()?;
        let struct_name = NIdx::of_word(cr.read_u32()?);
        let level_params = cr.read_nidx_vec()?;
        let num_params = cr.read_u64()?;
        let ctor = NIdx::of_word(cr.read_u32()?);
        let num_fields = cr.read_u64()?;
        let bodies = cr.read_eidx_vec()?;
        table_pairs.push((
            rec_pos,
            IProjTable {
                struct_name,
                level_params,
                num_params,
                ctor,
                num_fields,
                bodies,
            },
        ));
    }
    let firsts = cr.read_u64_vec()?;
    let next = cr.read_u64()?;

    // pins
    let pins = Pins {
        names: cr.read_nidx_vec()?,
        reserved: cr.read_nidx_vec()?,
        empty_levels: LsIdx::of_word(cr.read_u32()?),
        zero_level: LIdx::of_word(cr.read_u32()?),
        sort_one: EIdx::of_word(cr.read_u32()?),
        max_nat_size: Nat {
            limbs: cr.read_u64_vec()?,
        },
    };

    // ipins
    let n_ipins = cr.read_checked_count(96, "ipins")?;
    let mut ipins = Vec::with_capacity(n_ipins);
    for _ in 0..n_ipins {
        ipins.push(INatOpPinSet {
            toolchain: cr.read_u32_vec()?,
            div_pin: EIdx::of_word(cr.read_u32()?),
            mod_pin: EIdx::of_word(cr.read_u32()?),
            gcd_pin: EIdx::of_word(cr.read_u32()?),
            land_pin: EIdx::of_word(cr.read_u32()?),
            lor_pin: EIdx::of_word(cr.read_u32()?),
            xor_pin: EIdx::of_word(cr.read_u32()?),
            shift_left_pin: EIdx::of_word(cr.read_u32()?),
            shift_right_pin: EIdx::of_word(cr.read_u32()?),
            div_proofs: cr.read_eidx_vec()?,
            mod_proofs: cr.read_eidx_vec()?,
            gcd_proofs: cr.read_eidx_vec()?,
            land_proofs: cr.read_eidx_vec()?,
            lor_proofs: cr.read_eidx_vec()?,
            xor_proofs: cr.read_eidx_vec()?,
            shift_left_proofs: cr.read_eidx_vec()?,
            shift_right_proofs: cr.read_eidx_vec()?,
            div_type_pins: cr.read_pair_n_e_vec()?,
            mod_type_pins: cr.read_pair_n_e_vec()?,
            gcd_type_pins: cr.read_pair_n_e_vec()?,
            land_type_pins: cr.read_pair_n_e_vec()?,
            lor_type_pins: cr.read_pair_n_e_vec()?,
            xor_type_pins: cr.read_pair_n_e_vec()?,
            shift_left_type_pins: cr.read_pair_n_e_vec()?,
            shift_right_type_pins: cr.read_pair_n_e_vec()?,
        });
    }

    // decls (columnar)
    let n_decls = cr.read_checked_count(14, "decls")?;
    let d_tags = cr.read_col_slice(n_decls, 1, "decls.tag")?;
    let d_subtags = cr.read_col_slice(n_decls, 1, "decls.subtag")?;
    let d_vals = cr.read_col_slice(n_decls, 4, "decls.val")?;
    let d_auxs = cr.read_col_slice(n_decls, 8, "decls.aux")?;
    let cv_count = cr.read_checked_count(12, "decls.cv_count")?;
    let total_cv_lparams = cr.read_checked_count(4, "decls.cv_lparams_total")?;
    let total_ind_cis = cr.read_checked_count(13, "decls.ind_cis_total")?;

    let cv_names = cr.read_col_slice(cv_count, 4, "decls.cv_names")?;
    let cv_tys = cr.read_col_slice(cv_count, 4, "decls.cv_tys")?;
    let cv_lp_lens = cr.read_col_slice(cv_count, 4, "decls.cv_lp_lens")?;
    let cv_lp_flat = cr.read_col_slice(total_cv_lparams, 4, "decls.cv_lp_flat")?;

    let mut decls = Vec::with_capacity(n_decls);
    let mut cv_idx = 0usize;
    let mut lp_pos = 0usize;
    let mut ind_cis_seen = 0usize;

    for i in 0..n_decls {
        let tag = d_tags[i];
        let sub = d_subtags[i];
        let val_w = col_u32(d_vals, i);
        let aux = col_u64(d_auxs, i);

        if tag == 4 {
            let blen = val_w as usize;
            if ind_cis_seen + blen > total_ind_cis {
                return Err("corrupt ind block count in snapshot".to_string());
            }
            let mut block = Vec::with_capacity(blen);
            for _ in 0..blen {
                block.push(cr.read_const_info()?);
            }
            ind_cis_seen += blen;
            decls.push(IDeclaration::IndDecl(block, aux));
            continue;
        }

        if cv_idx >= cv_count {
            return Err("corrupt cv_count in snapshot decls".to_string());
        }
        let name = NIdx::of_word(col_u32(cv_names, cv_idx));
        let ty = EIdx::of_word(col_u32(cv_tys, cv_idx));
        let lp_len = col_u32(cv_lp_lens, cv_idx) as usize;
        cv_idx += 1;
        if lp_pos + lp_len > total_cv_lparams {
            return Err("corrupt cv level_params slice bounds in snapshot".to_string());
        }
        let mut level_params = Vec::with_capacity(lp_len);
        for k in 0..lp_len {
            level_params.push(NIdx::of_word(col_u32(cv_lp_flat, lp_pos + k)));
        }
        lp_pos += lp_len;
        let cv = IConstantVal {
            name,
            level_params,
            ty,
        };

        let d = match tag {
            0 => IDeclaration::AxiomDecl(cv),
            1 => {
                let hint = match sub {
                    0 => ReducibilityHint::Opaque,
                    1 => ReducibilityHint::Abbrev,
                    2 => ReducibilityHint::Regular(aux),
                    other => return Err(format!("invalid ReducibilityHint subtag {other}")),
                };
                IDeclaration::DefnDecl(cv, EIdx::of_word(val_w), hint)
            }
            2 => IDeclaration::ThmDecl(cv, EIdx::of_word(val_w)),
            3 => IDeclaration::OpaqueDecl(cv, EIdx::of_word(val_w)),
            5 => {
                let qk = match sub {
                    0 => QuotKind::Type,
                    1 => QuotKind::Ctor,
                    2 => QuotKind::Lift,
                    3 => QuotKind::Ind,
                    4 => QuotKind::Sound,
                    other => return Err(format!("invalid QuotKind subtag {other}")),
                };
                IDeclaration::QuotDecl(qk, cv)
            }
            other => return Err(format!("invalid IDeclaration tag {other}")),
        };
        decls.push(d);
    }

    // module_hashes
    let n_mods = cr.read_checked_count(20, "module_hashes")?;
    let mut module_hashes = HashMap::with_capacity(n_mods);
    for _ in 0..n_mods {
        let mname = cr.read_string("module_name")?;
        let hb = cr.take_bytes(16, "module_hash128")?;
        let mut fp = [0u8; 16];
        fp.copy_from_slice(hb);
        module_hashes.insert(mname, fp);
    }

    if cr.remaining() != 0 {
        return Err(format!(
            "trailing {} unread bytes in snapshot HostSection",
            cr.remaining()
        ));
    }

    let t_idx = Instant::now();
    let mut idx = HashMap2::with_capacity((env_consts.len() * 2).max(32));
    let mut tbls = HashMap2::with_capacity((table_pairs.len() * 2).max(32));
    let mut env_tables = Vec::with_capacity(table_pairs.len());

    rayon::scope(|s| {
        s.spawn(|_| {
            for (slot, ci) in env_consts.iter().enumerate() {
                let n = i_constant_info_name(ci);
                if !idx.contains_key(&n) {
                    idx.insert(n, slot as u64);
                }
            }
            for (slot, (rec_pos, tbl)) in table_pairs.into_iter().enumerate() {
                let sn = tbl.struct_name.dup2();
                if !tbls.contains_key(&sn) {
                    tbls.insert(sn, (rec_pos, slot as u64));
                }
                env_tables.push(tbl);
            }
        });
        s.spawn(|_| {
            rebuild_tbl_cons(&mut apps, |r| EIdx::pack_wide(TIER_P, r));
        });
        s.spawn(|_| {
            rebuild_tbl_cons(&mut foralls, |r| EIdx::pack(ETAG_FORALL_E, TIER_P, r));
        });
        s.spawn(|_| {
            rebuild_tbl_cons(&mut lams, |r| EIdx::pack(ETAG_LAM, TIER_P, r));
        });
        s.spawn(|_| {
            rebuild_tbl_cons(&mut e_consts, |r| EIdx::pack(ETAG_CONST, TIER_P, r));
        });
        s.spawn(|_| {
            rebuild_tbl_cons(&mut strs, |r| NIdx::pack(NTAG_STR, TIER_P, r));
            rebuild_tbl_cons(&mut nums, |r| NIdx::pack(NTAG_NUM, TIER_P, r));
            rebuild_tbl_cons(&mut anons, |r| NIdx::pack(NTAG_ANONYMOUS, TIER_P, r));
            rebuild_tbl_cons(&mut lists, |r| LsIdx::pack(LSTAG_LIST, TIER_P, r));
        });
        s.spawn(|_| {
            rebuild_tbl_cons(&mut zeros, |r| LIdx::pack(LTAG_ZERO, TIER_P, r));
            rebuild_tbl_cons(&mut succs, |r| LIdx::pack(LTAG_SUCC, TIER_P, r));
            rebuild_tbl_cons(&mut maxs, |r| LIdx::pack(LTAG_MAX, TIER_P, r));
            rebuild_tbl_cons(&mut imaxs, |r| LIdx::pack(LTAG_IMAX, TIER_P, r));
            rebuild_tbl_cons(&mut params, |r| LIdx::pack(LTAG_PARAM, TIER_P, r));
            rebuild_tbl_cons(&mut bvars, |r| EIdx::pack(ETAG_BVAR, TIER_P, r));
            rebuild_tbl_cons(&mut fvars, |r| EIdx::pack(ETAG_FVAR, TIER_P, r));
            rebuild_tbl_cons(&mut sorts, |r| EIdx::pack(ETAG_SORT, TIER_P, r));
            rebuild_tbl_cons(&mut lets, |r| EIdx::pack(ETAG_LET_E, TIER_P, r));
            rebuild_tbl_cons(&mut lits, |r| EIdx::pack(ETAG_LIT, TIER_P, r));
            rebuild_tbl_cons(&mut projs, |r| EIdx::pack(ETAG_PROJ, TIER_P, r));
        });
    });

    let pers_tier = PersTier {
        frozen: true,
        n: NTables { anons, strs, nums },
        l: LTables {
            zeros,
            succs,
            maxs,
            imaxs,
            params,
        },
        ls: LsTables { lists },
        e: ETables {
            bvars,
            fvars,
            sorts,
            consts: e_consts,
            apps,
            lams,
            foralls,
            lets,
            lits,
            projs,
        },
        env: IStreamIndex {
            consts: env_consts,
            idx,
            tables: env_tables,
            tbls,
            firsts,
            next,
        },
    };
    let index_ns = t_idx.elapsed().as_nanos();

    Ok(LoadedEnvironment {
        pers: pers_tier,
        pins,
        ipins,
        decls,
        file_records,
        synthesized,
        hoisted,
        olean: None,
        load_ns,
        materialize_ns: 0,
        index_ns,
        thm_materialized_count,
        closure_fingerprint: Some(closure_hash),
        closure_roots,
        closure_manifest,
        module_hashes,
        preverified_prefix,
    })
}

/// Saves BOTH the pre-packed `GpuArenaPacket` and the columnar `HostEnvImage` (`PersTier`,
/// `Pins`, `ipins`, `decls`, `module_hashes`, plus sorted `.olean` stat+hash manifest) in `CGSNAP03`
/// format protected by a parallel-verifiable `64 MiB`-chunked 128-bit integrity checksum.
pub fn save_snapshot(
    path: &Path,
    env: &LoadedEnvironment,
    packet: &GpuArenaPacket,
    closure_hash: [u8; 16],
    start_decl: usize,
) -> Result<(), String> {
    for (idx, d) in env.decls.iter().enumerate() {
        if let IDeclaration::ThmDecl(_, v) = d {
            if v.tag() == ETAG_BVAR {
                return Err(format!(
                    "cannot save CGSNAP03 snapshot: declaration #{idx} retains an unmaterialized lazy theorem value"
                ));
            }
        }
    }

    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)
                .map_err(|e| format!("failed creating snapshot dir {}: {e}", parent.display()))?;
        }
    }

    let manifest_bytes = encode_manifest_section(&env.closure_roots, &env.closure_manifest)?;
    let header_size = std::mem::size_of::<ArenaHeader>();
    let job_size = std::mem::size_of::<GpuJob>();
    let header_bytes = bytemuck::bytes_of(&packet.header);
    let e_nodes_bytes: &[u8] = bytemuck::cast_slice(&packet.e_nodes);
    let meta_nodes_bytes: &[u8] = bytemuck::cast_slice(&packet.meta_nodes);
    let env_tables_bytes: &[u8] = bytemuck::cast_slice(&packet.env_tables);
    let jobs_bytes: &[u8] = bytemuck::cast_slice(&packet.jobs);

    let manifest_off = SNAPSHOT_FIXED_HEADER_BYTES as u64;
    let manifest_len = manifest_bytes.len() as u64;
    let gpu_off = manifest_off + manifest_len;
    let gpu_len = (32
        + header_bytes.len()
        + e_nodes_bytes.len()
        + meta_nodes_bytes.len()
        + env_tables_bytes.len()
        + jobs_bytes.len()) as u64;
    let host_off = gpu_off + gpu_len;

    let mut fixed = [0u8; SNAPSHOT_FIXED_HEADER_BYTES];
    fixed[0..8].copy_from_slice(&SNAPSHOT_MAGIC);
    fixed[8..24].copy_from_slice(&closure_hash);
    fixed[24..28].copy_from_slice(&(header_size as u32).to_le_bytes());
    fixed[28..32].copy_from_slice(&(job_size as u32).to_le_bytes());
    fixed[32..40].copy_from_slice(&(env.file_records as u64).to_le_bytes());
    fixed[40..48].copy_from_slice(&(start_decl as u64).to_le_bytes());
    fixed[48..56].copy_from_slice(&(env.preverified_prefix as u64).to_le_bytes());
    fixed[56..64].copy_from_slice(&env.synthesized.to_le_bytes());
    fixed[64..72].copy_from_slice(&(env.hoisted as u64).to_le_bytes());
    fixed[72..80].copy_from_slice(&(env.thm_materialized_count as u64).to_le_bytes());
    fixed[80..88].copy_from_slice(&(packet.eligible_jobs_count as u64).to_le_bytes());
    fixed[88..96].copy_from_slice(&manifest_off.to_le_bytes());
    fixed[96..104].copy_from_slice(&manifest_len.to_le_bytes());
    fixed[104..112].copy_from_slice(&gpu_off.to_le_bytes());
    fixed[112..120].copy_from_slice(&gpu_len.to_le_bytes());
    fixed[120..128].copy_from_slice(&host_off.to_le_bytes());

    let f = File::create(path)
        .map_err(|e| format!("failed creating snapshot {}: {e}", path.display()))?;
    let mut sw = ChunkedSnapWriter::new(f);

    // Fixed header + ManifestSection
    sw.write_bytes(&fixed)?;
    sw.write_bytes(&manifest_bytes)?;

    // GpuSection
    sw.write_u64(packet.e_nodes.len() as u64)?;
    sw.write_u64(packet.meta_nodes.len() as u64)?;
    sw.write_u64(packet.env_tables.len() as u64)?;
    sw.write_u64(packet.jobs.len() as u64)?;
    sw.write_bytes(header_bytes)?;
    sw.write_bytes(e_nodes_bytes)?;
    sw.write_bytes(meta_nodes_bytes)?;
    sw.write_bytes(env_tables_bytes)?;
    sw.write_bytes(jobs_bytes)?;

    // Columnar HostSection
    write_host_section(&mut sw, env)?;
    sw.finish(path)
}

struct VerifiedRawHeader {
    closure_hash: [u8; 16],
    file_records: usize,
    start_decl: usize,
    preverified_prefix: usize,
    synthesized: u64,
    hoisted: usize,
    thm_materialized_count: usize,
    eligible_jobs_count: usize,
    gpu_off: usize,
    gpu_len: usize,
    host_off: usize,
    payload_len: usize,
}

fn read_and_verify_raw_snapshot(
    path: &Path,
    expected_closure_hash: Option<[u8; 16]>,
    closure_target: Option<ClosureTarget<'_>>,
    verify_olean_hashes: bool,
) -> Result<(Vec<u8>, VerifiedRawHeader, Vec<String>, Vec<SnapshotManifestEntry>), String> {
    let raw = fs::read(path)
        .map_err(|e| format!("failed reading snapshot {}: {e}", path.display()))?;
    if raw.len() < SNAPSHOT_FIXED_HEADER_BYTES + SNAPSHOT_CHECKSUM_BYTES {
        return Err(format!(
            "snapshot {} truncated ({} bytes)",
            path.display(),
            raw.len()
        ));
    }

    let payload_len = raw.len() - SNAPSHOT_CHECKSUM_BYTES;
    let payload = &raw[..payload_len];
    let expected_sum = &raw[payload_len..];

    if payload[0..8] != SNAPSHOT_MAGIC {
        return Err(format!(
            "snapshot {} invalid magic (expected CGSNAP03)",
            path.display()
        ));
    }

    // Verify full 128-bit parallel chunked checksum BEFORE trusting any offset, manifest, or table.
    let actual_sum = compute_chunked_checksum128(payload);
    if actual_sum != expected_sum {
        return Err(format!(
            "snapshot {} integrity checksum mismatch (expected {:02x?}, computed {:02x?})",
            path.display(),
            expected_sum,
            actual_sum
        ));
    }

    let mut closure_hash = [0u8; 16];
    closure_hash.copy_from_slice(&payload[8..24]);
    if let Some(expected) = expected_closure_hash {
        if closure_hash != expected {
            return Err(format!(
                "snapshot {} closure hash mismatch against current .olean closure",
                path.display()
            ));
        }
    }

    let header_size = read_u32_le(payload, 24) as usize;
    let job_size = read_u32_le(payload, 28) as usize;
    if header_size != std::mem::size_of::<ArenaHeader>() {
        return Err(format!(
            "snapshot {} ArenaHeader ABI size mismatch ({} != {})",
            path.display(),
            header_size,
            std::mem::size_of::<ArenaHeader>()
        ));
    }
    if job_size != std::mem::size_of::<GpuJob>() {
        return Err(format!(
            "snapshot {} GpuJob ABI size mismatch ({} != {})",
            path.display(),
            job_size,
            std::mem::size_of::<GpuJob>()
        ));
    }

    let file_records =
        usize::try_from(read_u64_le(payload, 32)).map_err(|_| "file_records overflow".to_string())?;
    let start_decl =
        usize::try_from(read_u64_le(payload, 40)).map_err(|_| "start_decl overflow".to_string())?;
    let preverified_prefix = usize::try_from(read_u64_le(payload, 48))
        .map_err(|_| "preverified_prefix overflow".to_string())?;
    let synthesized = read_u64_le(payload, 56);
    let hoisted =
        usize::try_from(read_u64_le(payload, 64)).map_err(|_| "hoisted overflow".to_string())?;
    let thm_materialized_count = usize::try_from(read_u64_le(payload, 72))
        .map_err(|_| "thm_materialized_count overflow".to_string())?;
    let eligible_jobs_count = usize::try_from(read_u64_le(payload, 80))
        .map_err(|_| "eligible_jobs_count overflow".to_string())?;

    let manifest_off =
        usize::try_from(read_u64_le(payload, 88)).map_err(|_| "manifest_off overflow".to_string())?;
    let manifest_len =
        usize::try_from(read_u64_le(payload, 96)).map_err(|_| "manifest_len overflow".to_string())?;
    let gpu_off =
        usize::try_from(read_u64_le(payload, 104)).map_err(|_| "gpu_off overflow".to_string())?;
    let gpu_len =
        usize::try_from(read_u64_le(payload, 112)).map_err(|_| "gpu_len overflow".to_string())?;
    let host_off =
        usize::try_from(read_u64_le(payload, 120)).map_err(|_| "host_off overflow".to_string())?;

    if manifest_off != SNAPSHOT_FIXED_HEADER_BYTES
        || manifest_off.checked_add(manifest_len) != Some(gpu_off)
        || gpu_off.checked_add(gpu_len) != Some(host_off)
        || host_off > payload_len
    {
        return Err(format!("snapshot {} invalid section layout offsets", path.display()));
    }

    let (closure_roots, closure_manifest) =
        decode_manifest_section(&payload[manifest_off..gpu_off])?;
    if let Some(target) = closure_target {
        validate_closure_manifest(&closure_roots, &closure_manifest, target, verify_olean_hashes)?;
    }

    let hdr = VerifiedRawHeader {
        closure_hash,
        file_records,
        start_decl,
        preverified_prefix,
        synthesized,
        hoisted,
        thm_materialized_count,
        eligible_jobs_count,
        gpu_off,
        gpu_len,
        host_off,
        payload_len,
    };
    Ok((raw, hdr, closure_roots, closure_manifest))
}

/// Validates integrity checksum and `.olean` stat+hash manifest, decodes `GpuArenaPacket`, and
/// defers `HostSection` columnar decode + `ConsMap` rebuild so GPU execution can start immediately.
pub fn load_snapshot_gpu_first(
    path: &Path,
    expected_closure_hash: Option<[u8; 16]>,
    closure_target: Option<ClosureTarget<'_>>,
    verify_olean_hashes: bool,
) -> Result<GpuFirstSnapshot, String> {
    let t0 = Instant::now();
    let (raw, hdr, closure_roots, closure_manifest) = read_and_verify_raw_snapshot(
        path,
        expected_closure_hash,
        closure_target,
        verify_olean_hashes,
    )?;

    let packet = decode_gpu_section(
        &raw[hdr.gpu_off..hdr.host_off],
        hdr.eligible_jobs_count,
    )?;
    let host_bytes = raw[hdr.host_off..hdr.payload_len].to_vec();
    drop(raw);

    Ok(GpuFirstSnapshot {
        packet,
        closure_hash: hdr.closure_hash,
        closure_roots,
        closure_manifest,
        file_records: hdr.file_records,
        start_decl: hdr.start_decl,
        preverified_prefix: hdr.preverified_prefix,
        synthesized: hdr.synthesized,
        hoisted: hdr.hoisted,
        thm_materialized_count: hdr.thm_materialized_count,
        load_gpu_first_ns: t0.elapsed().as_nanos(),
        host_bytes,
    })
}

/// Validates checksum + `.olean` manifest and decodes ONLY `HostSection` for `--backend cpu --snapshot`,
/// skipping `GpuSection` allocations completely.
pub fn load_snapshot_for_cpu(
    path: &Path,
    expected_closure_hash: Option<[u8; 16]>,
    closure_target: Option<ClosureTarget<'_>>,
    verify_olean_hashes: bool,
) -> Result<CpuLoadedSnapshot, String> {
    let t0 = Instant::now();
    let (raw, hdr, closure_roots, closure_manifest) = read_and_verify_raw_snapshot(
        path,
        expected_closure_hash,
        closure_target,
        verify_olean_hashes,
    )?;

    // Read only jobs_len from first 32 bytes of GpuSection for exact decl count telemetry.
    let total_jobs = if hdr.gpu_len >= 32 {
        usize::try_from(read_u64_le(&raw, hdr.gpu_off + 24)).unwrap_or(0)
    } else {
        0
    };
    let host_slice = &raw[hdr.host_off..hdr.payload_len];
    let mut env = decode_host_section_and_env(
        host_slice,
        hdr.closure_hash,
        closure_roots,
        closure_manifest,
        hdr.file_records,
        hdr.preverified_prefix,
        hdr.synthesized,
        hdr.hoisted,
        hdr.thm_materialized_count,
        0,
    )?;
    drop(raw);
    let load_ns = t0.elapsed().as_nanos();
    env.load_ns = load_ns;

    Ok(CpuLoadedSnapshot {
        env,
        closure_hash: hdr.closure_hash,
        file_records: hdr.file_records,
        start_decl: hdr.start_decl,
        eligible_jobs_count: hdr.eligible_jobs_count,
        total_jobs,
        load_ns,
    })
}

/// Loads, validates, and restores BOTH `GpuArenaPacket` and `LoadedEnvironment` from a `CGSNAP03`
/// snapshot without `.olean` re-parsing.
pub fn load_snapshot(
    path: &Path,
    expected_closure_hash: Option<[u8; 16]>,
) -> Result<LoadedSnapshot, String> {
    let t0 = Instant::now();
    let gpu_snap = load_snapshot_gpu_first(path, expected_closure_hash, None, false)?;
    let closure_hash = gpu_snap.closure_hash;
    let file_records = gpu_snap.file_records;
    let start_decl = gpu_snap.start_decl;
    let packet = gpu_snap.packet;
    let host_snap = GpuFirstSnapshot {
        packet: GpuArenaPacket {
            header: packet.header,
            e_nodes: Vec::new(),
            meta_nodes: Vec::new(),
            env_tables: Vec::new(),
            jobs: Vec::new(),
            eligible_jobs_count: packet.eligible_jobs_count,
            pack_ns: packet.pack_ns,
        },
        closure_hash,
        closure_roots: gpu_snap.closure_roots,
        closure_manifest: gpu_snap.closure_manifest,
        file_records,
        start_decl,
        preverified_prefix: gpu_snap.preverified_prefix,
        synthesized: gpu_snap.synthesized,
        hoisted: gpu_snap.hoisted,
        thm_materialized_count: gpu_snap.thm_materialized_count,
        load_gpu_first_ns: 0,
        host_bytes: gpu_snap.host_bytes,
    };
    let mut env = host_snap.into_host_env()?;
    let load_ns = t0.elapsed().as_nanos();
    env.load_ns = load_ns;

    Ok(LoadedSnapshot {
        env,
        packet,
        closure_hash,
        file_records,
        start_decl,
        load_ns,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fs::hash128_bytes;
    use crate::loader::InputSpec;
    use crate::soa_pack::{pack_arena_from, ArenaLimitsConfig};
    use crate::verify_host::verify_host_parallel;
    use con_ron_core::kernel::env::CheckMode;

    fn sample_packet() -> GpuArenaPacket {
        GpuArenaPacket {
            header: ArenaHeader {
                verified_mode: 1,
                num_jobs: 2,
                max_steps: 131_072,
                ..Default::default()
            },
            e_nodes: vec![1, 2, 3, 4, 5, 6],
            meta_nodes: vec![10, 20, 30],
            env_tables: vec![100, 200, 300, 400],
            jobs: vec![
                GpuJob {
                    orig_decl_idx: 7,
                    decl_kind: 2,
                    record_pos: 7,
                    base_below: 5,
                    name: 11,
                    ty: 22,
                    val: 33,
                    lparams_off: 0,
                    lparams_len: 1,
                    ast_size: 9,
                    ast_bucket: 3,
                    flags: 1,
                },
                GpuJob {
                    orig_decl_idx: 8,
                    decl_kind: 1,
                    record_pos: 8,
                    base_below: 6,
                    name: 12,
                    ty: 23,
                    val: 34,
                    lparams_off: 1,
                    lparams_len: 0,
                    ast_size: 4,
                    ast_bucket: 2,
                    flags: 0,
                },
            ],
            eligible_jobs_count: 1,
            pack_ns: 0,
        }
    }

    #[test]
    fn snapshot_roundtrip_and_tamper_rejection() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let dir =
                    std::env::temp_dir().join(format!("con_gpu_snap_v3_test_{}", std::process::id()));
                let _ = fs::remove_dir_all(&dir);
                fs::create_dir_all(&dir).expect("mkdir");
                let snap = dir.join("init_prelude.cgsnap");

                let prelude_path = Path::new(
                    "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init/Prelude.olean",
                );
                let (env, pkt, hash, start_decl) = if prelude_path.exists() {
                    let sp = vec![std::path::PathBuf::from(
                        "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean",
                    )];
                    let spec = InputSpec::Oleans {
                        roots: vec!["Init.Prelude".to_string()],
                        search_paths: sp,
                        constants: None,
                        materialize_thms: true,
                    };
                    let loaded_env = crate::loader::load_environment(&spec).expect("Prelude loads");
                    let start = loaded_env.decls.len().saturating_sub(50);
                    let pkt = pack_arena_from(&loaded_env, ArenaLimitsConfig::default(), start);
                    let fp = loaded_env.closure_fingerprint.unwrap_or([7u8; 16]);
                    (loaded_env, pkt, fp, start)
                } else {
                    let dummy_env = LoadedEnvironment {
                        pers: PersTier {
                            frozen: true,
                            ..PersTier::empty()
                        },
                        pins: Pins::empty(),
                        ipins: Vec::new(),
                        decls: Vec::new(),
                        file_records: 42,
                        synthesized: 3,
                        hoisted: 1,
                        olean: None,
                        load_ns: 0,
                        materialize_ns: 0,
                        index_ns: 0,
                        thm_materialized_count: 0,
                        closure_fingerprint: Some([1u8; 16]),
                        closure_roots: Vec::new(),
                        closure_manifest: Vec::new(),
                        module_hashes: HashMap::new(),
                        preverified_prefix: 5,
                    };
                    let pkt = sample_packet();
                    (dummy_env, pkt, [1u8; 16], 7)
                };

                save_snapshot(&snap, &env, &pkt, hash, start_decl).expect("save_snapshot");

                let loaded = load_snapshot(&snap, Some(hash)).expect("load_snapshot");
                assert_eq!(loaded.closure_hash, hash);
                assert_eq!(loaded.file_records, env.file_records);
                assert_eq!(loaded.start_decl, start_decl);
                assert_eq!(loaded.env.decls.len(), env.decls.len());
                assert_eq!(loaded.env.pers.e.apps.rows.len(), env.pers.e.apps.rows.len());
                assert_eq!(loaded.env.pers.env.consts.len(), env.pers.env.consts.len());
                assert_eq!(loaded.env.preverified_prefix, env.preverified_prefix);
                assert_eq!(loaded.packet.eligible_jobs_count, pkt.eligible_jobs_count);
                assert_eq!(
                    bytemuck::bytes_of(&loaded.packet.header),
                    bytemuck::bytes_of(&pkt.header)
                );
                assert_eq!(loaded.packet.e_nodes, pkt.e_nodes);
                assert_eq!(loaded.packet.meta_nodes, pkt.meta_nodes);
                assert_eq!(loaded.packet.env_tables, pkt.env_tables);
                assert_eq!(
                    bytemuck::cast_slice::<GpuJob, u8>(&loaded.packet.jobs),
                    bytemuck::cast_slice::<GpuJob, u8>(&pkt.jobs)
                );

                // CPU-only loader skips GpuSection and restores verifying LoadedEnvironment.
                let cpu_snap =
                    load_snapshot_for_cpu(&snap, Some(hash), None, false).expect("cpu snapshot");
                assert_eq!(cpu_snap.env.decls.len(), env.decls.len());
                if !cpu_snap.env.decls.is_empty() {
                    assert!(matches!(cpu_snap.env.mode(), CheckMode::Verified));
                    let (v, _) = verify_host_parallel(&cpu_snap.env, Some(4));
                    assert!(
                        matches!(v, crate::loader::VerificationVerdict::Accepted { .. }),
                        "restored CGSNAP03 host verification failed: {v:?}"
                    );
                }

                // Closure hash mismatch is rejected cleanly.
                let mut bad_hash = hash;
                bad_hash[15] ^= 0xFF;
                let err_hash = load_snapshot(&snap, Some(bad_hash)).err().expect("hash mismatch");
                assert!(err_hash.contains("closure hash mismatch"), "{err_hash}");

                // Bad magic is rejected cleanly.
                let mut raw = fs::read(&snap).expect("read");
                raw[0] = b'X';
                fs::write(&snap, &raw).expect("write bad magic");
                let err_magic = load_snapshot(&snap, None).err().expect("magic mismatch");
                assert!(err_magic.contains("magic"), "{err_magic}");

                // Valid magic + payload byte flip fails checksum.
                raw[0] = b'C';
                raw[32] ^= 0x01;
                fs::write(&snap, &raw).expect("write corrupt");
                let err_sum = load_snapshot(&snap, None).err().expect("checksum mismatch");
                assert!(err_sum.contains("checksum"), "{err_sum}");

                let _ = fs::remove_dir_all(&dir);
            })
            .expect("spawn")
            .join()
            .expect("join");
    }

    #[test]
    fn cgsnap03_manifest_stat_touch_and_tamper_tests() {
        let dir =
            std::env::temp_dir().join(format!("con_gpu_manifest_test_{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        fs::create_dir_all(&dir).expect("mkdir");
        let olean_p = dir.join("Foo.olean");
        let bytes = b"dummy olean payload v1\0\0\0\0";
        fs::write(&olean_p, bytes).expect("write olean");

        let meta = fs::metadata(&olean_p).expect("stat");
        let (mtime_secs, mtime_nanos) = crate::fs::system_time_parts(meta.modified().ok());
        let h = hash128_bytes(bytes);

        let entry = SnapshotManifestEntry {
            norm_key: "Foo.olean".to_string(),
            path: olean_p.to_string_lossy().into_owned(),
            byte_len: meta.len(),
            mtime_secs,
            mtime_nanos,
            content_hash128: h,
        };
        let sp = vec![dir.clone()];
        let roots = vec!["Foo".to_string()];

        let dummy_env = LoadedEnvironment {
            pers: PersTier {
                frozen: true,
                ..PersTier::empty()
            },
            pins: Pins::empty(),
            ipins: Vec::new(),
            decls: Vec::new(),
            file_records: 1,
            synthesized: 0,
            hoisted: 0,
            olean: None,
            load_ns: 0,
            materialize_ns: 0,
            index_ns: 0,
            thm_materialized_count: 0,
            closure_fingerprint: Some(h),
            closure_roots: roots.clone(),
            closure_manifest: vec![entry],
            module_hashes: HashMap::new(),
            preverified_prefix: 0,
        };
        let snap = dir.join("foo.cgsnap");
        let pkt = sample_packet();
        save_snapshot(&snap, &dummy_env, &pkt, h, 0).expect("save");

        let tgt = ClosureTarget::Oleans {
            roots: &roots,
            search_paths: &sp,
        };

        // 1. Stat fast path succeeds
        load_snapshot_gpu_first(&snap, None, Some(tgt), false).expect("stat fast path ok");

        // 2. Touch mtime with identical bytes -> re-hash accepts
        std::thread::sleep(std::time::Duration::from_millis(25));
        let f = File::options().write(true).open(&olean_p).expect("open");
        let _ = f.set_modified(std::time::SystemTime::now());
        drop(f);
        load_snapshot_gpu_first(&snap, None, Some(tgt), false).expect("touch same bytes rehash ok");

        // 3. Same size & updated mtime but different byte -> rejected cleanly!
        let tampered = b"dummy olean payload v2\0\0\0\0";
        assert_eq!(tampered.len(), bytes.len());
        fs::write(&olean_p, tampered).expect("tamper write");
        let err_tamper = load_snapshot_gpu_first(&snap, None, Some(tgt), false)
            .err()
            .expect("must reject tampered olean on mtime change");
        assert!(err_tamper.contains("hash mismatch"), "{err_tamper}");

        // 4. --verify-olean-hashes rejects even if mtime were unchanged (test directly with match)
        // Reset back to original bytes + current mtime matches stored? No, mtime differs so both reject,
        // so update manifest entry mtime mismatch or tamper keeping mtime:
        let f2 = File::options().write(true).open(&olean_p).expect("open2");
        let orig_time = std::time::UNIX_EPOCH
            + std::time::Duration::new(mtime_secs, mtime_nanos);
        let _ = f2.set_modified(orig_time);
        drop(f2);
        // Fast path (`verify_olean_hashes=false`) would see matching size+mtime, whereas true hashes!
        load_snapshot_gpu_first(&snap, None, Some(tgt), false)
            .expect("fast stat trusts matching mtime+size");
        let err_strict = load_snapshot_gpu_first(&snap, None, Some(tgt), true)
            .err()
            .expect("--verify-olean-hashes must catch same-mtime same-size byte tamper");
        assert!(err_strict.contains("hash mismatch"), "{err_strict}");

        let _ = fs::remove_dir_all(&dir);
    }
}
