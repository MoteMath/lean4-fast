use std::fs::{File, Metadata};
use std::io::Read;
use std::path::{Path, PathBuf};

#[cfg(unix)]
use std::os::unix::fs::FileExt;
#[cfg(windows)]
use std::os::windows::fs::FileExt;

use con_ron_core::frontend::olean::files::OleanFs;

/// Standard filesystem implementation of `con_ron_core::frontend::olean::files::OleanFs`.
/// Unlike `con-ron`'s CLI parser on Windows, search path splitting handles Windows
/// drive letters (`C:/...`, `C:\...`) and `.olean` file paths cleanly.
pub struct StdFs;

/// Normalize `/mnt/<drive>/...` WSL2 paths to `<DRIVE>:/...`.
/// Leaves non-WSL paths, multi-char `/mnt/<name>` directories, and module names untouched.
pub fn normalize_wsl_mnt_path(raw: &str) -> String {
    let bytes = raw.as_bytes();
    if bytes.len() >= 6
        && (bytes[0] == b'/' || bytes[0] == b'\\')
        && &bytes[1..4] == b"mnt"
        && (bytes[4] == b'/' || bytes[4] == b'\\')
        && bytes[5].is_ascii_alphabetic()
    {
        if bytes.len() == 6 {
            let drive = (bytes[5] as char).to_ascii_uppercase();
            return format!("{drive}:/");
        }
        if bytes[6] == b'/' || bytes[6] == b'\\' {
            let drive = (bytes[5] as char).to_ascii_uppercase();
            let rest = &raw[7..];
            return format!("{drive}:/{rest}");
        }
    }
    raw.to_string()
}

pub fn normalize_lean_path_str(raw: &str) -> String {
    if cfg!(windows) {
        normalize_wsl_mnt_path(raw)
    } else {
        raw.to_string()
    }
}

pub fn normalize_lean_path(p: &Path) -> PathBuf {
    let s = p.to_string_lossy();
    let norm = normalize_lean_path_str(&s);
    if norm.as_str() == s.as_ref() {
        p.to_path_buf()
    } else {
        PathBuf::from(norm)
    }
}

fn of_code_points(cps: &[u32]) -> PathBuf {
    let s: String = cps.iter().filter_map(|&c| char::from_u32(c)).collect();
    PathBuf::from(normalize_lean_path_str(&s))
}

#[allow(dead_code)]
fn to_code_points(p: &Path) -> Vec<u32> {
    p.to_string_lossy().chars().map(|c| c as u32).collect()
}

fn err_cp(e: impl ToString) -> Vec<u32> {
    e.to_string().chars().map(|c| c as u32).collect()
}

fn olean_file_kind(pb: &Path) -> Option<bool> {
    let name = pb.file_name()?.to_str()?;
    if name.ends_with(".olean") {
        Some(true)
    } else if name.ends_with(".olean.server") || name.ends_with(".olean.private") {
        Some(false)
    } else {
        None
    }
}

fn validate_olean_header_prefix(pb: &Path, buf: &[u8], file_size: u64) -> Result<(), Vec<u32>> {
    let Some(is_primary_olean) = olean_file_kind(pb) else {
        return Ok(());
    };
    if buf.len() < 96 || file_size < 96 || (file_size & 7) != 0 {
        return Err(err_cp(format!("{}: invalid or truncated .olean header", pb.display())));
    }
    if &buf[0..5] != b"olean" || buf[5] != 2 || (buf[6] & 1) == 0 {
        return Err(err_cp(format!("{}: incompatible .olean magic/version/flags", pb.display())));
    }
    if !buf[7..40].iter().all(|&b| b == 0 || (0x20..=0x7E).contains(&b)) {
        return Err(err_cp(format!("{}: corrupt .olean version string", pb.display())));
    }
    if !buf[40..80].iter().all(|&b| b == 0 || b.is_ascii_hexdigit()) {
        return Err(err_cp(format!("{}: corrupt .olean git hash header", pb.display())));
    }
    let base = u64::from_le_bytes([
        buf[80], buf[81], buf[82], buf[83], buf[84], buf[85], buf[86], buf[87],
    ]);
    let rptr = u64::from_le_bytes([
        buf[88], buf[89], buf[90], buf[91], buf[92], buf[93], buf[94], buf[95],
    ]);
    if (base & 7) != 0 || base > u64::MAX - file_size {
        return Err(err_cp(format!("{}: invalid .olean base pointer", pb.display())));
    }
    if is_primary_olean && ((rptr & 7) != 0 || rptr < base + 96 || rptr >= base + file_size) {
        return Err(err_cp(format!("{}: invalid .olean root pointer", pb.display())));
    }
    Ok(())
}

impl OleanFs for StdFs {
    fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
        let pb = of_code_points(p);
        Ok(pb.exists())
    }

    fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>> {
        let pb = of_code_points(p);
        match std::fs::canonicalize(&pb) {
            Ok(canon) => {
                // On Windows, strip \\?\ UNC prefix if possible while preserving canonical path.
                let s = canon.to_string_lossy();
                let clean = s.strip_prefix(r"\\?\").unwrap_or(&s);
                Ok(clean.chars().map(|c| c as u32).collect())
            }
            Err(e) => Err(err_cp(e)),
        }
    }

    fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>> {
        let pb = of_code_points(p);
        let mut f = File::open(&pb).map_err(err_cp)?;
        let md = f.metadata().map_err(err_cp)?;
        let len = usize::try_from(md.len()).map_err(|_| err_cp("file exceeds usize"))?;
        let mut bytes = vec![0u8; len];
        f.read_exact(&mut bytes).map_err(err_cp)?;
        validate_olean_header_prefix(&pb, &bytes, len as u64)?;
        Ok(bytes)
    }

    fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
        let pb = of_code_points(p);
        let file = File::open(&pb).map_err(err_cp)?;
        let cap = len as usize;
        let mut buf = vec![0u8; cap];
        let mut filled = 0usize;
        while filled < cap {
            #[cfg(windows)]
            let n = file
                .seek_read(&mut buf[filled..], off + filled as u64)
                .map_err(err_cp)?;
            #[cfg(unix)]
            let n = file
                .read_at(&mut buf[filled..], off + filled as u64)
                .map_err(err_cp)?;
            #[cfg(not(any(windows, unix)))]
            let n = {
                use std::io::{Seek, SeekFrom};
                let mut f = &file;
                f.seek(SeekFrom::Start(off + filled as u64)).map_err(err_cp)?;
                f.read(&mut buf[filled..]).map_err(err_cp)?
            };
            if n == 0 {
                break;
            }
            filled += n;
        }
        buf.truncate(filled);
        if off == 0 && len >= 96 {
            let file_size = file.metadata().map(|m| m.len()).map_err(err_cp)?;
            validate_olean_header_prefix(&pb, &buf, file_size)?;
        }
        Ok(buf)
    }

    fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>> {
        let pb = of_code_points(p);
        let meta: Metadata = std::fs::metadata(&pb).map_err(err_cp)?;
        Ok(meta.len())
    }

    fn read_notes_say(&self, _line: &Vec<u32>) {}

    fn read_notes_module_loaded(&self, _m: u64, _sz: u64) {}
}

/// Split a search path string (supporting `;`, POSIX `:`, mixed drive letters `C:/...`, and `/mnt/<drive>/...`).
pub fn split_search_path(spec: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    for segment in spec.split(';') {
        if segment.is_empty() {
            continue;
        }
        if !segment.contains(':') || is_single_windows_drive_path(segment) {
            out.push(PathBuf::from(normalize_lean_path_str(segment)));
            continue;
        }
        let bytes = segment.as_bytes();
        let mut start = 0usize;
        let mut i = 0usize;
        while i < bytes.len() {
            if bytes[i] == b':' {
                let is_drive = i == start + 1
                    && bytes[start].is_ascii_alphabetic()
                    && (i + 1 >= bytes.len() || bytes[i + 1] == b'/' || bytes[i + 1] == b'\\');
                if !is_drive {
                    let s = &segment[start..i];
                    if !s.is_empty() {
                        out.push(PathBuf::from(normalize_lean_path_str(s)));
                    }
                    start = i + 1;
                }
            }
            i += 1;
        }
        let tail = &segment[start..];
        if !tail.is_empty() {
            out.push(PathBuf::from(normalize_lean_path_str(tail)));
        }
    }
    out
}

fn is_single_windows_drive_path(s: &str) -> bool {
    let b = s.as_bytes();
    if b.len() >= 2 && b[0].is_ascii_alphabetic() && b[1] == b':' {
        // Check if there are any other colons after index 1.
        !s[2..].contains(':')
    } else {
        false
    }
}

fn canonical_clean(p: &Path) -> PathBuf {
    let canon = std::fs::canonicalize(p).unwrap_or_else(|_| p.to_path_buf());
    let s = canon.to_string_lossy();
    PathBuf::from(s.strip_prefix(r"\\?\").unwrap_or(&s))
}

fn push_unique_dir(dirs: &mut Vec<PathBuf>, p: PathBuf) {
    let clean = canonical_clean(&p);
    let key = clean.to_string_lossy().replace('\\', "/").to_ascii_lowercase();
    let already = dirs
        .iter()
        .any(|d| canonical_clean(d).to_string_lossy().replace('\\', "/").to_ascii_lowercase() == key);
    if !already {
        dirs.push(clean);
    }
}

/// Discover default Lean toolchain search paths from LEAN_PATH or a single active elan toolchain.
/// Note: `con-ron-core` requires each module (e.g. `Init`) to exist on at most ONE directory in the search path.
pub fn discover_default_search_paths() -> Vec<PathBuf> {
    let mut dirs = Vec::new();
    if let Ok(lp) = std::env::var("LEAN_PATH") {
        for d in split_search_path(&lp) {
            if d.is_dir() {
                push_unique_dir(&mut dirs, d);
            }
        }
    }
    if dirs.iter().any(|d| d.join("Init.olean").exists()) {
        return dirs;
    }

    // Check explicit v4.35.0 toolchain first, then fallback to at most one installed elan toolchain.
    let preferred = PathBuf::from(
        r"C:\Users\devin\.elan\toolchains\leanprover--lean4---v4.35.0\lib\lean",
    );
    if preferred.is_dir() {
        push_unique_dir(&mut dirs, preferred);
        return dirs;
    }

    if let Ok(home) = std::env::var("USERPROFILE").or_else(|_| std::env::var("HOME")) {
        let toolchains = PathBuf::from(home).join(".elan").join("toolchains");
        if let Ok(entries) = std::fs::read_dir(toolchains) {
            let mut candidates: Vec<PathBuf> = entries
                .flatten()
                .map(|e| e.path().join("lib").join("lean"))
                .filter(|lib| lib.is_dir() && lib.join("Init.olean").exists())
                .collect();
            candidates.sort();
            if let Some(last) = candidates.pop() {
                push_unique_dir(&mut dirs, last);
            }
        }
    }
    dirs
}

/// Resolve an `.olean` file path into `(search_dir, module_name)`.
/// For example `C:/.../lib/lean/Init.olean` -> `(Some("C:/.../lib/lean"), "Init")`,
/// and `C:/.../lib/lean/Init/Core.olean` -> tries finding root lib ancestor where `Init/Core.olean` lives.
pub fn resolve_olean_file(path: &Path) -> (Option<PathBuf>, String) {
    let norm = normalize_lean_path(path);
    let canon = std::fs::canonicalize(&norm).unwrap_or(norm);
    let s = canon.to_string_lossy();
    let clean_path = PathBuf::from(s.strip_prefix(r"\\?\").unwrap_or(&s));
    let mut components: Vec<String> = Vec::new();
    let cur = clean_path.as_path();
    let stem = cur
        .file_stem()
        .map(|x| x.to_string_lossy().to_string())
        .unwrap_or_else(|| "Main".to_string());
    components.push(stem);
    let parent_dir = cur.parent().map(Path::to_path_buf);

    // If inside ".../lib/lean/Foo/Bar.olean", reconstruct dotted module "Foo.Bar" rooted at ".../lib/lean".
    if let Some(p) = &parent_dir {
        let p_str = p.to_string_lossy().replace('\\', "/");
        if let Some(idx) = p_str.rfind("/lib/lean/") {
            let root = PathBuf::from(&p_str[..idx + "/lib/lean".len()]);
            let rel = &p_str[idx + "/lib/lean/".len()..];
            let mut mods: Vec<String> = rel
                .split('/')
                .filter(|x| !x.is_empty())
                .map(ToString::to_string)
                .collect();
            mods.push(components[0].clone());
            return (Some(root), mods.join("."));
        }
        // Check if parent has Init.olean or Lake packages structure (.lake/build/lib/lean).
        if let Some(idx) = p_str.rfind("/lib/lean") {
            if idx + "/lib/lean".len() == p_str.len() {
                return (Some(p.clone()), components[0].clone());
            }
        }
    }
    (parent_dir, components.join("."))
}

pub fn str_to_cp(s: &str) -> Vec<u32> {
    s.chars().map(|c| c as u32).collect()
}

pub fn cp_to_str(cps: &[u32]) -> String {
    cps.iter().filter_map(|&c| char::from_u32(c)).collect()
}

mod cache_support {
    use super::{
        cp_to_str, normalize_lean_path, normalize_lean_path_str, str_to_cp,
        validate_olean_header_prefix, StdFs,
    };
    use con_ron_core::arena::handle::NIdx;
    use con_ron_core::arena::store::{EStore, NNodeView, PersTier};
    use con_ron_core::frontend::olean::files::{self, OleanFs};
    use con_ron_core::frontend::olean::{header, region, spec, view};
    use rayon::prelude::*;
    use std::collections::{HashMap, HashSet, VecDeque};
    use std::fs::File;
    use std::io::Read;
    use std::path::{Path, PathBuf};
    use std::sync::atomic::{AtomicUsize, Ordering};
    use std::sync::{Arc, Condvar, Mutex, RwLock};
    use std::time::{SystemTime, UNIX_EPOCH};

    const MAP_SHARDS: usize = 64;
    pub const CHUNK_CHECKSUM_BYTES: usize = 64 * 1024 * 1024;

    #[inline]
    fn shard_for_cp(p: &[u32]) -> usize {
        let mut h: u64 = 0xcbf29ce484222325;
        for &w in p {
            h = (h ^ (w as u64)).wrapping_mul(0x100000001b3);
        }
        ((h ^ (h >> 32)) as usize) & (MAP_SHARDS - 1)
    }

    struct ShardedMap<V> {
        shards: Vec<RwLock<HashMap<Vec<u32>, V>>>,
    }

    impl<V> ShardedMap<V> {
        fn new() -> Self {
            let mut shards = Vec::with_capacity(MAP_SHARDS);
            for _ in 0..MAP_SHARDS {
                shards.push(RwLock::new(HashMap::new()));
            }
            Self { shards }
        }

        fn clear(&self) {
            for s in &self.shards {
                s.write().expect("shard write").clear();
            }
        }

        fn get_cloned(&self, k: &Vec<u32>) -> Option<V>
        where
            V: Clone,
        {
            let idx = shard_for_cp(k);
            self.shards[idx].read().expect("shard read").get(k).cloned()
        }

        fn insert(&self, k: Vec<u32>, v: V) {
            let idx = shard_for_cp(&k);
            self.shards[idx].write().expect("shard write").insert(k, v);
        }

        fn remove(&self, k: &Vec<u32>) {
            let idx = shard_for_cp(k);
            self.shards[idx].write().expect("shard write").remove(k);
        }

        fn len(&self) -> usize {
            self.shards
                .iter()
                .map(|s| s.read().expect("shard read").len())
                .sum()
        }
    }

    #[inline]
    pub fn system_time_parts(t: Option<SystemTime>) -> (u64, u32) {
        match t.and_then(|st| st.duration_since(UNIX_EPOCH).ok()) {
            Some(d) => (d.as_secs(), d.subsec_nanos()),
            None => (0, 0),
        }
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    pub struct SnapshotManifestEntry {
        pub norm_key: String,
        pub path: String,
        pub byte_len: u64,
        pub mtime_secs: u64,
        pub mtime_nanos: u32,
        pub content_hash128: [u8; 16],
    }

    #[derive(Clone, Copy, Debug)]
    pub enum ClosureTarget<'a> {
        Oleans {
            roots: &'a [String],
            search_paths: &'a [PathBuf],
        },
        Ndjson {
            path: &'a Path,
        },
    }

    struct FileCacheEntry {
        bytes: Arc<Vec<u8>>,
        len: u64,
        modified: Option<SystemTime>,
        content_hash128: [u8; 16],
    }

    struct CachedFsInner {
        exists: ShardedMap<bool>,
        real: ShardedMap<Vec<u32>>,
        sizes: ShardedMap<u64>,
        files: ShardedMap<FileCacheEntry>,
        file_hits: AtomicUsize,
        file_misses: AtomicUsize,
        exists_hits: AtomicUsize,
        exists_misses: AtomicUsize,
    }

    #[derive(Clone, Debug, Default, PartialEq, Eq)]
    pub struct CachedFsStats {
        pub file_hits: usize,
        pub file_misses: usize,
        pub exists_hits: usize,
        pub exists_misses: usize,
        pub cached_files: usize,
    }

    /// Thread-safe sharded in-memory filesystem cache implementing `con-ron-core`'s `OleanFs`.
    #[derive(Clone)]
    pub struct CachedFs {
        inner: Arc<CachedFsInner>,
    }

    impl Default for CachedFs {
        fn default() -> Self {
            Self::new()
        }
    }

    impl CachedFs {
        pub fn new() -> Self {
            Self {
                inner: Arc::new(CachedFsInner {
                    exists: ShardedMap::new(),
                    real: ShardedMap::new(),
                    sizes: ShardedMap::new(),
                    files: ShardedMap::new(),
                    file_hits: AtomicUsize::new(0),
                    file_misses: AtomicUsize::new(0),
                    exists_hits: AtomicUsize::new(0),
                    exists_misses: AtomicUsize::new(0),
                }),
            }
        }

        pub fn clear(&self) {
            self.inner.exists.clear();
            self.inner.real.clear();
            self.inner.sizes.clear();
            self.inner.files.clear();
        }

        pub fn cached_file_count(&self) -> usize {
            self.inner.files.len()
        }

        pub fn stats(&self) -> CachedFsStats {
            CachedFsStats {
                file_hits: self.inner.file_hits.load(Ordering::Relaxed),
                file_misses: self.inner.file_misses.load(Ordering::Relaxed),
                exists_hits: self.inner.exists_hits.load(Ordering::Relaxed),
                exists_misses: self.inner.exists_misses.load(Ordering::Relaxed),
                cached_files: self.cached_file_count(),
            }
        }

        pub fn reset_stats(&self) {
            self.inner.file_hits.store(0, Ordering::Relaxed);
            self.inner.file_misses.store(0, Ordering::Relaxed);
            self.inner.exists_hits.store(0, Ordering::Relaxed);
            self.inner.exists_misses.store(0, Ordering::Relaxed);
        }

        /// Re-checks disk metadata for cached files and evicts any modified or deleted entries.
        /// Returns the number of evicted files.
        pub fn revalidate_on_disk(&self) -> usize {
            let mut snapshot: Vec<(Vec<u32>, u64, Option<SystemTime>)> = Vec::new();
            for s in &self.inner.files.shards {
                let g = s.read().expect("files shard read");
                for (k, v) in g.iter() {
                    snapshot.push((k.clone(), v.len, v.modified));
                }
            }
            if snapshot.is_empty() {
                return 0;
            }
            let stale: Vec<Vec<u32>> = snapshot
                .into_par_iter()
                .filter_map(|(k, len, mtime)| {
                    let pb = PathBuf::from(normalize_lean_path_str(&cp_to_str(&k)));
                    match std::fs::metadata(&pb) {
                        Ok(md) if md.is_file() => {
                            let cur_len = md.len();
                            let cur_mtime = md.modified().ok();
                            if cur_len == len && cur_mtime == mtime {
                                None
                            } else {
                                Some(k)
                            }
                        }
                        _ => Some(k),
                    }
                })
                .collect();
            if stale.is_empty() {
                return 0;
            }
            let count = stale.len();
            for k in &stale {
                self.inner.files.remove(k);
                self.inner.sizes.remove(k);
            }
            self.inner.exists.clear();
            self.inner.real.clear();
            count
        }

        pub fn read_bin_arc_with_meta(
            &self,
            p: &Vec<u32>,
        ) -> Result<(Arc<Vec<u8>>, u64, u64, u32, [u8; 16]), Vec<u32>> {
            let shard = shard_for_cp(p);
            if let Some((arc, len, modified, hash128)) = self.inner.files.shards[shard]
                .read()
                .expect("files read")
                .get(p)
                .map(|e| (Arc::clone(&e.bytes), e.len, e.modified, e.content_hash128))
            {
                self.inner.file_hits.fetch_add(1, Ordering::Relaxed);
                let (secs, nanos) = system_time_parts(modified);
                return Ok((arc, len, secs, nanos, hash128));
            }
            self.inner.file_misses.fetch_add(1, Ordering::Relaxed);
            let pb = PathBuf::from(normalize_lean_path_str(&cp_to_str(p)));
            let mut file = File::open(&pb).map_err(super::err_cp)?;
            let md = file.metadata().map_err(super::err_cp)?;
            let len = md.len();
            let modified = md.modified().ok();
            let cap = usize::try_from(len).map_err(|_| super::err_cp("file exceeds usize"))?;
            let mut bytes = vec![0u8; cap];
            file.read_exact(&mut bytes).map_err(super::err_cp)?;
            validate_olean_header_prefix(&pb, &bytes, len)?;
            let content_hash128 = hash128_bytes(&bytes);
            let (secs, nanos) = system_time_parts(modified);
            let arc = Arc::new(bytes);
            self.inner.files.shards[shard].write().expect("files write").insert(
                p.clone(),
                FileCacheEntry {
                    bytes: Arc::clone(&arc),
                    len,
                    modified,
                    content_hash128,
                },
            );
            self.inner.sizes.insert(p.clone(), len);
            Ok((arc, len, secs, nanos, content_hash128))
        }

        pub fn read_bin_arc(&self, p: &Vec<u32>) -> Result<Arc<Vec<u8>>, Vec<u32>> {
            self.read_bin_arc_with_meta(p).map(|(arc, _, _, _, _)| arc)
        }
    }

    impl OleanFs for CachedFs {
        fn path_exists(&self, p: &Vec<u32>) -> Result<bool, Vec<u32>> {
            if let Some(b) = self.inner.exists.get_cloned(p) {
                self.inner.exists_hits.fetch_add(1, Ordering::Relaxed);
                return Ok(b);
            }
            self.inner.exists_misses.fetch_add(1, Ordering::Relaxed);
            let b = StdFs.path_exists(p)?;
            self.inner.exists.insert(p.clone(), b);
            Ok(b)
        }

        fn real_path(&self, p: &Vec<u32>) -> Result<Vec<u32>, Vec<u32>> {
            if let Some(rp) = self.inner.real.get_cloned(p) {
                return Ok(rp);
            }
            let rp = StdFs.real_path(p)?;
            self.inner.real.insert(p.clone(), rp.clone());
            Ok(rp)
        }

        fn read_bin_file(&self, p: &Vec<u32>) -> Result<Vec<u8>, Vec<u32>> {
            self.read_bin_arc(p).map(|arc| (*arc).clone())
        }

        fn read_range(&self, p: &Vec<u32>, off: u64, len: u64) -> Result<Vec<u8>, Vec<u32>> {
            let shard = shard_for_cp(p);
            if let Some(arc) = self.inner.files.shards[shard]
                .read()
                .expect("files read")
                .get(p)
                .map(|e| Arc::clone(&e.bytes))
            {
                self.inner.file_hits.fetch_add(1, Ordering::Relaxed);
                let start = (off as usize).min(arc.len());
                let end = off.saturating_add(len).min(arc.len() as u64) as usize;
                return Ok(arc[start..end].to_vec());
            }
            StdFs.read_range(p, off, len)
        }

        fn file_size(&self, p: &Vec<u32>) -> Result<u64, Vec<u32>> {
            if let Some(sz) = self.inner.sizes.get_cloned(p) {
                return Ok(sz);
            }
            let shard = shard_for_cp(p);
            if let Some(len) = self.inner.files.shards[shard]
                .read()
                .expect("files read")
                .get(p)
                .map(|e| e.len)
            {
                return Ok(len);
            }
            let sz = StdFs.file_size(p)?;
            self.inner.sizes.insert(p.clone(), sz);
            Ok(sz)
        }

        fn read_notes_say(&self, _line: &Vec<u32>) {}

        fn read_notes_module_loaded(&self, _total: u64, _size: u64) {}
    }

    #[derive(Clone, Debug)]
    pub struct PrefetchedOleanFile {
        pub key: String,
        pub path_cp: Vec<u32>,
        pub path_str: String,
        pub bytes: Arc<Vec<u8>>,
        pub byte_len: u64,
        pub mtime_secs: u64,
        pub mtime_nanos: u32,
        pub content_hash128: [u8; 16],
    }

    impl PrefetchedOleanFile {
        pub fn from_bytes(key: String, path_cp: Vec<u32>, bytes: Arc<Vec<u8>>) -> Self {
            let path_str = normalize_lean_path_str(&cp_to_str(&path_cp));
            let byte_len = bytes.len() as u64;
            let content_hash128 = hash128_bytes(&bytes);
            Self {
                key,
                path_cp,
                path_str,
                bytes,
                byte_len,
                mtime_secs: 0,
                mtime_nanos: 0,
                content_hash128,
            }
        }

        pub fn to_manifest_entry(&self) -> SnapshotManifestEntry {
            SnapshotManifestEntry {
                norm_key: self.key.clone(),
                path: self.path_str.clone(),
                byte_len: self.byte_len,
                mtime_secs: self.mtime_secs,
                mtime_nanos: self.mtime_nanos,
                content_hash128: self.content_hash128,
            }
        }
    }

    #[derive(Clone, Debug)]
    pub struct PrefetchedClosure {
        pub files: Vec<PrefetchedOleanFile>,
        pub fingerprint: [u8; 16],
        pub modules_visited: usize,
    }

    #[inline]
    fn splitmix64(mut x: u64) -> u64 {
        x = x.wrapping_add(0x9e3779b97f4a7c15);
        x = (x ^ (x >> 30)).wrapping_mul(0xbf58476d1ce4e5b9);
        x = (x ^ (x >> 27)).wrapping_mul(0x94d049bb133111eb);
        x ^ (x >> 31)
    }

    #[inline]
    fn read_le64(data: &[u8], off: usize) -> u64 {
        u64::from_le_bytes([
            data[off],
            data[off + 1],
            data[off + 2],
            data[off + 3],
            data[off + 4],
            data[off + 5],
            data[off + 6],
            data[off + 7],
        ])
    }

    #[inline]
    fn hash128_feed_bytes(h1: &mut u64, h2: &mut u64, data: &[u8]) {
        const FNV_PRIME: u64 = 0x100000001b3;
        const P2: u64 = 0x9e3779b97f4a7c15;
        let mut s1 = *h1;
        let mut s2 = *h2;
        let mut s3 = *h1 ^ 0x517cc1b727220a95;
        let mut s4 = *h2 ^ 0x94d049bb133111eb;
        let mut i = 0usize;
        while i + 32 <= data.len() {
            let w0 = read_le64(data, i);
            let w1 = read_le64(data, i + 8);
            let w2 = read_le64(data, i + 16);
            let w3 = read_le64(data, i + 24);
            s1 = (s1 ^ w0).wrapping_mul(FNV_PRIME).rotate_left(13);
            s2 = (s2 ^ w1).wrapping_mul(P2).rotate_left(17);
            s3 = (s3 ^ w2).wrapping_mul(0xbf58476d1ce4e5b9).rotate_left(19);
            s4 = (s4 ^ w3).wrapping_mul(0x94d049bb133111eb).rotate_left(23);
            i += 32;
        }
        s1 ^= s3.rotate_left(7);
        s2 ^= s4.rotate_left(11);
        while i + 8 <= data.len() {
            let w = read_le64(data, i);
            s1 = (s1 ^ w).wrapping_mul(FNV_PRIME).rotate_left(13).wrapping_add(P2);
            s2 = splitmix64(s2 ^ w);
            i += 8;
        }
        if i < data.len() {
            let mut tail = [0u8; 8];
            let rem = data.len() - i;
            tail[..rem].copy_from_slice(&data[i..]);
            let w = u64::from_le_bytes(tail);
            s1 = (s1 ^ w ^ ((rem as u64) << 56)).wrapping_mul(FNV_PRIME);
            s2 = splitmix64(s2 ^ w ^ (rem as u64));
        }
        *h1 = s1;
        *h2 = s2;
    }

    pub fn hash128_bytes_with_seed(data: &[u8], seed1: u64, seed2: u64) -> [u8; 16] {
        let mut h1 = seed1;
        let mut h2 = seed2;
        hash128_feed_bytes(&mut h1, &mut h2, data);
        h1 = splitmix64(h1 ^ (data.len() as u64) ^ h2.rotate_left(17));
        h2 = splitmix64(h2 ^ (data.len() as u64) ^ h1.rotate_right(23));
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&h1.to_le_bytes());
        out[8..].copy_from_slice(&h2.to_le_bytes());
        out
    }

    pub fn hash128_bytes(data: &[u8]) -> [u8; 16] {
        hash128_bytes_with_seed(data, 0xcbf29ce484222325, 0x517cc1b727220a95)
    }

    pub fn combine_chunk_hashes128(chunk_hashes: &[[u8; 16]], total_bytes: u64) -> [u8; 16] {
        let mut h1: u64 = 0xcbf29ce484222325;
        let mut h2: u64 = 0x517cc1b727220a95;
        hash128_feed_bytes(&mut h1, &mut h2, &(chunk_hashes.len() as u64).to_le_bytes());
        hash128_feed_bytes(&mut h1, &mut h2, &total_bytes.to_le_bytes());
        for ch in chunk_hashes {
            hash128_feed_bytes(&mut h1, &mut h2, ch);
        }
        h1 = splitmix64(h1 ^ h2.rotate_left(17) ^ total_bytes);
        h2 = splitmix64(h2 ^ h1.rotate_right(23) ^ (chunk_hashes.len() as u64));
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&h1.to_le_bytes());
        out[8..].copy_from_slice(&h2.to_le_bytes());
        out
    }

    /// Parallel `rayon` `64 MiB`-chunked 128-bit integrity checksum over an arbitrary byte slice.
    pub fn compute_chunked_checksum128(payload: &[u8]) -> [u8; 16] {
        if payload.is_empty() {
            return combine_chunk_hashes128(&[], 0);
        }
        let chunk_hashes: Vec<[u8; 16]> = payload
            .par_chunks(CHUNK_CHECKSUM_BYTES)
            .enumerate()
            .map(|(chunk_idx, chunk)| {
                let s1 = 0xcbf29ce484222325u64
                    ^ (chunk_idx as u64).wrapping_mul(0x9e3779b97f4a7c15);
                let s2 = 0x517cc1b727220a95u64 ^ (chunk.len() as u64);
                hash128_bytes_with_seed(chunk, s1, s2)
            })
            .collect();
        combine_chunk_hashes128(&chunk_hashes, payload.len() as u64)
    }

    /// Computes a deterministic 128-bit pure-integer fingerprint over sorted `.olean` closure files
    /// by parallelizing per-file hashing when needed and folding sorted file digests.
    pub fn compute_closure_fingerprint(files: &[PrefetchedOleanFile]) -> [u8; 16] {
        let mut ordered: Vec<(usize, &PrefetchedOleanFile)> = files.iter().enumerate().collect();
        ordered.sort_by(|a, b| a.1.key.cmp(&b.1.key));
        let per_file_hashes: Vec<[u8; 16]> = ordered
            .par_iter()
            .map(|(_, f)| {
                let expected_zero = f.byte_len != (f.bytes.len() as u64) || f.content_hash128 == [0u8; 16];
                if !expected_zero || f.bytes.is_empty() {
                    if f.byte_len == f.bytes.len() as u64 {
                        return f.content_hash128;
                    }
                }
                hash128_bytes(&f.bytes)
            })
            .collect();
        let mut h1: u64 = 0xcbf29ce484222325;
        let mut h2: u64 = 0x517cc1b727220a95;
        let count_le = (ordered.len() as u64).to_le_bytes();
        hash128_feed_bytes(&mut h1, &mut h2, &count_le);
        for (pos, (_, f)) in ordered.iter().enumerate() {
            let key_bytes = f.key.as_bytes();
            let klen = (key_bytes.len() as u64).to_le_bytes();
            hash128_feed_bytes(&mut h1, &mut h2, &klen);
            hash128_feed_bytes(&mut h1, &mut h2, key_bytes);
            let blen = (f.bytes.len() as u64).to_le_bytes();
            hash128_feed_bytes(&mut h1, &mut h2, &blen);
            hash128_feed_bytes(&mut h1, &mut h2, &per_file_hashes[pos]);
            h1 = splitmix64(h1 ^ 0xA5A5_5A5A_F0F0_0F0F);
            h2 = splitmix64(h2 ^ h1.rotate_left(19));
        }
        h1 = splitmix64(h1 ^ h2.rotate_left(17));
        h2 = splitmix64(h2 ^ h1.rotate_right(23));
        let mut out = [0u8; 16];
        out[..8].copy_from_slice(&h1.to_le_bytes());
        out[8..].copy_from_slice(&h2.to_le_bytes());
        out
    }

    pub fn normalize_closure_roots(roots: &[String]) -> Vec<String> {
        let mut out: Vec<String> = roots
            .iter()
            .map(|r| {
                if r.ends_with(".olean") || r.contains('/') || r.contains('\\') {
                    let p = normalize_lean_path(Path::new(r));
                    super::resolve_olean_file(&p).1
                } else {
                    r.clone()
                }
            })
            .collect();
        out.sort();
        out.dedup();
        out
    }

    fn key_to_rel_path(norm_key: &str) -> Option<PathBuf> {
        let (mod_part, ext) = if let Some(m) = norm_key.strip_suffix(".olean.server") {
            (m, ".olean.server")
        } else if let Some(m) = norm_key.strip_suffix(".olean.private") {
            (m, ".olean.private")
        } else if let Some(m) = norm_key.strip_suffix(".olean") {
            (m, ".olean")
        } else {
            return None;
        };
        let mut rel = PathBuf::new();
        for seg in mod_part.split('.') {
            if !seg.is_empty() {
                rel.push(seg);
            }
        }
        let fname = rel.file_name()?.to_string_lossy().into_owned();
        rel.set_file_name(format!("{fname}{ext}"));
        Some(rel)
    }

    /// Validates a `CGSNAP03` snapshot's embedded `.olean`/`.ndjson` manifest against disk via parallel
    /// `fs::metadata`, re-hashing file bytes ONLY on `mtime` mismatch or `verify_hashes == true`.
    /// Rejects immediately on root mismatch, missing/extra/shadowing files, size changes, or hash mismatch.
    pub fn validate_closure_manifest(
        manifest_roots: &[String],
        manifest: &[SnapshotManifestEntry],
        target: ClosureTarget<'_>,
        verify_hashes: bool,
    ) -> Result<(), String> {
        match target {
            ClosureTarget::Ndjson { path } => {
                let norm = normalize_lean_path(path);
                let canon = std::fs::canonicalize(&norm).unwrap_or_else(|_| norm.clone());
                let expected_key = canon.to_string_lossy().replace('\\', "/");
                if manifest.len() != 1 {
                    return Err(format!(
                        "snapshot manifest expected {} entries, found 1 ndjson target",
                        manifest.len()
                    ));
                }
                let entry = &manifest[0];
                if entry.norm_key != expected_key && entry.path != normalize_lean_path_str(&norm.to_string_lossy()) {
                    return Err(format!(
                        "snapshot manifest ndjson path mismatch (`{}` vs `{}`)",
                        entry.norm_key, expected_key
                    ));
                }
                let md = std::fs::metadata(&norm).map_err(|e| {
                    format!("snapshot manifest missing file {}: {e}", norm.display())
                })?;
                if !md.is_file() {
                    return Err(format!("snapshot manifest target is not a file: {}", norm.display()));
                }
                if md.len() != entry.byte_len {
                    return Err(format!(
                        "snapshot closure size mismatch on `{}` ({} != {})",
                        entry.norm_key,
                        md.len(),
                        entry.byte_len
                    ));
                }
                let (secs, nanos) = system_time_parts(md.modified().ok());
                if verify_hashes || secs != entry.mtime_secs || nanos != entry.mtime_nanos {
                    let bytes = std::fs::read(&norm).map_err(|e| {
                        format!("snapshot manifest failed reading {}: {e}", norm.display())
                    })?;
                    let h = hash128_bytes(&bytes);
                    if h != entry.content_hash128 {
                        return Err(format!(
                            "snapshot closure hash mismatch on `{}`",
                            entry.norm_key
                        ));
                    }
                }
                Ok(())
            }
            ClosureTarget::Oleans { roots, search_paths } => {
                let cur_roots = normalize_closure_roots(roots);
                let mut snap_roots = manifest_roots.to_vec();
                snap_roots.sort();
                snap_roots.dedup();
                if snap_roots != cur_roots {
                    return Err(format!(
                        "snapshot closure roots mismatch (snapshot={snap_roots:?}, current={cur_roots:?})"
                    ));
                }
                if manifest.is_empty() && !cur_roots.is_empty() {
                    return Err("snapshot contains empty closure manifest".to_string());
                }
                let key_set: HashSet<&str> =
                    manifest.iter().map(|e| e.norm_key.as_str()).collect();
                manifest
                    .par_iter()
                    .try_for_each(|entry| -> Result<(), String> {
                        let rel = key_to_rel_path(&entry.norm_key).ok_or_else(|| {
                            format!("invalid manifest key `{}`", entry.norm_key)
                        })?;
                        let mut found_path: Option<(PathBuf, std::fs::Metadata)> = None;
                        if entry.norm_key.ends_with(".olean") {
                            for dir in search_paths {
                                let cand = dir.join(&rel);
                                if let Ok(md) = std::fs::metadata(&cand) {
                                    if md.is_file() {
                                        found_path = Some((cand, md));
                                        break;
                                    }
                                }
                            }
                            if found_path.is_none() {
                                let saved_pb = PathBuf::from(&entry.path);
                                if let Ok(md) = std::fs::metadata(&saved_pb) {
                                    if md.is_file() {
                                        found_path = Some((saved_pb, md));
                                    }
                                }
                            }
                            if let Some((ref cand, _)) = found_path {
                                if let Some(mod_part) = entry.norm_key.strip_suffix(".olean") {
                                    let srv_key = format!("{mod_part}.olean.server");
                                    if !key_set.contains(srv_key.as_str()) {
                                        let mut srv_path = cand.clone();
                                        let fname = srv_path
                                            .file_name()
                                            .map(|n| n.to_string_lossy().into_owned())
                                            .unwrap_or_default();
                                        srv_path.set_file_name(format!("{fname}.server"));
                                        if srv_path.is_file() {
                                            return Err(format!(
                                                "snapshot manifest extra `{srv_key}` detected on disk"
                                            ));
                                        }
                                    }
                                    let prv_key = format!("{mod_part}.olean.private");
                                    if !key_set.contains(prv_key.as_str()) {
                                        let mut prv_path = cand.clone();
                                        let fname = prv_path
                                            .file_name()
                                            .map(|n| n.to_string_lossy().into_owned())
                                            .unwrap_or_default();
                                        prv_path.set_file_name(format!("{fname}.private"));
                                        if prv_path.is_file() {
                                            return Err(format!(
                                                "snapshot manifest extra `{prv_key}` detected on disk"
                                            ));
                                        }
                                    }
                                }
                            }
                        } else {
                            let saved_pb = PathBuf::from(&entry.path);
                            if let Ok(md) = std::fs::metadata(&saved_pb) {
                                if md.is_file() {
                                    found_path = Some((saved_pb, md));
                                }
                            }
                            if found_path.is_none() {
                                for dir in search_paths {
                                    let cand = dir.join(&rel);
                                    if let Ok(md) = std::fs::metadata(&cand) {
                                        if md.is_file() {
                                            found_path = Some((cand, md));
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                        let (disk_pb, md) = found_path.ok_or_else(|| {
                            format!(
                                "snapshot closure missing file `{}`",
                                entry.norm_key
                            )
                        })?;
                        if md.len() != entry.byte_len {
                            return Err(format!(
                                "snapshot closure size mismatch on `{}` ({} != {})",
                                entry.norm_key,
                                md.len(),
                                entry.byte_len
                            ));
                        }
                        let (secs, nanos) = system_time_parts(md.modified().ok());
                        if verify_hashes || secs != entry.mtime_secs || nanos != entry.mtime_nanos {
                            let mut f = File::open(&disk_pb).map_err(|e| {
                                format!("snapshot failed reading `{}`: {e}", disk_pb.display())
                            })?;
                            let cap = usize::try_from(md.len())
                                .map_err(|_| "olean exceeds usize".to_string())?;
                            let mut buf = vec![0u8; cap];
                            f.read_exact(&mut buf).map_err(|e| {
                                format!("snapshot failed reading `{}`: {e}", disk_pb.display())
                            })?;
                            let cur_hash = hash128_bytes(&buf);
                            if cur_hash != entry.content_hash128 {
                                return Err(format!(
                                    "snapshot closure hash mismatch on `{}`",
                                    entry.norm_key
                                ));
                            }
                        }
                        Ok(())
                    })?;
                Ok(())
            }
        }
    }

    fn intern_dotted_name_in_store(
        pers: &PersTier,
        store: &mut EStore,
        s: &str,
    ) -> Option<NIdx> {
        let mut cur = store.intern_name(pers, NNodeView::Anonymous).ok()?;
        for part in s.split('.') {
            if part.is_empty() {
                continue;
            }
            let node = if let Ok(num) = part.parse::<u64>() {
                NNodeView::Num(cur, num)
            } else {
                NNodeView::Str(cur, str_to_cp(part))
            };
            cur = store.intern_name(pers, node).ok()?;
        }
        Some(cur)
    }

    struct PrefetchQueue {
        pending: VecDeque<String>,
        seen: HashSet<String>,
        active: usize,
        done: bool,
        collected: Vec<PrefetchedOleanFile>,
        modules_visited: usize,
        err: Option<String>,
    }

    /// Walks and preloads the transitive `.olean` import closure for `root_modules` into `fs`
    /// in parallel (capped at `max_threads.clamp(1, 16)` threads) and returns all reachable files
    /// plus a deterministic 128-bit closure fingerprint.
    pub fn prefetch_olean_closure(
        fs: &CachedFs,
        search_paths: &[PathBuf],
        root_modules: &[String],
        max_threads: usize,
    ) -> Result<PrefetchedClosure, String> {
        if root_modules.is_empty() {
            return Ok(PrefetchedClosure {
                files: Vec::new(),
                fingerprint: compute_closure_fingerprint(&[]),
                modules_visited: 0,
            });
        }
        let sp_cp: Vec<Vec<u32>> = search_paths
            .iter()
            .map(|p| str_to_cp(&p.to_string_lossy()))
            .collect();
        let mut pending = VecDeque::new();
        let mut seen = HashSet::new();
        for r in root_modules {
            if seen.insert(r.clone()) {
                pending.push_back(r.clone());
            }
        }
        let n_workers = max_threads.clamp(1, 16);
        let queue = Mutex::new(PrefetchQueue {
            pending,
            seen,
            active: 0,
            done: false,
            collected: Vec::new(),
            modules_visited: 0,
            err: None,
        });
        let cv = Condvar::new();

        std::thread::scope(|scope| {
            for _ in 0..n_workers {
                scope.spawn(|| {
                    let pers = PersTier::empty();
                    let mut ar = EStore::empty();
                    let pk = match spec::olean_pins(&pers, &mut ar) {
                        Ok(p) => p,
                        Err(_) => {
                            let mut q = queue.lock().expect("queue lock");
                            q.err.get_or_insert_with(|| {
                                "failed to initialize OleanPins in prefetch worker".to_string()
                            });
                            q.done = true;
                            cv.notify_all();
                            return;
                        }
                    };
                    let ext_o = files::part_ext(0);
                    let ext_s = files::part_ext(1);
                    let ext_p = files::part_ext(2);

                    loop {
                        let mod_name = {
                            let mut q = queue.lock().expect("queue lock");
                            loop {
                                if q.done || q.err.is_some() {
                                    return;
                                }
                                if let Some(m) = q.pending.pop_front() {
                                    q.active += 1;
                                    break m;
                                }
                                if q.active == 0 {
                                    q.done = true;
                                    cv.notify_all();
                                    return;
                                }
                                q = cv.wait(q).expect("queue condvar");
                            }
                        };

                        let mut local_files: Vec<PrefetchedOleanFile> = Vec::with_capacity(3);
                        let mut imports: Vec<String> = Vec::new();
                        let mut local_err: Option<String> = None;

                        if let Some(m_nidx) = intern_dotted_name_in_store(&pers, &mut ar, &mod_name)
                        {
                            match files::find_module(fs, &pers, &ar, &sp_cp, &m_nidx) {
                                Ok(loc) => {
                                    match files::mod_file(&pers, &ar, &loc.dir, &m_nidx, &ext_o) {
                                        Ok(p_o) => match fs.read_bin_arc_with_meta(&p_o) {
                                            Ok((ex_bytes, byte_len, mtime_secs, mtime_nanos, content_hash128)) => {
                                                if (ex_bytes.len() as u64) >= region::DATA_START
                                                    && (ex_bytes.len() as u64) <= region::PART_MAX
                                                    && &ex_bytes[0..5] == b"olean"
                                                {
                                                    if let Ok(imps) = header::imports_pre(
                                                        &pk, &pers, &mut ar, &ex_bytes,
                                                    ) {
                                                        for imp in imps {
                                                            let nt = view::name_text(
                                                                &pers,
                                                                &ar,
                                                                &imp.module,
                                                            );
                                                            let s = cp_to_str(&nt);
                                                            if !s.is_empty() {
                                                                imports.push(s);
                                                            }
                                                        }
                                                    }
                                                }
                                                let path_str = normalize_lean_path_str(&cp_to_str(&p_o));
                                                local_files.push(PrefetchedOleanFile {
                                                    key: format!("{mod_name}.olean"),
                                                    path_cp: p_o,
                                                    path_str,
                                                    bytes: ex_bytes,
                                                    byte_len,
                                                    mtime_secs,
                                                    mtime_nanos,
                                                    content_hash128,
                                                });
                                            }
                                            Err(e) => {
                                                local_err = Some(format!(
                                                    "prefetch failed reading {mod_name}.olean: {}",
                                                    cp_to_str(&e)
                                                ));
                                            }
                                        },
                                        Err(_) => {
                                            local_err = Some(format!(
                                                "prefetch failed formatting path for {mod_name}.olean"
                                            ));
                                        }
                                    }

                                    if local_err.is_none() && loc.has_server {
                                        if let Ok(p_s) = files::mod_file(
                                            &pers, &ar, &loc.dir, &m_nidx, &ext_s,
                                        ) {
                                            if let Ok((sb, byte_len, mtime_secs, mtime_nanos, content_hash128)) = fs.read_bin_arc_with_meta(&p_s) {
                                                let path_str = normalize_lean_path_str(&cp_to_str(&p_s));
                                                local_files.push(PrefetchedOleanFile {
                                                    key: format!("{mod_name}.olean.server"),
                                                    path_cp: p_s,
                                                    path_str,
                                                    bytes: sb,
                                                    byte_len,
                                                    mtime_secs,
                                                    mtime_nanos,
                                                    content_hash128,
                                                });
                                            }
                                        }
                                    }
                                    if local_err.is_none() && loc.has_private {
                                        if let Ok(p_p) = files::mod_file(
                                            &pers, &ar, &loc.dir, &m_nidx, &ext_p,
                                        ) {
                                            if let Ok((pb, byte_len, mtime_secs, mtime_nanos, content_hash128)) = fs.read_bin_arc_with_meta(&p_p) {
                                                let path_str = normalize_lean_path_str(&cp_to_str(&p_p));
                                                local_files.push(PrefetchedOleanFile {
                                                    key: format!("{mod_name}.olean.private"),
                                                    path_cp: p_p,
                                                    path_str,
                                                    bytes: pb,
                                                    byte_len,
                                                    mtime_secs,
                                                    mtime_nanos,
                                                    content_hash128,
                                                });
                                            }
                                        }
                                    }
                                }
                                Err(_) => {
                                    local_err = Some(format!(
                                        "module {mod_name}: not found on search path"
                                    ));
                                }
                            }
                        } else {
                            local_err = Some(format!("invalid module name: {mod_name}"));
                        }

                        let mut q = queue.lock().expect("queue lock");
                        q.active -= 1;
                        if let Some(e) = local_err {
                            if q.err.is_none() {
                                q.err = Some(e);
                            }
                            q.done = true;
                            cv.notify_all();
                        } else {
                            q.modules_visited += 1;
                            q.collected.extend(local_files);
                            for imp in imports {
                                if q.seen.insert(imp.clone()) {
                                    q.pending.push_back(imp);
                                }
                            }
                            if q.pending.is_empty() && q.active == 0 {
                                q.done = true;
                            }
                            cv.notify_all();
                        }
                    }
                });
            }
        });

        let mut q = queue.into_inner().expect("queue mutex");
        if let Some(err) = q.err.take() {
            return Err(err);
        }
        q.collected.sort_by(|a, b| a.key.cmp(&b.key));
        let fingerprint = compute_closure_fingerprint(&q.collected);
        Ok(PrefetchedClosure {
            files: q.collected,
            fingerprint,
            modules_visited: q.modules_visited,
        })
    }
}

pub use cache_support::{
    combine_chunk_hashes128, compute_chunked_checksum128, compute_closure_fingerprint,
    hash128_bytes, hash128_bytes_with_seed, normalize_closure_roots, prefetch_olean_closure,
    system_time_parts, validate_closure_manifest, CachedFs, CachedFsStats, ClosureTarget,
    PrefetchedClosure, PrefetchedOleanFile, SnapshotManifestEntry, CHUNK_CHECKSUM_BYTES,
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cached_fs_hits_range_and_revalidate() {
        let dir = std::env::temp_dir().join(format!(
            "con_gpu_cached_fs_test_{}",
            std::process::id()
        ));
        let _ = std::fs::remove_dir_all(&dir);
        std::fs::create_dir_all(&dir).expect("mkdir");
        let file = dir.join("sample.bin");
        std::fs::write(&file, b"abcdefghij0123456789").expect("write");

        let cp = str_to_cp(&file.to_string_lossy());
        let cfs = CachedFs::new();
        assert!(cfs.path_exists(&cp).expect("exists"));
        assert!(cfs.path_exists(&cp).expect("exists hit"));
        assert_eq!(cfs.read_bin_file(&cp).expect("read 1"), b"abcdefghij0123456789");
        assert_eq!(cfs.read_bin_file(&cp).expect("read 2"), b"abcdefghij0123456789");
        assert_eq!(cfs.read_range(&cp, 4, 6).expect("range"), b"efghij");
        assert_eq!(cfs.file_size(&cp).expect("size"), 20);

        let st = cfs.stats();
        assert_eq!(st.file_misses, 1);
        assert_eq!(st.file_hits, 2);
        assert_eq!(st.exists_misses, 1);
        assert_eq!(st.exists_hits, 1);
        assert_eq!(st.cached_files, 1);

        // Changing length on disk triggers eviction on revalidate_on_disk.
        std::fs::write(&file, b"updated-payload-longer-bytes!").expect("rewrite");
        let evicted = cfs.revalidate_on_disk();
        assert_eq!(evicted, 1);
        assert_eq!(cfs.cached_file_count(), 0);
        assert_eq!(
            cfs.read_bin_file(&cp).expect("re-read"),
            b"updated-payload-longer-bytes!"
        );
        let _ = std::fs::remove_dir_all(&dir);
    }

    #[test]
    fn closure_fingerprint_detects_single_byte_change() {
        use std::sync::Arc;
        let f1 = PrefetchedOleanFile::from_bytes(
            "A.olean".to_string(),
            str_to_cp("A.olean"),
            Arc::new(vec![1u8, 2, 3, 4, 5, 6, 7, 8, 9]),
        );
        let f2 = PrefetchedOleanFile::from_bytes(
            "B.olean".to_string(),
            str_to_cp("B.olean"),
            Arc::new(vec![10u8, 20, 30]),
        );
        let f1_mut = PrefetchedOleanFile::from_bytes(
            "A.olean".to_string(),
            str_to_cp("A.olean"),
            Arc::new(vec![1u8, 2, 3, 4, 5, 6, 7, 8, 10]),
        );

        let h_ab = compute_closure_fingerprint(&[f1.clone(), f2.clone()]);
        let h_ba = compute_closure_fingerprint(&[f2.clone(), f1.clone()]);
        let h_mut = compute_closure_fingerprint(&[f1_mut, f2]);
        assert_eq!(h_ab, h_ba, "fingerprint must be order-independent");
        assert_ne!(h_ab, h_mut, "fingerprint must detect single-byte mutation");
    }

    #[test]
    fn prefetch_init_closure_parallel_and_deterministic() {
        let init_path = PathBuf::from(
            "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init.olean",
        );
        if !init_path.exists() {
            return;
        }
        let sp = discover_default_search_paths();
        let cfs1 = CachedFs::new();
        let c1 = prefetch_olean_closure(&cfs1, &sp, &["Init".to_string()], 1)
            .expect("prefetch 1 thread");
        let cfs8 = CachedFs::new();
        let c8 = prefetch_olean_closure(&cfs8, &sp, &["Init".to_string()], 16)
            .expect("prefetch 16 threads");
        assert!(c8.modules_visited > 50, "visited={}", c8.modules_visited);
        assert_eq!(c1.modules_visited, c8.modules_visited);
        assert_eq!(c1.files.len(), c8.files.len());
        assert_eq!(c1.fingerprint, c8.fingerprint);
        assert!(cfs8.cached_file_count() >= c8.files.len());
    }

    #[test]
    fn wsl_mnt_path_normalization_handles_drives_and_non_drives() {
        assert_eq!(
            normalize_wsl_mnt_path("/mnt/c/Users/devin/Desktop/lean/Init.olean"),
            "C:/Users/devin/Desktop/lean/Init.olean"
        );
        assert_eq!(normalize_wsl_mnt_path("/mnt/d"), "D:/");
        assert_eq!(normalize_wsl_mnt_path("/mnt/e/"), "E:/");
        assert_eq!(normalize_wsl_mnt_path("/mnt/share/foo"), "/mnt/share/foo");
        assert_eq!(normalize_wsl_mnt_path("/mnt/1/foo"), "/mnt/1/foo");
        assert_eq!(normalize_wsl_mnt_path("Init.Data.Nat"), "Init.Data.Nat");
    }

    #[test]
    fn split_search_path_handles_mixed_windows_and_wsl_lists() {
        let parts = split_search_path("/mnt/c/lean/lib;C:/proj/.lake/lib:/mnt/d/extra/lib");
        if cfg!(windows) {
            assert_eq!(
                parts,
                vec![
                    PathBuf::from("C:/lean/lib"),
                    PathBuf::from("C:/proj/.lake/lib"),
                    PathBuf::from("D:/extra/lib"),
                ]
            );
        } else {
            assert_eq!(parts.len(), 3);
        }
    }
}
