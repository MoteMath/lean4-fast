use std::collections::HashMap;
use std::fs::File;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::time::Instant;

use flate2::read::GzDecoder;

use con_ron_core::arena::checker;
use con_ron_core::arena::nat_op_pin_set::INatOpPinSet;
use con_ron_core::arena::env::IDeclaration;
use con_ron_core::arena::handle::{EIdx, NIdx, ETAG_BVAR};
use con_ron_core::arena::monad::AState;
use con_ron_core::arena::pins::intern_reserved_pins;
use con_ron_core::arena::store::{EStore, PersTier};
use con_ron_core::arena::stream_index::{self, IStreamIndex};
use con_ron_core::frontend::export_c::{self, ParseResultD};
use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
use con_ron_core::frontend::olean::records::{
    fill_records, read_oleans, ModRef, OleanRead,
};
use con_ron_core::frontend::olean::spec::OleanPins;
use con_ron_core::frontend::prepare::{self, PreludeIx};
use con_ron_core::frontend::prelude::builtin_prelude_e;
use con_ron_core::kernel::core_types::CheckError;
use con_ron_core::kernel::env::CheckMode;
use con_ron_core::kernel::pins_decode;
use con_ron_core::ron::nat::Nat;

use crate::fs::{
    compute_closure_fingerprint, cp_to_str, discover_default_search_paths, hash128_bytes,
    normalize_closure_roots, normalize_lean_path, normalize_lean_path_str, prefetch_olean_closure,
    resolve_olean_file, str_to_cp, system_time_parts, CachedFs, PrefetchedClosure,
    PrefetchedOleanFile, SnapshotManifestEntry,
};
use crate::verify_host::StructuralPrefixCmp;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerificationVerdict {
    Accepted {
        file_records: usize,
        fold_records: usize,
    },
    Rejected {
        message: String,
        fold_pos: u64,
    },
    Declined {
        message: String,
        fold_pos: u64,
    },
    Error {
        message: String,
        line_or_pos: u64,
    },
}

impl VerificationVerdict {
    pub fn exit_code(&self) -> u8 {
        match self {
            VerificationVerdict::Accepted { .. } => 0,
            VerificationVerdict::Rejected { .. } => 1,
            VerificationVerdict::Declined { .. } => 2,
            VerificationVerdict::Error { .. } => 3,
        }
    }

    pub fn failure_pos(&self) -> Option<u64> {
        match self {
            VerificationVerdict::Accepted { .. } => None,
            VerificationVerdict::Rejected { fold_pos, .. }
            | VerificationVerdict::Declined { fold_pos, .. }
            | VerificationVerdict::Error {
                line_or_pos: fold_pos,
                ..
            } => Some(*fold_pos),
        }
    }
}

#[derive(Clone, Debug)]
pub enum InputSpec {
    Oleans {
        roots: Vec<String>,
        search_paths: Vec<PathBuf>,
        constants: Option<Vec<String>>,
        materialize_thms: bool,
    },
    Ndjson {
        path: PathBuf,
    },
}

pub struct LoadedEnvironment {
    pub pers: PersTier,
    pub pins: con_ron_core::arena::pins::Pins,
    pub ipins: Vec<INatOpPinSet>,
    pub decls: Vec<IDeclaration>,
    pub file_records: usize,
    pub synthesized: u64,
    pub hoisted: usize,
    pub olean: Option<(OleanPins, Vec<ModRef>, Vec<Vec<u32>>)>,
    pub load_ns: u128,
    pub materialize_ns: u128,
    pub index_ns: u128,
    pub thm_materialized_count: usize,
    pub closure_fingerprint: Option<[u8; 16]>,
    pub closure_roots: Vec<String>,
    pub closure_manifest: Vec<SnapshotManifestEntry>,
    pub module_hashes: HashMap<String, [u8; 16]>,
    pub preverified_prefix: usize,
}

impl LoadedEnvironment {
    pub fn mode(&self) -> CheckMode {
        CheckMode::Verified
    }

    pub fn decl_name_str(&self, decl_idx: usize) -> String {
        if let Some(d) = self.decls.get(decl_idx) {
            let ns = con_ron_core::arena::env::i_declaration_names(d);
            if let Some(n) = ns.first() {
                return nidx_to_string(&self.pers, n);
            }
        }
        format!("<decl#{}>", decl_idx)
    }
}

pub fn nidx_to_string(pers: &PersTier, n: &NIdx) -> String {
    let dummy = EStore::empty_frozen();
    match con_ron_core::arena::env::read_name(pers, &dummy, n) {
        Ok(name) => cp_to_str(&con_ron_core::kernel::name::render(&name)),
        Err(_) => "<dangling>".to_string(),
    }
}

pub fn check_error_to_string(e: &CheckError) -> String {
    let cps = match e {
        CheckError::NotImplemented(m)
        | CheckError::Invalid(m)
        | CheckError::Internal(m)
        | CheckError::Native(m) => m,
    };
    cp_to_str(cps)
}

pub fn classify_error(e: CheckError, fold_pos: u64) -> VerificationVerdict {
    let message = check_error_to_string(&e);
    match e {
        CheckError::Invalid(_) => VerificationVerdict::Rejected { message, fold_pos },
        CheckError::NotImplemented(_) | CheckError::Native(_) => {
            VerificationVerdict::Declined { message, fold_pos }
        }
        CheckError::Internal(_) => VerificationVerdict::Error {
            message,
            line_or_pos: fold_pos,
        },
    }
}

/// Build an `InputSpec::Oleans` from CLI positional args (handles both file paths like
/// `.../Init.olean` and dotted module names like `Init`, `Init.Core`, `Std`).
pub fn build_olean_input(
    paths_or_modules: &[String],
    extra_search_paths: &[PathBuf],
    constants: Option<Vec<String>>,
    materialize_thms: bool,
) -> InputSpec {
    let mut roots = Vec::with_capacity(paths_or_modules.len());
    let mut search_paths: Vec<PathBuf> = extra_search_paths
        .iter()
        .map(|p| normalize_lean_path(p))
        .collect();
    for item in paths_or_modules {
        let norm_item = normalize_lean_path_str(item);
        let p = Path::new(&norm_item);
        if norm_item.ends_with(".olean") || p.exists() {
            let (dir, mod_name) = resolve_olean_file(p);
            if let Some(d) = dir {
                if !search_paths.contains(&d) {
                    search_paths.push(d);
                }
            }
            roots.push(mod_name);
        } else {
            roots.push(norm_item);
        }
    }
    let mut dedup: Vec<PathBuf> = Vec::with_capacity(search_paths.len());
    let mut seen_keys: Vec<String> = Vec::new();
    let push_dedup = |dedup: &mut Vec<PathBuf>, seen: &mut Vec<String>, d: PathBuf| {
        let canon = std::fs::canonicalize(&d).unwrap_or(d);
        let s = canon.to_string_lossy();
        let clean = PathBuf::from(s.strip_prefix(r"\\?\").unwrap_or(&s));
        let key = clean.to_string_lossy().replace('\\', "/").to_ascii_lowercase();
        if !seen.contains(&key) {
            seen.push(key);
            dedup.push(clean);
        }
    };
    for d in search_paths {
        push_dedup(&mut dedup, &mut seen_keys, d);
    }
    if !dedup.iter().any(|d| d.join("Init.olean").exists()) {
        for d in discover_default_search_paths() {
            push_dedup(&mut dedup, &mut seen_keys, d);
        }
    }
    InputSpec::Oleans {
        roots,
        search_paths: dedup,
        constants,
        materialize_thms,
    }
}

fn intern_dotted_name(pers: &PersTier, st: &mut AState, s: &str) -> Result<NIdx, CheckError> {
    let mut cur = st
        .store
        .intern_name(pers, con_ron_core::arena::store::NNodeView::Anonymous)?;
    for part in s.split('.') {
        if let Ok(num) = part.parse::<u64>() {
            cur = st
                .store
                .intern_name(pers, con_ron_core::arena::store::NNodeView::Num(cur, num))?;
        } else {
            cur = st.store.intern_name(
                pers,
                con_ron_core::arena::store::NNodeView::Str(cur, str_to_cp(part)),
            )?;
        }
    }
    Ok(cur)
}

fn read_ndjson_file(
    pers: &PersTier,
    st: &mut AState,
    path: &Path,
) -> Result<ParseResultD, (CheckError, u64)> {
    let is_gz = path
        .extension()
        .map(|x| x.to_string_lossy().eq_ignore_ascii_case("gz"))
        .unwrap_or(false);
    let mut reader: Box<dyn Read> = match File::open(path) {
        Ok(f) => {
            if is_gz {
                Box::new(GzDecoder::new(f))
            } else {
                Box::new(f)
            }
        }
        Err(e) => {
            return Err((
                CheckError::Internal(str_to_cp(&format!("{}: {}", path.display(), e))),
                0,
            ));
        }
    };

    struct ReaderChunkSource<'a> {
        r: &'a mut dyn Read,
        err: Option<std::io::Error>,
    }
    impl<'a> export_c::ChunkSource for ReaderChunkSource<'a> {
        fn next_chunk(&mut self) -> Vec<u8> {
            let mut buf = vec![0u8; export_c::CHUNK_SIZE];
            let mut total = 0usize;
            while total < buf.len() {
                match self.r.read(&mut buf[total..]) {
                    Ok(0) => break,
                    Ok(n) => total += n,
                    Err(e) => {
                        self.err = Some(e);
                        return Vec::new();
                    }
                }
            }
            buf.truncate(total);
            buf
        }
    }

    let mut src = ReaderChunkSource {
        r: &mut *reader,
        err: None,
    };
    let res = export_c::parse_source(pers, st, &mut src);
    if let Some(e) = src.err {
        return Err((
            CheckError::Internal(str_to_cp(&format!("{}: {}", path.display(), e))),
            0,
        ));
    }
    res
}

fn load_max_nat_default() -> Nat {
    // Official Lean kernel default (128 MiB).
    con_ron_core::arena::pins::max_nat_size_default()
}

fn module_name_from_file_key(key: &str) -> &str {
    key.strip_suffix(".olean.private")
        .or_else(|| key.strip_suffix(".olean.server"))
        .or_else(|| key.strip_suffix(".olean"))
        .unwrap_or(key)
}

fn build_module_hashes(closure: &PrefetchedClosure) -> HashMap<String, [u8; 16]> {
    let mut grouped: HashMap<String, Vec<PrefetchedOleanFile>> = HashMap::new();
    for f in &closure.files {
        let mod_name = module_name_from_file_key(&f.key).to_string();
        grouped.entry(mod_name).or_default().push(f.clone());
    }
    let mut out = HashMap::with_capacity(grouped.len());
    for (mod_name, files) in grouped {
        out.insert(mod_name, compute_closure_fingerprint(&files));
    }
    out
}

fn compute_prepared_prefix(
    base: &LoadedEnvironment,
    empty_pers: &PersTier,
    store: &EStore,
    prepared_decls: &[IDeclaration],
    values: &[ModRef],
    target_mod_hashes: &HashMap<String, [u8; 16]>,
) -> usize {
    let limit = base.decls.len().min(prepared_decls.len());
    let empty_base_st = EStore::empty_frozen();
    let mut cmp = StructuralPrefixCmp::new(&base.pers, &empty_base_st, empty_pers, store);
    let mut mod_match_cache: Vec<Option<bool>> = vec![None; values.len()];
    let mut k = 0usize;
    while k < limit {
        let allow_lazy_a = k < base.preverified_prefix;
        let ok = cmp.eq_decl_prefix_with_lazy_thm(
            &base.decls[k],
            &prepared_decls[k],
            allow_lazy_a,
            &mut |vb: &EIdx| -> bool {
                let Some(code) = store.view_bvar(empty_pers, vb) else {
                    return false;
                };
                let mod_idx = con_ron_core::frontend::olean::lazy::ref_module(code) as usize;
                let Some(slot) = mod_match_cache.get_mut(mod_idx) else {
                    return false;
                };
                if let Some(cached) = *slot {
                    return cached;
                }
                let ok_mod = match con_ron_core::arena::env::read_name(
                    empty_pers,
                    store,
                    &values[mod_idx].name,
                ) {
                    Ok(nm) => {
                        let mod_name = cp_to_str(&con_ron_core::kernel::name::render(&nm));
                        match (
                            base.module_hashes.get(&mod_name),
                            target_mod_hashes.get(&mod_name),
                        ) {
                            (Some(hb), Some(ht)) => hb == ht,
                            _ => false,
                        }
                    }
                    Err(_) => false,
                };
                *slot = Some(ok_mod);
                ok_mod
            },
        );
        if !ok {
            break;
        }
        k += 1;
    }
    k
}

pub fn load_environment(spec: &InputSpec) -> Result<LoadedEnvironment, VerificationVerdict> {
    let cfs = CachedFs::new();
    load_environment_with_fs_and_base(spec, &cfs, None)
}

/// Loads `spec` using a shared thread-safe `CachedFs` (prefetched across up to 16 threads).
pub fn load_environment_with_fs(
    spec: &InputSpec,
    cached_fs: &CachedFs,
) -> Result<LoadedEnvironment, VerificationVerdict> {
    load_environment_with_fs_and_base(spec, cached_fs, None)
}

/// Loads `spec` incrementally against an already-verified `base` environment, skipping `fill_records`
/// theorem proof decoding for the unchanged prefix `[0..preverified_prefix)`.
/// Caller must ensure `base` was already kernel-verified under compatible `VerifyOptions`.
pub fn load_environment_from_prefix(
    spec: &InputSpec,
    base: &LoadedEnvironment,
    cached_fs: Option<&CachedFs>,
) -> Result<LoadedEnvironment, VerificationVerdict> {
    match cached_fs {
        Some(fs) => load_environment_with_fs_and_base(spec, fs, Some(base)),
        None => {
            let fs = CachedFs::new();
            load_environment_with_fs_and_base(spec, &fs, Some(base))
        }
    }
}

pub fn load_environment_with_fs_and_base(
    spec: &InputSpec,
    cached_fs: &CachedFs,
    base: Option<&LoadedEnvironment>,
) -> Result<LoadedEnvironment, VerificationVerdict> {
    std::thread::scope(|scope| {
        match std::thread::Builder::new()
            .name("con-gpu-loader".to_string())
            .stack_size(1 << 30)
            .spawn_scoped(scope, || load_environment_inner(spec, cached_fs, base))
        {
            Ok(h) => match h.join() {
                Ok(res) => res,
                Err(_) => Err(VerificationVerdict::Error {
                    message: "loader thread panicked".to_string(),
                    line_or_pos: 0,
                }),
            },
            Err(_) => load_environment_inner(spec, cached_fs, base),
        }
    })
}

fn load_environment_inner(
    spec: &InputSpec,
    cached_fs: &CachedFs,
    base: Option<&LoadedEnvironment>,
) -> Result<LoadedEnvironment, VerificationVerdict> {
    let t_start = Instant::now();
    let empty_pers = PersTier::empty();
    let mut st = AState::init(EStore::empty());

    if let Err(e) = intern_reserved_pins(&empty_pers, &mut st) {
        return Err(classify_error(e, 0));
    }
    let prelude_ix: PreludeIx = match builtin_prelude_e(&empty_pers, &mut st) {
        Ok(p) => p,
        Err((e, line)) => return Err(classify_error(e, line)),
    };

    let mut closure_fingerprint: Option<[u8; 16]> = None;
    let mut closure_roots: Vec<String> = Vec::new();
    let mut closure_manifest: Vec<SnapshotManifestEntry> = Vec::new();
    let mut module_hashes: HashMap<String, [u8; 16]> = HashMap::new();

    let (parsed_decls, olean_read, sp_cp): (Vec<IDeclaration>, Option<OleanRead>, Vec<Vec<u32>>) =
        match spec {
            InputSpec::Ndjson { path } => {
                let norm_p = normalize_lean_path(path);
                let norm_str = norm_p.to_string_lossy().into_owned();
                if let Ok(meta) = std::fs::metadata(&norm_p) {
                    if let Ok(bytes) = std::fs::read(&norm_p) {
                        let content_hash128 = hash128_bytes(&bytes);
                        let (mtime_secs, mtime_nanos) = system_time_parts(meta.modified().ok());
                        closure_fingerprint = Some(content_hash128);
                        closure_roots = vec![norm_str.clone()];
                        closure_manifest.push(SnapshotManifestEntry {
                            norm_key: norm_str.clone(),
                            path: norm_str,
                            byte_len: meta.len(),
                            mtime_secs,
                            mtime_nanos,
                            content_hash128,
                        });
                    }
                }
                match read_ndjson_file(&empty_pers, &mut st, &norm_p) {
                    Ok(pr) => (pr.decls, None, Vec::new()),
                    Err((e, line)) => return Err(classify_error(e, line)),
                }
            }
            InputSpec::Oleans {
                roots,
                search_paths,
                constants,
                ..
            } => {
                closure_roots = normalize_closure_roots(roots);
                if let Ok(closure) = prefetch_olean_closure(cached_fs, search_paths, roots, 16) {
                    closure_fingerprint = Some(closure.fingerprint);
                    module_hashes = build_module_hashes(&closure);
                    closure_manifest = closure
                        .files
                        .iter()
                        .map(|f| f.to_manifest_entry())
                        .collect();
                    closure_manifest.sort_by(|a, b| a.norm_key.cmp(&b.norm_key));
                }
                let sp_cp: Vec<Vec<u32>> = search_paths
                    .iter()
                    .map(|p| str_to_cp(&p.to_string_lossy()))
                    .collect();
                let mut root_names = Vec::with_capacity(roots.len());
                for r in roots {
                    match intern_dotted_name(&empty_pers, &mut st, r) {
                        Ok(n) => root_names.push(n),
                        Err(e) => return Err(classify_error(e, 0)),
                    }
                }
                let const_names = match constants {
                    None => None,
                    Some(cs) => {
                        let mut v = Vec::with_capacity(cs.len());
                        for c in cs {
                            match intern_dotted_name(&empty_pers, &mut st, c) {
                                Ok(n) => v.push(n),
                                Err(e) => return Err(classify_error(e, 0)),
                            }
                        }
                        Some(v)
                    }
                };
                match read_oleans(
                    cached_fs,
                    &empty_pers,
                    &mut st.store,
                    &sp_cp,
                    &root_names,
                    &const_names,
                ) {
                    Ok(mut rd) => {
                        let decls = std::mem::take(&mut rd.decls);
                        (decls, Some(rd), sp_cp)
                    }
                    Err((e, line)) => return Err(classify_error(e, line)),
                }
            }
        };

    let file_records = parsed_decls.len();

    let prepared = match &olean_read {
        None => prepare::prepare_d(&empty_pers, &mut st, prelude_ix, parsed_decls, &DeclUsedConsts),
        Some(rd) => prepare::prepare_d(&empty_pers, &mut st, prelude_ix, parsed_decls, rd),
    };
    let mut prepared = match prepared {
        Ok(p) => p,
        Err(e) => return Err(classify_error(e, 0)),
    };

    let pins_decoded = match pins_decode::decode_embedded() {
        Ok(p) => p,
        Err(e) => return Err(classify_error(e, 0)),
    };
    let max_nat = load_max_nat_default();
    let ipins = match checker::intern_all_pins(&empty_pers, &mut st, &pins_decoded, &max_nat) {
        Ok(ip) => ip,
        Err(e) => return Err(classify_error(e, 0)),
    };

    let load_ns = t_start.elapsed().as_nanos();

    let materialize_thms = matches!(
        spec,
        InputSpec::Oleans {
            materialize_thms: true,
            ..
        }
    );

    let mut materialize_ns: u128 = 0;
    let mut thm_materialized_count: usize = 0;

    let olean_kept: Option<(OleanPins, Vec<ModRef>, Vec<Vec<u32>>)> =
        olean_read.map(|rd| (rd.pins, rd.values, sp_cp));

    let matching_prefix = if materialize_thms {
        if let (Some(base_env), Some((_, ref values, _))) = (base, &olean_kept) {
            if !base_env.module_hashes.is_empty() && !module_hashes.is_empty() {
                compute_prepared_prefix(
                    base_env,
                    &empty_pers,
                    &st.store,
                    &prepared.decls,
                    values,
                    &module_hashes,
                )
            } else {
                0
            }
        } else {
            0
        }
    } else {
        0
    };

    if materialize_thms {
        if let Some((ref pk, ref values, ref sp)) = olean_kept {
            let t_mat = Instant::now();
            if matching_prefix < prepared.decls.len() {
                let delta_decls = prepared.decls.split_off(matching_prefix);
                match fill_records(cached_fs, pk, &empty_pers, &mut st.store, sp, values, &delta_decls) {
                    Ok(filled) => {
                        for d in &filled {
                            if let IDeclaration::ThmDecl(_, v) = d {
                                if v.tag() != ETAG_BVAR {
                                    thm_materialized_count += 1;
                                }
                            }
                        }
                        prepared.decls.extend(filled);
                    }
                    Err(_) => {
                        // Preserve lazy theorem references cleanly if any edge module fails eager fill.
                        prepared.decls.extend(delta_decls);
                    }
                }
            }
            materialize_ns = t_mat.elapsed().as_nanos();
        }
    }

    let t_idx = Instant::now();
    let ix: IStreamIndex = match stream_index::build_index(
        &empty_pers,
        &mut st,
        stream_index::stream_index_empty(),
        &prepared.decls,
        0,
    ) {
        Ok(ix) => ix,
        Err((e, pos)) => return Err(classify_error(e, pos)),
    };
    let pers: PersTier = checker::freeze_tier(&mut st.store, ix);
    let index_ns = t_idx.elapsed().as_nanos();

    Ok(LoadedEnvironment {
        pers,
        pins: st.pins,
        ipins,
        decls: prepared.decls,
        file_records,
        synthesized: prepared.synthesised,
        hoisted: prepared.hoisted.len(),
        olean: olean_kept,
        load_ns,
        materialize_ns,
        index_ns,
        thm_materialized_count,
        closure_fingerprint,
        closure_roots,
        closure_manifest,
        module_hashes,
        preverified_prefix: matching_prefix,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::verify_host::{verify_host_parallel, verify_host_range_with, VerifyOptions};

    #[test]
    fn prefix_skipped_load_matches_cold_suffix_and_skips_base_thms() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let prelude_path = PathBuf::from(
                    "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init/Prelude.olean",
                );
                let core_path = PathBuf::from(
                    "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init/Core.olean",
                );
                if !prelude_path.exists() || !core_path.exists() {
                    return;
                }
                let sp_pb = vec![PathBuf::from(
                    "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean",
                )];
                let prelude_spec = build_olean_input(
                    &[prelude_path.to_string_lossy().into_owned()],
                    &sp_pb,
                    None,
                    true,
                );
                let core_spec = build_olean_input(
                    &[core_path.to_string_lossy().into_owned()],
                    &sp_pb,
                    None,
                    true,
                );

                let cfs = CachedFs::new();
                let env_base = load_environment_with_fs(&prelude_spec, &cfs).expect("Prelude loads");
                let (v_base, _) = verify_host_parallel(&env_base, Some(4));
                assert!(matches!(v_base, VerificationVerdict::Accepted { .. }), "{v_base:?}");

                let env_cold = load_environment(&core_spec).expect("Core cold loads");
                let env_inc = load_environment_from_prefix(&core_spec, &env_base, Some(&cfs))
                    .expect("Core inc loads");

                assert_eq!(env_inc.decls.len(), env_cold.decls.len());
                assert_eq!(env_inc.preverified_prefix, env_base.decls.len());
                assert!(env_inc.preverified_prefix > 100);
                assert!(
                    env_inc.thm_materialized_count < env_cold.thm_materialized_count,
                    "inc materialized={} cold={}",
                    env_inc.thm_materialized_count,
                    env_cold.thm_materialized_count
                );

                let empty_inc = EStore::empty_frozen();
                let empty_cold = EStore::empty_frozen();
                let mut cmp =
                    StructuralPrefixCmp::new(&env_inc.pers, &empty_inc, &env_cold.pers, &empty_cold);
                for i in 0..env_cold.decls.len() {
                    assert_eq!(env_inc.decl_name_str(i), env_cold.decl_name_str(i), "idx={i}");
                    if i >= env_inc.preverified_prefix {
                        assert!(
                            cmp.eq_decl_prefix_with_lazy_thm(
                                &env_inc.decls[i],
                                &env_cold.decls[i],
                                false,
                                |_| false
                            ),
                            "suffix mismatch at {i} ({})",
                            env_cold.decl_name_str(i)
                        );
                    }
                }

                let (v_inc, tel) = verify_host_range_with(
                    &env_inc,
                    env_inc.preverified_prefix,
                    Some(4),
                    VerifyOptions::default(),
                );
                assert!(matches!(v_inc, VerificationVerdict::Accepted { .. }), "{v_inc:?}");
                assert_eq!(tel.checked_count, env_inc.decls.len() - env_inc.preverified_prefix);

                // Changing a single byte in cached base module hash invalidates prefix skipping.
                let mut tampered_base = env_base;
                if let Some((_, h)) = tampered_base.module_hashes.iter_mut().next() {
                    h[0] ^= 1;
                }
                let env_tampered = load_environment_from_prefix(&core_spec, &tampered_base, Some(&cfs))
                    .expect("Core tampered");
                assert!(env_tampered.preverified_prefix < env_inc.preverified_prefix);
            })
            .expect("spawn")
            .join()
            .expect("join");
    }
}
