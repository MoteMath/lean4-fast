use std::sync::{Mutex, OnceLock};
use std::time::Instant;

use con_gpu_arena::loader::{LoadedEnvironment, VerificationVerdict};
use con_gpu_arena::soa_pack::{
    ArenaHeader, GpuArenaPacket, GpuJob, GpuVerdict, E_NODES_NUM_PAGES, E_NODES_PAGE_WORDS,
    JOB_FLAG_ELIGIBLE, STATUS_DELEGATE, STATUS_REJECTED_GPU, STATUS_VERIFIED_GPU,
};
use con_gpu_arena::verify_host::{
    verify_delegated_exact_with, verify_host_range_with, HostExactRunner, VerifyOptions,
};

use crate::device::GpuContext;

enum ArenaSlice<'a> {
    Borrowed(&'a [u32]),
    Owned(Vec<u32>),
}

impl<'a> ArenaSlice<'a> {
    fn as_slice(&self) -> &[u32] {
        match self {
            Self::Borrowed(s) => s,
            Self::Owned(v) => v,
        }
    }

    fn release(&mut self) {
        if let Self::Owned(v) = self {
            *v = Vec::new();
        }
    }
}

pub const TYPECHECK_SHADER_WGSL: &str = include_str!("wgsl/typecheck_arena.wgsl");
pub const TYPECHECK_COMPACT_WGSL: &str = concat!(
    include_str!("wgsl/typecheck_arena.wgsl"),
    "\n",
    include_str!("wgsl/typecheck_compact.wgsl"),
);
pub const TYPECHECK_FUSED_WGSL: &str = concat!(
    include_str!("wgsl/typecheck_arena.wgsl"),
    "\n",
    include_str!("wgsl/typecheck_level.wgsl"),
    "\n",
    include_str!("wgsl/typecheck_whnf.wgsl"),
    "\n",
    include_str!("wgsl/typecheck_defeq.wgsl"),
    "\n",
    include_str!("wgsl/typecheck_infer.wgsl"),
    "\n",
    include_str!("wgsl/typecheck_fused.wgsl"),
);

const REASON_STEP_BUDGET: u32 = 3;
const REASON_STACK_BUDGET: u32 = 4;
const REASON_SCRATCH_BUDGET: u32 = 5;
const STATUS_STOLEN_T2: u32 = 99;

const SCRATCH_ALLOC_START: u32 = 4_896;

const TIER1_MAX_WGS: u32 = 1_024;
const TIER1_MAX_STEPS: u32 = 131_072;
const TIER1_MAX_STACK_FRAMES: u32 = 256;
const TIER1_MAX_SCRATCH_WORDS: u32 = SCRATCH_ALLOC_START + 16_384;

const TIER2_MAX_WGS: u32 = 124;
const TIER2_MAX_STEPS: u32 = 131_072;
const TIER2_MAX_STACK_FRAMES: u32 = 512;
const TIER2_MAX_SCRATCH_WORDS: u32 = 65_536;

#[cfg(target_os = "windows")]
const QUANTUM_STEPS: u32 = 16_384;
#[cfg(not(target_os = "windows"))]
const QUANTUM_STEPS: u32 = 65_536;

#[cfg(target_os = "windows")]
const TIER2_QUANTUM_STEPS: u32 = 8_192;
#[cfg(not(target_os = "windows"))]
const TIER2_QUANTUM_STEPS: u32 = 32_768;

const MIN_ADAPTIVE_QUANTUM_STEPS: u32 = 2_048;

pub fn typecheck_reason_str(code: u32) -> &'static str {
    match code {
        0 => "ok",
        1 => "not_eligible",
        2 => "unmodeled",
        3 => "step_budget",
        4 => "stack_budget",
        5 => "scratch_budget",
        10 => "duplicate declaration",
        11 => "duplicate universe parameter",
        12 => "loose bound variable",
        13 => "unexpected free variable",
        14 => "undeclared universe parameter",
        15 => "unresolved constant",
        16 => "expected Sort",
        17 => "theorem type must be Prop",
        18 => "definition/theorem value type mismatch",
        19 => "application head is not a function type",
        20 => "application argument type mismatch",
        21 => "invalid projection",
        22 => "loose bound variable in infer",
        23 => "literal type constant not stored in environment",
        _ => "unknown reason",
    }
}

#[derive(Clone, Debug)]
pub struct GpuVerifyReport {
    pub verdict: VerificationVerdict,
    pub total_decls: usize,
    pub eligible_jobs_count: usize,
    pub gpu_verified_count: usize,
    pub gpu_rejected_count: usize,
    pub delegated_count: usize,
    pub host_verified_delegated: usize,
    pub tier2_promoted_count: usize,
    pub pcie_upload_ns: u128,
    pub gpu_kernel_ns: u128,
    pub max_quantum_ns: u128,
    pub gpu_readback_ns: u128,
    pub host_fallback_ns: u128,
    pub total_steps_gpu: u64,
    pub max_scratch_words_used: u32,
    pub delegate_reasons: [u64; 8],
    pub first_gpu_reject: Option<(usize, String, u32)>,
}

#[derive(Clone, Copy)]
struct TierConfig {
    label: &'static str,
    max_wgs: u32,
    max_steps: u32,
    max_stack_frames: u32,
    max_scratch_words: u32,
    quantum_steps: u32,
}

const TIER1_CFG: TierConfig = TierConfig {
    label: "tier1",
    max_wgs: TIER1_MAX_WGS,
    max_steps: TIER1_MAX_STEPS,
    max_stack_frames: TIER1_MAX_STACK_FRAMES,
    max_scratch_words: TIER1_MAX_SCRATCH_WORDS,
    quantum_steps: QUANTUM_STEPS,
};

const TIER2_CFG: TierConfig = TierConfig {
    label: "tier2",
    max_wgs: TIER2_MAX_WGS,
    max_steps: TIER2_MAX_STEPS,
    max_stack_frames: TIER2_MAX_STACK_FRAMES,
    max_scratch_words: TIER2_MAX_SCRATCH_WORDS,
    quantum_steps: TIER2_QUANTUM_STEPS,
};

struct CachedTierBuffers {
    scratch_buf: wgpu::Buffer,
    scratch_cap_bytes: u64,
    active_a: wgpu::Buffer,
    active_b: wgpu::Buffer,
    active_cap_bytes: u64,
    ctl_buf: wgpu::Buffer,
    ctl_staging: wgpu::Buffer,
    hdr_buf: wgpu::Buffer,
    next_epoch: std::cell::Cell<u32>,
    needs_clear: std::cell::Cell<bool>,
}

impl CachedTierBuffers {
    fn alloc_epoch(&self) -> u32 {
        let ep = self.next_epoch.get();
        let next = ep.wrapping_add(1);
        if next == 0 {
            self.next_epoch.set(1);
            self.needs_clear.set(true);
        } else {
            self.next_epoch.set(next);
        }
        ep
    }
}

#[derive(Default)]
struct TierBufferCache {
    tier1: Option<CachedTierBuffers>,
    tier2: Option<CachedTierBuffers>,
}

struct VmPipelineSet {
    p_infer: wgpu::ComputePipeline,
    p_whnf: wgpu::ComputePipeline,
    p_defeq: wgpu::ComputePipeline,
    p_level: wgpu::ComputePipeline,
    p_subst: wgpu::ComputePipeline,
    p_compact: wgpu::ComputePipeline,
}

pub struct TypecheckGpuPipeline {
    vm_1gb: VmPipelineSet,
    vm_paged: OnceLock<VmPipelineSet>,
    bgl: wgpu::BindGroupLayout,
    pl: wgpu::PipelineLayout,
    pool: Mutex<TierBufferCache>,
}

fn ensure_tier_buffers<'a>(
    ctx: &GpuContext,
    slot: &'a mut Option<CachedTierBuffers>,
    label: &str,
    needed_scratch_bytes: u64,
    needed_active_bytes: u64,
) -> &'a CachedTierBuffers {
    let realloc = match slot {
        Some(bufs) => {
            bufs.scratch_cap_bytes < needed_scratch_bytes
                || bufs.active_cap_bytes < needed_active_bytes
        }
        None => true,
    };

    if realloc {
        let scratch_cap_bytes = needed_scratch_bytes.max(64);
        let active_cap_bytes = needed_active_bytes.max(8);
        let scratch_buf = ctx.create_storage_buffer_zeroed(
            &format!("tc-{label}-scratch"),
            scratch_cap_bytes,
            wgpu::BufferUsages::COPY_DST,
        );
        let active_a = ctx.create_storage_buffer_zeroed(
            &format!("tc-{label}-active-a"),
            active_cap_bytes,
            wgpu::BufferUsages::COPY_DST,
        );
        let active_b = ctx.create_storage_buffer_zeroed(
            &format!("tc-{label}-active-b"),
            active_cap_bytes,
            wgpu::BufferUsages::COPY_DST,
        );
        let ctl_buf = ctx.create_storage_buffer_zeroed(
            &format!("tc-{label}-ctl"),
            16,
            wgpu::BufferUsages::COPY_SRC | wgpu::BufferUsages::COPY_DST,
        );
        let ctl_staging = ctx.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(&format!("tc-{label}-ctl-staging")),
            size: 4,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        let hdr_buf = ctx.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(&format!("tc-{label}-hdr")),
            size: std::mem::size_of::<con_gpu_arena::soa_pack::ArenaHeader>() as u64,
            usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });
        *slot = Some(CachedTierBuffers {
            scratch_buf,
            scratch_cap_bytes,
            active_a,
            active_b,
            active_cap_bytes,
            ctl_buf,
            ctl_staging,
            hdr_buf,
            next_epoch: std::cell::Cell::new(1),
            needs_clear: std::cell::Cell::new(false),
        });
    }

    slot.as_ref().expect("tier buffers allocated")
}

fn earliest_verdict(
    a: Result<(), VerificationVerdict>,
    b: Result<(), VerificationVerdict>,
) -> Result<(), VerificationVerdict> {
    match (a, b) {
        (Ok(()), Ok(())) => Ok(()),
        (Err(va), Ok(())) => Err(va),
        (Ok(()), Err(vb)) => Err(vb),
        (Err(va), Err(vb)) => {
            let pa = va.failure_pos().unwrap_or(u64::MAX);
            let pb = vb.failure_pos().unwrap_or(u64::MAX);
            if pa <= pb {
                Err(va)
            } else {
                Err(vb)
            }
        }
    }
}

impl TypecheckGpuPipeline {
    pub fn make_bgl(ctx: &GpuContext) -> wgpu::BindGroupLayout {
        let ro_storage = |binding: u32| wgpu::BindGroupLayoutEntry {
            binding,
            visibility: wgpu::ShaderStages::COMPUTE,
            ty: wgpu::BindingType::Buffer {
                ty: wgpu::BufferBindingType::Storage { read_only: true },
                has_dynamic_offset: false,
                min_binding_size: None,
            },
            count: None,
        };
        let rw_storage = |binding: u32| wgpu::BindGroupLayoutEntry {
            binding,
            visibility: wgpu::ShaderStages::COMPUTE,
            ty: wgpu::BindingType::Buffer {
                ty: wgpu::BufferBindingType::Storage { read_only: false },
                has_dynamic_offset: false,
                min_binding_size: None,
            },
            count: None,
        };

        ctx.device
            .create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("typecheck-fused-bgl"),
                entries: &[
                    wgpu::BindGroupLayoutEntry {
                        binding: 0,
                        visibility: wgpu::ShaderStages::COMPUTE,
                        ty: wgpu::BindingType::Buffer {
                            ty: wgpu::BufferBindingType::Uniform,
                            has_dynamic_offset: false,
                            min_binding_size: None,
                        },
                        count: None,
                    },
                    ro_storage(1),
                    ro_storage(2),
                    ro_storage(3),
                    ro_storage(4),
                    rw_storage(5),
                    rw_storage(6),
                    rw_storage(7),
                    ro_storage(8),
                    rw_storage(9),
                    ro_storage(10),
                    ro_storage(11),
                    ro_storage(12),
                    ro_storage(13),
                    ro_storage(14),
                    ro_storage(15),
                    ro_storage(16),
                ],
            })
    }

    fn make_vm_wgsl(k_id: u32, op_cases: &str, paged: bool) -> String {
        let base = TYPECHECK_FUSED_WGSL
            .replace(
                "const VM_MY_K: u32 = 0u;",
                &format!("const VM_MY_K: u32 = {k_id}u;"),
            )
            .replace("// __OP_CASES__", op_cases);
        if paged {
            base
        } else {
            base.replace("const E_NODES_PAGED: bool = true;", "const E_NODES_PAGED: bool = false;")
        }
    }

    fn fnv1a_64_bundle(parts: &[&[u8]]) -> u64 {
        let mut h: u64 = 0xcbf2_9ce4_8422_2325;
        for part in parts {
            for &b in *part {
                h ^= b as u64;
                h = h.wrapping_mul(0x0000_0100_0000_01b3);
            }
            h ^= 0xff;
            h = h.wrapping_mul(0x0000_0100_0000_01b3);
        }
        h
    }

    fn pipeline_cache_path(ctx: &GpuContext, paged: bool) -> Option<std::path::PathBuf> {
        let key = wgpu::util::pipeline_cache_key(&ctx.adapter.get_info())?;
        let tag = if paged { b"paged8".as_slice() } else { b"fast1g".as_slice() };
        let bundle_hash = Self::fnv1a_64_bundle(&[
            TYPECHECK_FUSED_WGSL.as_bytes(),
            TYPECHECK_COMPACT_WGSL.as_bytes(),
            std::env::consts::ARCH.as_bytes(),
            key.as_bytes(),
            tag,
        ]);
        let dir = std::env::var_os("LOCALAPPDATA")
            .map(std::path::PathBuf::from)
            .unwrap_or_else(std::env::temp_dir)
            .join("con-gpu")
            .join("vk_cache");
        Some(dir.join(format!("{key}_{bundle_hash:016x}.bin")))
    }

    fn compile_vm_set(ctx: &GpuContext, pl: &wgpu::PipelineLayout, paged: bool) -> VmPipelineSet {
        let trace = std::env::var_os("CON_GPU_TRACE").is_some();
        let t0 = Instant::now();
        let supports_pcache = ctx.device.features().contains(wgpu::Features::PIPELINE_CACHE);
        let cache_path = if supports_pcache {
            Self::pipeline_cache_path(ctx, paged)
        } else {
            None
        };
        let cached_bytes = cache_path.as_ref().and_then(|p| std::fs::read(p).ok());
        let pipe_cache = if supports_pcache {
            Some(unsafe {
                ctx.device.create_pipeline_cache(&wgpu::PipelineCacheDescriptor {
                    label: Some(if paged {
                        "con-gpu-tc-pipeline-cache-paged8"
                    } else {
                        "con-gpu-tc-pipeline-cache"
                    }),
                    data: cached_bytes.as_deref(),
                    fallback: true,
                })
            })
        } else {
            None
        };

        let infer_src = Self::make_vm_wgsl(
            1,
            "case OP_JOB_FINISH: { exec_job_finish(top); }\n            case OP_INFER, OP_INFER_IO: { exec_infer(top, op == OP_INFER_IO); }",
            paged,
        );
        let whnf_src = Self::make_vm_wgsl(
            2,
            "case OP_WHNF: { exec_whnf(top); }\n            case OP_WHNF_CORE: { exec_whnf_core(top); }",
            paged,
        );
        let defeq_src = Self::make_vm_wgsl(
            3,
            "case OP_DEFEQ: { exec_defeq(top); }\n            case OP_DEFEQ_LAM_CHAIN: { exec_defeq_bind_chain(top, ETAG_LAM); }\n            case OP_DEFEQ_FORALL_CHAIN: { exec_defeq_bind_chain(top, ETAG_FORALL_E); }\n            case OP_DEFEQ_SPINE: { exec_defeq_spine(top); }\n            case OP_DEFEQ_STRUCT_ETA: { exec_defeq_struct_eta(top); }",
            paged,
        );
        let level_src = Self::make_vm_wgsl(
            4,
            "case OP_LEVEL_CMP: { exec_level_cmp(top); }",
            paged,
        );
        let subst_src = Self::make_vm_wgsl(
            5,
            "case OP_INST_LP, OP_INST_REV, OP_ABS_RANGE: { exec_subst(top, op); }",
            paged,
        );

        let compile_one = |label: &str, wgsl: &str| -> wgpu::ComputePipeline {
            let tk = Instant::now();
            let shader = ctx.device.create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some(label),
                source: wgpu::ShaderSource::Wgsl(wgsl.into()),
            });
            let p = ctx.device.create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some(label),
                layout: Some(pl),
                module: &shader,
                entry_point: Some("main"),
                compilation_options: wgpu::PipelineCompilationOptions {
                    zero_initialize_workgroup_memory: false,
                    ..Default::default()
                },
                cache: pipe_cache.as_ref(),
            });
            if trace {
                eprintln!(
                    "[TRACE] compiled {label} (paged={paged}) in {} ms",
                    tk.elapsed().as_millis()
                );
            }
            p
        };

        if trace {
            eprintln!(
                "[TRACE] compiling 6 parallel VM pipelines (paged={paged}, pcache={supports_pcache}, hit={})...",
                cached_bytes.is_some()
            );
        }

        let (p_infer, p_whnf, p_defeq, p_level, p_subst, p_compact) = std::thread::scope(|s| {
            let h_infer = s.spawn(|| compile_one("tc-infer", &infer_src));
            let h_whnf = s.spawn(|| compile_one("tc-whnf", &whnf_src));
            let h_defeq = s.spawn(|| compile_one("tc-defeq", &defeq_src));
            let h_level = s.spawn(|| compile_one("tc-level", &level_src));
            let h_subst = s.spawn(|| compile_one("tc-subst", &subst_src));
            let p_compact = compile_one("tc-compact", TYPECHECK_COMPACT_WGSL);
            (
                h_infer.join().expect("tc-infer compile panic"),
                h_whnf.join().expect("tc-whnf compile panic"),
                h_defeq.join().expect("tc-defeq compile panic"),
                h_level.join().expect("tc-level compile panic"),
                h_subst.join().expect("tc-subst compile panic"),
                p_compact,
            )
        });

        if let (Some(c), Some(path)) = (pipe_cache.as_ref(), cache_path.as_ref()) {
            if let Some(bytes) = c.get_data() {
                if let Some(parent) = path.parent() {
                    let _ = std::fs::create_dir_all(parent);
                }
                let tmp = path.with_extension(format!("tmp.{}", std::process::id()));
                if std::fs::write(&tmp, &bytes).is_ok() {
                    let _ = std::fs::rename(&tmp, path);
                }
            }
        }

        if trace {
            eprintln!(
                "[TRACE] all 6 compute pipelines ready (paged={paged}) in {} ms total",
                t0.elapsed().as_millis()
            );
        }

        VmPipelineSet {
            p_infer,
            p_whnf,
            p_defeq,
            p_level,
            p_subst,
            p_compact,
        }
    }

    pub fn new(ctx: &GpuContext) -> Self {
        let bgl = Self::make_bgl(ctx);
        let pl = ctx
            .device
            .create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("typecheck-fused-pl"),
                bind_group_layouts: &[Some(&bgl)],
                immediate_size: 0,
            });
        let vm_1gb = Self::compile_vm_set(ctx, &pl, false);
        Self {
            vm_1gb,
            vm_paged: OnceLock::new(),
            bgl,
            pl,
            pool: Mutex::new(TierBufferCache::default()),
        }
    }

    fn vm_for_len(&self, ctx: &GpuContext, e_nodes_len: usize) -> &VmPipelineSet {
        if e_nodes_len > E_NODES_PAGE_WORDS {
            self.vm_paged
                .get_or_init(|| Self::compile_vm_set(ctx, &self.pl, true))
        } else {
            &self.vm_1gb
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn run_tier_with<C, F>(
        &self,
        ctx: &GpuContext,
        slot: &mut Option<CachedTierBuffers>,
        tier: TierConfig,
        pkt_header: &ArenaHeader,
        pkt_jobs: &[GpuJob],
        e_nodes_len: usize,
        e_nodes_pages: &[wgpu::Buffer; E_NODES_NUM_PAGES],
        meta_nodes_buf: &wgpu::Buffer,
        env_tables_buf: &wgpu::Buffer,
        jobs_buf: &wgpu::Buffer,
        verdicts_buf: &wgpu::Buffer,
        target_job_indices: &[u32],
        max_binding_bytes: u64,
        tail_cutoff: bool,
        hybrid_large: bool,
        max_quantum_ns: &mut u128,
        gpu_kernel_ns: &mut u128,
        mut next_chunk: C,
        mut on_chunk_done: F,
    ) -> Result<(), String>
    where
        C: FnMut(usize) -> Option<(usize, usize)>,
        F: FnMut(&[u32], bool) -> Result<(), String>,
    {
        if target_job_indices.is_empty() {
            return Ok(());
        }

        let wg_size = pkt_header.wg_size.max(1);
        let wg_stride_words = (tier.max_stack_frames * 8 + tier.max_scratch_words) * wg_size;
        let wg_stride_bytes = (wg_stride_words as u64) * 4;
        let max_wgs_by_limit = (max_binding_bytes / wg_stride_bytes.max(1)).max(1) as u32;
        let wgs_cap = max_wgs_by_limit.min(tier.max_wgs).max(1);
        let chunk_jobs_cap = (wgs_cap * wg_size) as usize;

        let max_chunk_jobs = target_job_indices.len().min(chunk_jobs_cap);
        let actual_wgs_needed = (((max_chunk_jobs as u32) + wg_size - 1) / wg_size).max(1);
        let needed_scratch_bytes = (actual_wgs_needed as u64) * wg_stride_bytes.max(64);
        let needed_active_bytes = (max_chunk_jobs as u64) * 8;

        let work = ensure_tier_buffers(
            ctx,
            slot,
            tier.label,
            needed_scratch_bytes,
            needed_active_bytes,
        );

        let make_bg = |in_buf: &wgpu::Buffer, out_buf: &wgpu::Buffer, tag: &str| {
            ctx.device.create_bind_group(&wgpu::BindGroupDescriptor {
                label: Some(tag),
                layout: &self.bgl,
                entries: &[
                    wgpu::BindGroupEntry {
                        binding: 0,
                        resource: work.hdr_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 1,
                        resource: e_nodes_pages[0].as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 2,
                        resource: meta_nodes_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 3,
                        resource: env_tables_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 4,
                        resource: jobs_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 5,
                        resource: work.scratch_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 6,
                        resource: verdicts_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 7,
                        resource: work.ctl_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 8,
                        resource: in_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 9,
                        resource: out_buf.as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 10,
                        resource: e_nodes_pages[1].as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 11,
                        resource: e_nodes_pages[2].as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 12,
                        resource: e_nodes_pages[3].as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 13,
                        resource: e_nodes_pages[4].as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 14,
                        resource: e_nodes_pages[5].as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 15,
                        resource: e_nodes_pages[6].as_entire_binding(),
                    },
                    wgpu::BindGroupEntry {
                        binding: 16,
                        resource: e_nodes_pages[7].as_entire_binding(),
                    },
                ],
            })
        };

        let bg_a_to_b = make_bg(&work.active_a, &work.active_b, "tc-bg-ab");
        let bg_b_to_a = make_bg(&work.active_b, &work.active_a, "tc-bg-ba");

        let mut tier_hdr = *pkt_header;
        tier_hdr.max_steps = tier.max_steps;
        tier_hdr.max_stack_frames = tier.max_stack_frames;
        tier_hdr.max_scratch_words = tier.max_scratch_words;
        tier_hdr.scratch_wg_stride = wg_stride_words;
        tier_hdr.wg_size = wg_size;

        let max_quanta = ((tier.max_steps + 15) / 16).max(512);
        let mut cur_q_steps = tier.quantum_steps;
        let mut need_clear_scratch = true;
        let mut init_pairs: Vec<[u32; 2]> = Vec::with_capacity(max_chunk_jobs);
        let trace = std::env::var_os("CON_GPU_TRACE").is_some();

        let dispatch_pass = |encoder: &mut wgpu::CommandEncoder,
                             pipe: &wgpu::ComputePipeline,
                             bg: &wgpu::BindGroup,
                             wgs: u32,
                             label: &str| {
            let mut cpass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some(label),
                timestamp_writes: None,
            });
            cpass.set_pipeline(pipe);
            cpass.set_bind_group(0, bg, &[]);
            cpass.dispatch_workgroups(wgs, 1, 1);
        };

        while let Some((start, end)) = next_chunk(chunk_jobs_cap) {
            if start >= end {
                continue;
            }
            let chunk = &target_job_indices[start..end];
            let t_chunk_k = Instant::now();
            let chunk_min_bucket = pkt_jobs[chunk[0] as usize].ast_bucket;
            let chunk_max_quanta = if tail_cutoff && hybrid_large && chunk_min_bucket >= 12 {
                1u32.min(max_quanta)
            } else if tail_cutoff && hybrid_large && chunk_min_bucket >= 8 {
                4u32.min(max_quanta)
            } else {
                max_quanta
            };
            tier_hdr.max_steps = if tail_cutoff && hybrid_large && chunk_min_bucket >= 12 {
                tier.max_steps.min(16_384)
            } else if tail_cutoff && hybrid_large && chunk_min_bucket >= 9 {
                tier.max_steps.min(32_768)
            } else if tail_cutoff && hybrid_large && chunk_min_bucket >= 8 {
                tier.max_steps.min(65_536)
            } else {
                tier.max_steps
            };
            tier_hdr.job_offset = 0;
            tier_hdr.num_jobs = chunk.len() as u32;
            tier_hdr.batch_epoch = work.alloc_epoch();
            ctx.queue
                .write_buffer(&work.hdr_buf, 0, bytemuck::bytes_of(&tier_hdr));

            init_pairs.clear();
            for (slot_idx, &job_idx) in chunk.iter().enumerate() {
                init_pairs.push([job_idx, slot_idx as u32]);
            }
            ctx.queue
                .write_buffer(&work.active_a, 0, bytemuck::cast_slice(&init_pairs));

            let mut in_count = chunk.len() as u32;
            let mut ping = false;
            if trace {
                eprintln!(
                    "[TRACE] {} chunk offset={} len={} bucket>={} max_q={} max_steps={} epoch={}",
                    tier.label,
                    start,
                    chunk.len(),
                    chunk_min_bucket,
                    chunk_max_quanta,
                    tier_hdr.max_steps,
                    tier_hdr.batch_epoch
                );
            }

            let mut did_cutoff = false;
            for q in 0..chunk_max_quanta {
                let ctl_words: [u32; 4] = [
                    in_count,
                    0u32,
                    q + 1,
                    cur_q_steps,
                ];
                ctx.queue
                    .write_buffer(&work.ctl_buf, 0, bytemuck::cast_slice(&ctl_words));

                let wgs = (in_count + wg_size - 1) / wg_size;
                let bg = if !ping { &bg_a_to_b } else { &bg_b_to_a };
                let rounds = if hybrid_large {
                    if in_count <= 128 {
                        48u32
                    } else if in_count <= 512 {
                        32u32
                    } else {
                        24u32
                    }
                } else if in_count <= 64 {
                    96u32
                } else if in_count <= 256 {
                    48u32
                } else if in_count <= 2048 {
                    24u32
                } else {
                    12u32
                };

                let t_q = Instant::now();
                let mut encoder =
                    ctx.device
                        .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                            label: Some("typecheck-fused-enc"),
                        });
                if q == 0 && (need_clear_scratch || work.needs_clear.get()) {
                    encoder.clear_buffer(&work.scratch_buf, 0, None);
                    need_clear_scratch = false;
                    work.needs_clear.set(false);
                }
                let vm = self.vm_for_len(ctx, e_nodes_len);
                for r in 0..rounds {
                    dispatch_pass(&mut encoder, &vm.p_infer, bg, wgs, "tc-infer-pass");
                    dispatch_pass(&mut encoder, &vm.p_subst, bg, wgs, "tc-subst-pass");
                    dispatch_pass(&mut encoder, &vm.p_whnf, bg, wgs, "tc-whnf-pass");
                    dispatch_pass(&mut encoder, &vm.p_subst, bg, wgs, "tc-subst-pass");
                    dispatch_pass(&mut encoder, &vm.p_defeq, bg, wgs, "tc-defeq-pass");
                    if (r & 1) == 1 || r + 1 == rounds {
                        dispatch_pass(&mut encoder, &vm.p_level, bg, wgs, "tc-level-pass");
                    }
                }
                dispatch_pass(&mut encoder, &vm.p_compact, bg, wgs, "tc-compact-pass");
                encoder.copy_buffer_to_buffer(&work.ctl_buf, 4, &work.ctl_staging, 0, 4);
                ctx.queue.submit(Some(encoder.finish()));

                let slice = work.ctl_staging.slice(..4);
                let (tx, rx) = std::sync::mpsc::sync_channel(1);
                slice.map_async(wgpu::MapMode::Read, move |res| {
                    let _ = tx.send(res);
                });
                ctx.wait_idle();
                rx.recv()
                    .map_err(|e| format!("GPU ctl readback channel closed: {e}"))?
                    .map_err(|e| format!("GPU ctl staging map_async failed: {e}"))?;

                let out_count = {
                    let data = slice
                        .get_mapped_range()
                        .map_err(|e| format!("GPU ctl get_mapped_range failed: {e}"))?;
                    *bytemuck::from_bytes::<u32>(&data[..4])
                };
                work.ctl_staging.unmap();
                let q_ns = t_q.elapsed().as_nanos();
                if trace {
                    eprintln!(
                        "[TRACE]   {} q={} in={} wgs={} out={} q_steps={} ms={}",
                        tier.label,
                        q,
                        in_count,
                        wgs,
                        out_count,
                        cur_q_steps,
                        q_ns / 1_000_000
                    );
                }
                if q_ns > *max_quantum_ns {
                    *max_quantum_ns = q_ns;
                }
                if cfg!(target_os = "windows")
                    && q_ns > 800_000_000
                    && cur_q_steps > MIN_ADAPTIVE_QUANTUM_STEPS
                {
                    cur_q_steps = (cur_q_steps / 2).max(MIN_ADAPTIVE_QUANTUM_STEPS);
                }

                if out_count == 0 {
                    break;
                }
                let hit_cutoff = if hybrid_large {
                    if tail_cutoff {
                        if chunk_min_bucket >= 12 {
                            (q + 1 >= chunk_max_quanta)
                                || (out_count > ((chunk.len() as u32) * 63) / 64)
                        } else if chunk_min_bucket >= 8 {
                            (q + 1 >= chunk_max_quanta)
                                || (q >= 1 && out_count > ((chunk.len() as u32) * 63) / 64)
                        } else {
                            (q >= 3 && out_count <= 64)
                                || (q >= 7 && out_count > ((chunk.len() as u32) * 15) / 16)
                                || (q >= 15 && out_count > ((chunk.len() as u32) * 3) / 4)
                                || (q >= 18 && out_count <= 2_560)
                                || q >= 23
                        }
                    } else {
                        (chunk.len() >= 256 && q >= 2 && out_count <= 64)
                            || (q >= 8 && out_count <= 128)
                            || q >= 23
                    }
                } else {
                    (tail_cutoff && chunk.len() >= 2048 && q >= 1 && out_count <= 256)
                        || (!tail_cutoff && chunk.len() >= 128 && q >= 2 && out_count <= 64)
                };
                if hit_cutoff {
                    did_cutoff = true;
                    if trace {
                        eprintln!(
                            "[TRACE]   {} tail_cutoff at q={} out={} (chunk len={})",
                            tier.label,
                            q,
                            out_count,
                            chunk.len()
                        );
                    }
                    break;
                }
                in_count = out_count;
                ping = !ping;
            }
            *gpu_kernel_ns += t_chunk_k.elapsed().as_nanos();
            on_chunk_done(chunk, did_cutoff)?;
        }

        Ok(())
    }

    pub fn verify_packet_hybrid(
        &self,
        ctx: &GpuContext,
        env: &LoadedEnvironment,
        pkt: &GpuArenaPacket,
        host_threads: Option<usize>,
    ) -> Result<GpuVerifyReport, String> {
        self.verify_packet_hybrid_with(ctx, env, pkt, host_threads, VerifyOptions::default())
    }

    pub fn verify_packet_hybrid_with(
        &self,
        ctx: &GpuContext,
        env: &LoadedEnvironment,
        pkt: &GpuArenaPacket,
        host_threads: Option<usize>,
        opts: VerifyOptions,
    ) -> Result<GpuVerifyReport, String> {
        self.verify_packet_hybrid_range_with(ctx, env, pkt, host_threads, 0, opts)
    }

    pub fn verify_packet_hybrid_range_with(
        &self,
        ctx: &GpuContext,
        env: &LoadedEnvironment,
        pkt: &GpuArenaPacket,
        host_threads: Option<usize>,
        skip_prefix_len: usize,
        opts: VerifyOptions,
    ) -> Result<GpuVerifyReport, String> {
        let no_lazy: Option<fn() -> Result<LoadedEnvironment, VerificationVerdict>> = None;
        self.verify_packet_hybrid_core(
            ctx,
            Some(env),
            pkt.header,
            &pkt.jobs,
            pkt.eligible_jobs_count,
            ArenaSlice::Borrowed(&pkt.e_nodes),
            ArenaSlice::Borrowed(&pkt.meta_nodes),
            ArenaSlice::Borrowed(&pkt.env_tables),
            env.file_records,
            host_threads,
            skip_prefix_len,
            opts,
            true,
            no_lazy,
        )
    }

    /// Execute full-depth GPU verification (`--backend gpu`) without aggressive hybrid early cutoffs,
    /// retaining exact host fallback only for unmodeled/delegated/overflow declarations.
    pub fn verify_packet_gpu_range_with(
        &self,
        ctx: &GpuContext,
        env: &LoadedEnvironment,
        pkt: &GpuArenaPacket,
        host_threads: Option<usize>,
        skip_prefix_len: usize,
        opts: VerifyOptions,
    ) -> Result<GpuVerifyReport, String> {
        let no_lazy: Option<fn() -> Result<LoadedEnvironment, VerificationVerdict>> = None;
        self.verify_packet_hybrid_core(
            ctx,
            Some(env),
            pkt.header,
            &pkt.jobs,
            pkt.eligible_jobs_count,
            ArenaSlice::Borrowed(&pkt.e_nodes),
            ArenaSlice::Borrowed(&pkt.meta_nodes),
            ArenaSlice::Borrowed(&pkt.env_tables),
            env.file_records,
            host_threads,
            skip_prefix_len,
            opts,
            false,
            no_lazy,
        )
    }

    /// Execute hybrid GPU + exact CPU verification from a pre-packed `GpuArenaPacket` snapshot
    /// without eagerly constructing a `LoadedEnvironment`.
    ///
    /// - If `pkt` has non-eligible declarations (`non_eligible_orig`), `lazy_loader` runs
    ///   concurrently on the CPU worker thread while the GPU uploads and checks `eligible` jobs.
    /// - If every declaration in `pkt` is GPU-eligible and GPU verifies 100% of them with 0
    ///   delegations and 0 rejections, `lazy_loader` is never invoked at all.
    pub fn verify_snapshot_hybrid_with<F>(
        &self,
        ctx: &GpuContext,
        pkt: &GpuArenaPacket,
        file_records: usize,
        host_threads: Option<usize>,
        skip_prefix_len: usize,
        opts: VerifyOptions,
        lazy_loader: F,
    ) -> Result<GpuVerifyReport, String>
    where
        F: FnOnce() -> Result<LoadedEnvironment, VerificationVerdict> + Send,
    {
        self.verify_packet_hybrid_core(
            ctx,
            None,
            pkt.header,
            &pkt.jobs,
            pkt.eligible_jobs_count,
            ArenaSlice::Borrowed(&pkt.e_nodes),
            ArenaSlice::Borrowed(&pkt.meta_nodes),
            ArenaSlice::Borrowed(&pkt.env_tables),
            file_records,
            host_threads,
            skip_prefix_len,
            opts,
            true,
            Some(lazy_loader),
        )
    }

    /// Owning variant of [`Self::verify_snapshot_hybrid_with`] that frees `pkt.e_nodes`,
    /// `pkt.meta_nodes`, and `pkt.env_tables` immediately after PCIe upload completes so CPU
    /// host decoding and verification run with full RAM headroom.
    pub fn verify_snapshot_hybrid_owning_with<F>(
        &self,
        ctx: &GpuContext,
        pkt: GpuArenaPacket,
        file_records: usize,
        host_threads: Option<usize>,
        skip_prefix_len: usize,
        opts: VerifyOptions,
        lazy_loader: F,
    ) -> Result<GpuVerifyReport, String>
    where
        F: FnOnce() -> Result<LoadedEnvironment, VerificationVerdict> + Send,
    {
        self.verify_packet_hybrid_core(
            ctx,
            None,
            pkt.header,
            &pkt.jobs,
            pkt.eligible_jobs_count,
            ArenaSlice::Owned(pkt.e_nodes),
            ArenaSlice::Owned(pkt.meta_nodes),
            ArenaSlice::Owned(pkt.env_tables),
            file_records,
            host_threads,
            skip_prefix_len,
            opts,
            true,
            Some(lazy_loader),
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn verify_packet_hybrid_core<F>(
        &self,
        ctx: &GpuContext,
        env_opt: Option<&LoadedEnvironment>,
        pkt_header: ArenaHeader,
        pkt_jobs: &[GpuJob],
        pkt_eligible_jobs_count: usize,
        mut pkt_e_nodes: ArenaSlice<'_>,
        mut pkt_meta_nodes: ArenaSlice<'_>,
        mut pkt_env_tables: ArenaSlice<'_>,
        file_records: usize,
        host_threads: Option<usize>,
        skip_prefix_len: usize,
        opts: VerifyOptions,
        hybrid_mode: bool,
        mut lazy_loader: Option<F>,
    ) -> Result<GpuVerifyReport, String>
    where
        F: FnOnce() -> Result<LoadedEnvironment, VerificationVerdict> + Send,
    {
        let total_decls = env_opt.map(|e| e.decls.len()).unwrap_or(file_records);
        let skip_n = skip_prefix_len.min(total_decls);
        if total_decls == 0 || skip_n == total_decls || pkt_jobs.is_empty() {
            return Ok(GpuVerifyReport {
                verdict: VerificationVerdict::Accepted {
                    file_records,
                    fold_records: file_records,
                },
                total_decls,
                eligible_jobs_count: 0,
                gpu_verified_count: 0,
                gpu_rejected_count: 0,
                delegated_count: 0,
                host_verified_delegated: 0,
                tier2_promoted_count: 0,
                pcie_upload_ns: 0,
                gpu_kernel_ns: 0,
                max_quantum_ns: 0,
                gpu_readback_ns: 0,
                host_fallback_ns: 0,
                total_steps_gpu: 0,
                max_scratch_words_used: 0,
                delegate_reasons: [0; 8],
                first_gpu_reject: None,
            });
        }

        let limits = ctx.device.limits();
        let max_binding_bytes =
            (limits.max_storage_buffer_binding_size as u64).min(limits.max_buffer_size);
        let e_nodes_len = pkt_e_nodes.as_slice().len();
        let max_e_nodes_page_bytes = (0..E_NODES_NUM_PAGES)
            .map(|p| {
                let start = p * E_NODES_PAGE_WORDS;
                if start < e_nodes_len {
                    let end = ((p + 1) * E_NODES_PAGE_WORDS).min(e_nodes_len);
                    ((end - start) as u64) * 4
                } else {
                    4u64
                }
            })
            .max()
            .unwrap_or(4);
        let meta_nodes_bytes_check = (pkt_meta_nodes.as_slice().len().max(1) as u64) * 4;
        let env_tables_bytes_check = (pkt_env_tables.as_slice().len().max(1) as u64) * 4;

        let verdicts_bytes_check = (pkt_jobs.len() as u64) * (std::mem::size_of::<GpuVerdict>() as u64);
        let jobs_bytes_check = (pkt_jobs.len() as u64) * (std::mem::size_of::<GpuJob>() as u64);
        let e_pages_exceed = e_nodes_len > E_NODES_PAGE_WORDS * E_NODES_NUM_PAGES;
        let oversized = if e_pages_exceed {
            Some(("e_nodes_8gb_limit", (e_nodes_len as u64) * 4))
        } else {
            [
                ("e_nodes_page", max_e_nodes_page_bytes),
                ("meta_nodes", meta_nodes_bytes_check),
                ("env_tables", env_tables_bytes_check),
                ("jobs", jobs_bytes_check),
                ("verdicts", verdicts_bytes_check),
            ]
            .into_iter()
            .find(|(_, bytes)| *bytes > max_binding_bytes)
        };
        if let Some((buf_name, buf_bytes)) = oversized {
            pkt_e_nodes.release();
            pkt_meta_nodes.release();
            pkt_env_tables.release();
            if std::env::var_os("CON_GPU_TRACE").is_some() {
                eprintln!(
                    "[TRACE] GPU storage buffer `{buf_name}` ({buf_bytes} B) exceeds max_storage_buffer_binding_size ({max_binding_bytes} B); falling back to exact CPU HostExactRunner"
                );
            }
            let owned_env = match env_opt {
                Some(_) => None,
                None => match lazy_loader.take() {
                    Some(loader) => match loader() {
                        Ok(e) => Some(e),
                        Err(v) => {
                            return Ok(GpuVerifyReport {
                                verdict: v,
                                total_decls,
                                eligible_jobs_count: 0,
                                gpu_verified_count: 0,
                                gpu_rejected_count: 0,
                                delegated_count: total_decls.saturating_sub(skip_n),
                                host_verified_delegated: 0,
                                tier2_promoted_count: 0,
                                pcie_upload_ns: 0,
                                gpu_kernel_ns: 0,
                                max_quantum_ns: 0,
                                gpu_readback_ns: 0,
                                host_fallback_ns: 0,
                                total_steps_gpu: 0,
                                max_scratch_words_used: 0,
                                delegate_reasons: [0; 8],
                                first_gpu_reject: None,
                            });
                        }
                    },
                    None => {
                        return Err(format!(
                            "Arena buffer `{buf_name}` size ({buf_bytes} bytes) exceeds Vulkan max_storage_buffer_binding_size ({max_binding_bytes}) and no host loader was supplied"
                        ));
                    }
                },
            };
            let active_env = env_opt.or(owned_env.as_ref()).expect("env available");
            let t_cpu = Instant::now();
            let (verdict, _) = verify_host_range_with(active_env, skip_n, host_threads, opts);
            let host_ns = t_cpu.elapsed().as_nanos();
            let remaining = total_decls.saturating_sub(skip_n);
            let host_ok = if matches!(verdict, VerificationVerdict::Accepted { .. }) {
                remaining
            } else {
                0
            };
            return Ok(GpuVerifyReport {
                verdict,
                total_decls,
                eligible_jobs_count: pkt_jobs
                    .iter()
                    .filter(|j| (j.orig_decl_idx as usize) >= skip_n && (j.flags & JOB_FLAG_ELIGIBLE) != 0)
                    .count(),
                gpu_verified_count: 0,
                gpu_rejected_count: 0,
                delegated_count: remaining,
                host_verified_delegated: host_ok,
                tier2_promoted_count: 0,
                pcie_upload_ns: 0,
                gpu_kernel_ns: 0,
                max_quantum_ns: 0,
                gpu_readback_ns: 0,
                host_fallback_ns: host_ns,
                total_steps_gpu: 0,
                max_scratch_words_used: 0,
                delegate_reasons: [0; 8],
                first_gpu_reject: None,
            });
        }

        let mut eligible_job_indices: Vec<u32> = Vec::with_capacity(pkt_eligible_jobs_count);
        let mut non_eligible_orig: Vec<usize> =
            Vec::with_capacity(pkt_jobs.len().saturating_sub(pkt_eligible_jobs_count));
        for (job_idx, job) in pkt_jobs.iter().enumerate() {
            if (job.orig_decl_idx as usize) < skip_n {
                continue;
            }
            if (job.flags & JOB_FLAG_ELIGIBLE) != 0 {
                eligible_job_indices.push(job_idx as u32);
            } else {
                non_eligible_orig.push(job.orig_decl_idx as usize);
            }
        }

        if non_eligible_orig.is_empty() && eligible_job_indices.is_empty() {
            return Ok(GpuVerifyReport {
                verdict: VerificationVerdict::Accepted {
                    file_records,
                    fold_records: file_records,
                },
                total_decls,
                eligible_jobs_count: 0,
                gpu_verified_count: 0,
                gpu_rejected_count: 0,
                delegated_count: 0,
                host_verified_delegated: 0,
                tier2_promoted_count: 0,
                pcie_upload_ns: 0,
                gpu_kernel_ns: 0,
                max_quantum_ns: 0,
                gpu_readback_ns: 0,
                host_fallback_ns: 0,
                total_steps_gpu: 0,
                max_scratch_words_used: 0,
                delegate_reasons: [0; 8],
                first_gpu_reject: None,
            });
        }

        let mut pcie_upload_ns = 0u128;
        let mut gpu_kernel_ns = 0u128;
        let mut max_quantum_ns = 0u128;
        let mut gpu_readback_ns = 0u128;
        let mut tier2_promoted_count = 0usize;
        let hybrid_large = hybrid_mode && eligible_job_indices.len() >= 2_048;
        let trace = std::env::var_os("CON_GPU_TRACE").is_some();
        if trace {
            eprintln!(
                "[TRACE] start verify_packet_hybrid eligible={} non_elig={} hybrid_large={}",
                eligible_job_indices.len(),
                non_eligible_orig.len(),
                hybrid_large,
            );
        }

        let non_eligible_count = non_eligible_orig.len();
        let is_snapshot_lazy = env_opt.is_none();
        let frontier = Mutex::new((0usize, eligible_job_indices.len()));
        let t2_pool: Mutex<Vec<u32>> = Mutex::new(Vec::new());
        let t2_frontier: Mutex<(usize, usize)> = Mutex::new((0usize, 0usize));
        let t2_ready = std::sync::atomic::AtomicBool::new(false);
        let gpu_done = std::sync::atomic::AtomicBool::new(false);
        let loader_done = std::sync::atomic::AtomicBool::new(env_opt.is_some());
        let (deleg_tx, deleg_rx) = std::sync::mpsc::channel::<Vec<usize>>();
        let t_scope = Instant::now();
        let loader_for_scope = lazy_loader.take();
        let (
            (mut verdicts, gpu_handled_end),
            (cpu_res, cpu_stolen_count, cpu_end_from_scope_ns, mut lazy_loaded_env, mut unused_loader),
        ) = std::thread::scope(|scope| -> Result<((Vec<GpuVerdict>, usize), _), String> {
                let elig_ref = &eligible_job_indices;
                let frontier_ref = &frontier;
                let t2_pool_ref = &t2_pool;
                let t2_frontier_ref = &t2_frontier;
                let t2_ready_ref = &t2_ready;
                let gpu_done_ref = &gpu_done;
                let loader_done_ref = &loader_done;
                let cpu_handle = std::thread::Builder::new()
                    .name("con-gpu-cpu-worker".to_string())
                    .stack_size(64 * 1024 * 1024)
                    .spawn_scoped(scope, move || {
                    let run_with_env =
                        |active_env: &LoadedEnvironment,
                         first_batch: Vec<usize>,
                         deleg_rx: std::sync::mpsc::Receiver<Vec<usize>>|
                         -> (Result<(), VerificationVerdict>, usize) {
                            let mut initial_batch = first_batch;
                            let mut disconnected = false;
                            loop {
                                match deleg_rx.try_recv() {
                                    Ok(batch) => initial_batch.extend(batch),
                                    Err(std::sync::mpsc::TryRecvError::Empty) => break,
                                    Err(std::sync::mpsc::TryRecvError::Disconnected) => {
                                        disconnected = true;
                                        break;
                                    }
                                }
                            }
                            let t1_exhausted = {
                                let g = frontier_ref.lock().expect("frontier lock");
                                g.0 >= g.1
                            };
                            let t2_exhausted = {
                                let g = t2_frontier_ref.lock().expect("t2 frontier lock");
                                g.0 >= g.1
                            };
                            if gpu_done_ref.load(std::sync::atomic::Ordering::Acquire)
                                || (disconnected && t1_exhausted && t2_exhausted)
                            {
                                while let Ok(batch) = deleg_rx.recv() {
                                    initial_batch.extend(batch);
                                }
                                if initial_batch.len() > 1 {
                                    initial_batch.sort_unstable();
                                }
                                let t_cpu_v = Instant::now();
                                let (res, _) = verify_delegated_exact_with(
                                    active_env,
                                    &initial_batch,
                                    host_threads,
                                    opts,
                                );
                                if trace {
                                    eprintln!(
                                        "[TRACE] cpu verify_delegated_exact_with count={} took={} ms",
                                        initial_batch.len(),
                                        t_cpu_v.elapsed().as_millis()
                                    );
                                }
                                return (res, 0usize);
                            }
                            let runner =
                                match HostExactRunner::new_with(active_env, host_threads, opts) {
                                    Ok(r) => r,
                                    Err(v) => return (Err(v), 0usize),
                                };
                            let mut pending_first = if initial_batch.is_empty() {
                                None
                            } else {
                                Some(initial_batch)
                            };
                            let stolen_atomic = std::sync::atomic::AtomicUsize::new(0);
                            let stolen_ref = &stolen_atomic;
                            let acc_res = runner.run_streaming(move || {
                                if let Some(first) = pending_first.take() {
                                    return Some(first);
                                }

                                let mut coalesced: Vec<usize> = Vec::new();
                                while let Ok(batch) = deleg_rx.try_recv() {
                                    coalesced.extend(batch);
                                }
                                if !coalesced.is_empty() {
                                    return Some(coalesced);
                                }

                                let claimed = {
                                    let mut g = frontier_ref.lock().expect("frontier lock");
                                    let (front, back) = *g;
                                    if front < back && back - front > 64 {
                                        let avail = back - front;
                                        let slice_len = if avail > 12_288 {
                                            1_024
                                        } else if avail > 2_048 {
                                            512
                                        } else if avail > 512 {
                                            256
                                        } else {
                                            64
                                        };
                                        let new_back = back.saturating_sub(slice_len).max(front);
                                        g.1 = new_back;
                                        Some((new_back, back))
                                    } else {
                                        None
                                    }
                                };
                                if let Some((lo, hi)) = claimed {
                                    let batch_orig: Vec<usize> = elig_ref[lo..hi]
                                        .iter()
                                        .map(|&job_idx| {
                                            pkt_jobs[job_idx as usize].orig_decl_idx as usize
                                        })
                                        .collect();
                                    stolen_ref.fetch_add(
                                        batch_orig.len(),
                                        std::sync::atomic::Ordering::Relaxed,
                                    );
                                    if trace {
                                        eprintln!(
                                            "[TRACE] cpu steal [{}..{}) len={} at t={} ms",
                                            lo,
                                            hi,
                                            batch_orig.len(),
                                            t_scope.elapsed().as_millis()
                                        );
                                    }
                                    return Some(batch_orig);
                                }

                                if t2_ready_ref.load(std::sync::atomic::Ordering::Acquire) {
                                    let claimed_t2 = {
                                        let mut g =
                                            t2_frontier_ref.lock().expect("t2 frontier lock");
                                        let (front, back) = *g;
                                        if front < back && back - front > 32 {
                                            let avail = back - front;
                                            let slice_len = if avail > 2_048 {
                                                256
                                            } else if avail > 512 {
                                                64
                                            } else {
                                                16
                                            };
                                            let new_back =
                                                back.saturating_sub(slice_len).max(front);
                                            g.1 = new_back;
                                            Some((new_back, back))
                                        } else {
                                            None
                                        }
                                    };
                                    if let Some((lo, hi)) = claimed_t2 {
                                        let pool_g = t2_pool_ref.lock().expect("t2 pool lock");
                                        let batch_orig: Vec<usize> = pool_g[lo..hi]
                                            .iter()
                                            .map(|&job_idx| {
                                                pkt_jobs[job_idx as usize].orig_decl_idx as usize
                                            })
                                            .collect();
                                        stolen_ref.fetch_add(
                                            batch_orig.len(),
                                            std::sync::atomic::Ordering::Relaxed,
                                        );
                                        if trace {
                                            eprintln!(
                                                "[TRACE] cpu steal tier2 [{}..{}) len={} at t={} ms",
                                                lo,
                                                hi,
                                                batch_orig.len(),
                                                t_scope.elapsed().as_millis()
                                            );
                                        }
                                        return Some(batch_orig);
                                    }
                                }

                                loop {
                                    match deleg_rx.recv() {
                                        Ok(mut first) => {
                                            while let Ok(more) = deleg_rx.try_recv() {
                                                first.extend(more);
                                            }
                                            if !first.is_empty() {
                                                return Some(first);
                                            }
                                            if t2_ready_ref
                                                .load(std::sync::atomic::Ordering::Acquire)
                                            {
                                                return Some(Vec::new());
                                            }
                                        }
                                        Err(_) => return None,
                                    }
                                }
                            });
                            let stolen_count =
                                stolen_atomic.load(std::sync::atomic::Ordering::Relaxed);
                            (acc_res, stolen_count)
                        };

                    if let Some(env) = env_opt {
                        let (acc_res, stolen_count) =
                            run_with_env(env, std::mem::take(&mut non_eligible_orig), deleg_rx);
                        let end_ns = t_scope.elapsed().as_nanos();
                        if trace {
                            eprintln!(
                                "[TRACE] cpu worker total wall={} ms (stolen={})",
                                end_ns / 1_000_000,
                                stolen_count
                            );
                        }
                        return (acc_res, stolen_count, end_ns, None, None);
                    }

                    let loader = loader_for_scope
                        .expect("verify_packet_hybrid_core requires env_opt or lazy_loader");
                    if !non_eligible_orig.is_empty() {
                        let t_ld = Instant::now();
                        let loaded_res = loader();
                        loader_done_ref.store(true, std::sync::atomic::Ordering::Release);
                        if trace {
                            eprintln!(
                                "[TRACE] cpu lazy_loader finished in {} ms",
                                t_ld.elapsed().as_millis()
                            );
                        }
                        match loaded_res {
                            Ok(loaded) => {
                                let (acc_res, stolen_count) = run_with_env(
                                    &loaded,
                                    std::mem::take(&mut non_eligible_orig),
                                    deleg_rx,
                                );
                                let end_ns = t_scope.elapsed().as_nanos();
                                if trace {
                                    eprintln!(
                                        "[TRACE] cpu snapshot worker total wall={} ms (stolen={})",
                                        end_ns / 1_000_000,
                                        stolen_count
                                    );
                                }
                                (acc_res, stolen_count, end_ns, Some(loaded), None)
                            }
                            Err(v) => (Err(v), 0usize, t_scope.elapsed().as_nanos(), None, None),
                        }
                    } else {
                        let first_batch = loop {
                            match deleg_rx.recv() {
                                Ok(mut first) => {
                                    while let Ok(more) = deleg_rx.try_recv() {
                                        first.extend(more);
                                    }
                                    if !first.is_empty() {
                                        break Some(first);
                                    }
                                }
                                Err(_) => break None,
                            }
                        };
                        if let Some(batch) = first_batch {
                            let t_ld = Instant::now();
                            let loaded_res = loader();
                            loader_done_ref.store(true, std::sync::atomic::Ordering::Release);
                            if trace {
                                eprintln!(
                                    "[TRACE] cpu lazy_loader finished in {} ms",
                                    t_ld.elapsed().as_millis()
                                );
                            }
                            match loaded_res {
                                Ok(loaded) => {
                                    let (acc_res, stolen_count) =
                                        run_with_env(&loaded, batch, deleg_rx);
                                    let end_ns = t_scope.elapsed().as_nanos();
                                    if trace {
                                        eprintln!(
                                            "[TRACE] cpu snapshot lazy-deleg worker end={} ms (stolen={})",
                                            end_ns / 1_000_000,
                                            stolen_count
                                        );
                                    }
                                    (acc_res, stolen_count, end_ns, Some(loaded), None)
                                }
                                Err(v) => {
                                    (Err(v), 0usize, t_scope.elapsed().as_nanos(), None, None)
                                }
                            }
                        } else {
                            (Ok(()), 0usize, 0u128, None, Some(loader))
                        }
                    }
                })
                .map_err(|e| format!("failed spawning CPU worker thread: {e}"))?;

                let (verdicts, gpu_handled_end) = if eligible_job_indices.is_empty() {
                    pkt_e_nodes.release();
                    pkt_meta_nodes.release();
                    pkt_env_tables.release();
                    drop(deleg_tx);
                    gpu_done.store(true, std::sync::atomic::Ordering::Release);
                    (Vec::new(), 0usize)
                } else {
                    let t_up = Instant::now();
                    let e_nodes_pages: [wgpu::Buffer; E_NODES_NUM_PAGES] = std::array::from_fn(|p| {
                        let slice_full = pkt_e_nodes.as_slice();
                        let start = p * E_NODES_PAGE_WORDS;
                        let page_slice = if start < slice_full.len() {
                            let end = ((p + 1) * E_NODES_PAGE_WORDS).min(slice_full.len());
                            &slice_full[start..end]
                        } else {
                            &[0u32; 1][..]
                        };
                        ctx.create_storage_buffer_init(
                            &format!("tc-e-nodes-{p}"),
                            page_slice,
                            wgpu::BufferUsages::empty(),
                        )
                    });
                    let meta_nodes_slice: &[u32] = if pkt_meta_nodes.as_slice().is_empty() {
                        &[0]
                    } else {
                        pkt_meta_nodes.as_slice()
                    };
                    let meta_nodes_buf = ctx.create_storage_buffer_init(
                        "tc-meta-nodes",
                        meta_nodes_slice,
                        wgpu::BufferUsages::empty(),
                    );
                    let env_tables_slice: &[u32] = if pkt_env_tables.as_slice().is_empty() {
                        &[0]
                    } else {
                        pkt_env_tables.as_slice()
                    };
                    let env_tables_buf = ctx.create_storage_buffer_init(
                        "tc-env-tables",
                        env_tables_slice,
                        wgpu::BufferUsages::empty(),
                    );
                    let jobs_buf = ctx.create_storage_buffer_init(
                        "tc-jobs",
                        pkt_jobs,
                        wgpu::BufferUsages::empty(),
                    );
                    let verdicts_bytes =
                        (pkt_jobs.len() as u64) * (std::mem::size_of::<GpuVerdict>() as u64);
                    let verdicts_buf = ctx.create_storage_buffer_zeroed(
                        "tc-verdicts",
                        verdicts_bytes.max(16),
                        wgpu::BufferUsages::COPY_SRC,
                    );
                    ctx.wait_idle();
                    pcie_upload_ns = t_up.elapsed().as_nanos();
                    pkt_e_nodes.release();
                    pkt_meta_nodes.release();
                    pkt_env_tables.release();

                    let mut pool_guard = self
                        .pool
                        .lock()
                        .map_err(|_| "GPU tier buffer pool mutex poisoned".to_string())?;
                    let cache = &mut *pool_guard;

                    let mut verdicts = vec![GpuVerdict::default(); pkt_jobs.len()];
                    let mut tier2_jobs: Vec<u32> = Vec::new();
                    self.run_tier_with(
                        ctx,
                        &mut cache.tier1,
                        TIER1_CFG,
                        &pkt_header,
                        pkt_jobs,
                        e_nodes_len,
                        &e_nodes_pages,
                        &meta_nodes_buf,
                        &env_tables_buf,
                        &jobs_buf,
                        &verdicts_buf,
                        &eligible_job_indices,
                        max_binding_bytes,
                        true,
                        hybrid_large,
                        &mut max_quantum_ns,
                        &mut gpu_kernel_ns,
                        |cap| {
                            let mut g = frontier.lock().expect("frontier lock");
                            let (front, back) = *g;
                            if front >= back {
                                return None;
                            }
                            let eff_cap = if hybrid_large {
                                let head_bucket = pkt_jobs[eligible_job_indices[front] as usize].ast_bucket;
                                let waiting_for_loader = is_snapshot_lazy
                                    && !loader_done.load(std::sync::atomic::Ordering::Acquire);
                                let bucket_cutoff = if waiting_for_loader { 16 } else { 9 };
                                if head_bucket >= bucket_cutoff {
                                    return None;
                                } else if head_bucket >= 12 {
                                    cap.min(8_192)
                                } else {
                                    cap.min(16_384)
                                }
                            } else {
                                cap
                            };
                            let end = (front + eff_cap).min(back);
                            g.0 = end;
                            Some((front, end))
                        },
                        |chunk, did_cutoff| {
                            if chunk.is_empty() {
                                return Ok(());
                            }
                            let t_rb = Instant::now();
                            let first = chunk[0] as usize;
                            let last = chunk[chunk.len() - 1] as usize;
                            let span_verdicts: Vec<GpuVerdict> = ctx.read_buffer_range_vec(
                                &verdicts_buf,
                                first,
                                last - first + 1,
                            )?;
                            let mut batch_orig = Vec::new();
                            let mut c_ver = 0usize;
                            let mut c_rej = 0usize;
                            let mut c_t2 = 0usize;
                            let mut c_reasons = [0u32; 8];
                            for &job_idx_u32 in chunk {
                                let job_idx = job_idx_u32 as usize;
                                let v = span_verdicts[job_idx - first];
                                verdicts[job_idx] = v;
                                if v.status == STATUS_VERIFIED_GPU {
                                    c_ver += 1;
                                } else if v.status == STATUS_REJECTED_GPU {
                                    c_rej += 1;
                                    if trace {
                                        eprintln!(
                                            "[TRACE]   tier1 REJECT job={} orig={} reason={} steps={} scratch={}",
                                            job_idx,
                                            pkt_jobs[job_idx].orig_decl_idx,
                                            v.reason,
                                            v.steps_used,
                                            v.scratch_used
                                        );
                                    }
                                } else if v.status == STATUS_DELEGATE
                                    && matches!(
                                        v.reason,
                                        REASON_STACK_BUDGET | REASON_SCRATCH_BUDGET
                                    )
                                {
                                    c_t2 += 1;
                                    tier2_jobs.push(job_idx_u32);
                                } else {
                                    c_reasons[(v.reason as usize).min(7)] += 1;
                                    batch_orig.push(pkt_jobs[job_idx].orig_decl_idx as usize);
                                }
                            }
                            if trace {
                                eprintln!(
                                    "[TRACE]   tier1 chunk cutoff={} ver={} rej={} to_t2={} del={} reasons(unmod={},step={},stack={},scratch={})",
                                    did_cutoff,
                                    c_ver,
                                    c_rej,
                                    c_t2,
                                    batch_orig.len(),
                                    c_reasons[2],
                                    c_reasons[3],
                                    c_reasons[4],
                                    c_reasons[5]
                                );
                            }
                            gpu_readback_ns += t_rb.elapsed().as_nanos();
                            if !batch_orig.is_empty() {
                                let _ = deleg_tx.send(batch_orig);
                            }
                            Ok(())
                        },
                    )?;

                    let gpu_handled_end = {
                        let mut g = frontier.lock().expect("frontier lock");
                        let (rem_front, rem_back) = *g;
                        if hybrid_large && rem_front < rem_back {
                            g.0 = rem_back;
                            let mut tail_orig = Vec::with_capacity(rem_back - rem_front);
                            for &job_idx_u32 in &eligible_job_indices[rem_front..rem_back] {
                                let job_idx = job_idx_u32 as usize;
                                verdicts[job_idx] = GpuVerdict {
                                    status: STATUS_DELEGATE,
                                    reason: REASON_STEP_BUDGET,
                                    steps_used: 0,
                                    scratch_used: 0,
                                };
                                tail_orig.push(pkt_jobs[job_idx].orig_decl_idx as usize);
                            }
                            if trace {
                                eprintln!(
                                    "[TRACE] skip mega-AST tail bucket>=9 [{}..{}) len={} -> cpu",
                                    rem_front,
                                    rem_back,
                                    tail_orig.len()
                                );
                            }
                            let _ = deleg_tx.send(tail_orig);
                            rem_back
                        } else {
                            rem_front
                        }
                    };

                    if hybrid_large && !tier2_jobs.is_empty() && tier2_jobs.len() < 1_024 {
                        if trace {
                            eprintln!(
                                "[TRACE] skip small tier2 len={} -> cpu",
                                tier2_jobs.len()
                            );
                        }
                        let batch_orig: Vec<usize> = tier2_jobs
                            .iter()
                            .map(|&job_idx_u32| pkt_jobs[job_idx_u32 as usize].orig_decl_idx as usize)
                            .collect();
                        if !batch_orig.is_empty() {
                            let _ = deleg_tx.send(batch_orig);
                        }
                    } else if !tier2_jobs.is_empty() {
                        let t2_total = tier2_jobs.len();
                        *t2_pool.lock().expect("t2 pool lock") = tier2_jobs.clone();
                        *t2_frontier.lock().expect("t2 frontier lock") = (0usize, t2_total);
                        t2_ready.store(true, std::sync::atomic::Ordering::Release);
                        let _ = deleg_tx.send(Vec::new());
                        self.run_tier_with(
                            ctx,
                            &mut cache.tier2,
                            TIER2_CFG,
                            &pkt_header,
                            pkt_jobs,
                            e_nodes_len,
                            &e_nodes_pages,
                            &meta_nodes_buf,
                            &env_tables_buf,
                            &jobs_buf,
                            &verdicts_buf,
                            &tier2_jobs,
                            max_binding_bytes,
                            false,
                            hybrid_large,
                            &mut max_quantum_ns,
                            &mut gpu_kernel_ns,
                            |cap| {
                                let tail_range = {
                                    let mut g = t2_frontier.lock().expect("t2 frontier lock");
                                    let (front, back) = *g;
                                    if front >= back {
                                        return None;
                                    }
                                    if hybrid_large && back - front <= 32 {
                                        g.0 = back;
                                        Some((front, back))
                                    } else {
                                        let end = (front + cap).min(back);
                                        g.0 = end;
                                        return Some((front, end));
                                    }
                                };
                                if let Some((front, back)) = tail_range {
                                    let tail_orig: Vec<usize> = tier2_jobs[front..back]
                                        .iter()
                                        .map(|&job_idx_u32| {
                                            pkt_jobs[job_idx_u32 as usize].orig_decl_idx as usize
                                        })
                                        .collect();
                                    if trace {
                                        eprintln!(
                                            "[TRACE] tier2 skip small tail [{}..{}) len={}",
                                            front,
                                            back,
                                            tail_orig.len()
                                        );
                                    }
                                    if !tail_orig.is_empty() {
                                        let _ = deleg_tx.send(tail_orig);
                                    }
                                }
                                None
                            },
                            |chunk, _did_cutoff| {
                                if chunk.is_empty() {
                                    return Ok(());
                                }
                                let t_rb2 = Instant::now();
                                let first = chunk[0] as usize;
                                let last = chunk[chunk.len() - 1] as usize;
                                let span_verdicts: Vec<GpuVerdict> = ctx.read_buffer_range_vec(
                                    &verdicts_buf,
                                    first,
                                    last - first + 1,
                                )?;
                                let mut batch_orig = Vec::new();
                                for &job_idx_u32 in chunk {
                                    let job_idx = job_idx_u32 as usize;
                                    let v = span_verdicts[job_idx - first];
                                    verdicts[job_idx] = v;
                                    if trace && v.status == STATUS_REJECTED_GPU {
                                        eprintln!(
                                            "[TRACE]   tier2 REJECT job={} orig={} reason={} steps={} scratch={}",
                                            job_idx,
                                            pkt_jobs[job_idx].orig_decl_idx,
                                            v.reason,
                                            v.steps_used,
                                            v.scratch_used
                                        );
                                    }
                                    if v.status != STATUS_VERIFIED_GPU
                                        && v.status != STATUS_REJECTED_GPU
                                    {
                                        batch_orig.push(pkt_jobs[job_idx].orig_decl_idx as usize);
                                    }
                                }
                                gpu_readback_ns += t_rb2.elapsed().as_nanos();
                                if !batch_orig.is_empty() {
                                    let _ = deleg_tx.send(batch_orig);
                                }
                                Ok(())
                            },
                        )?;
                        tier2_promoted_count = t2_frontier.lock().expect("t2 frontier lock").0;
                    }

                    drop(deleg_tx);
                    gpu_done.store(true, std::sync::atomic::Ordering::Release);
                    drop(pool_guard);
                    drop(e_nodes_pages);
                    drop(meta_nodes_buf);
                    drop(env_tables_buf);
                    drop(jobs_buf);
                    drop(verdicts_buf);
                    (verdicts, gpu_handled_end)
                };

                let cpu_done = cpu_handle
                    .join()
                    .map_err(|_| "concurrent CPU worker panicked".to_string())?;
                Ok(((verdicts, gpu_handled_end), cpu_done))
            })?;
        let t2_handled = t2_frontier.lock().expect("t2 frontier lock").0;
        let t2_pool_vec = t2_pool.into_inner().expect("t2 pool lock");
        for &job_idx_u32 in t2_pool_vec.get(t2_handled..).unwrap_or(&[]) {
            verdicts[job_idx_u32 as usize].status = STATUS_STOLEN_T2;
        }
        let mut gpu_verified_count = 0usize;
        let mut gpu_rejected_count = 0usize;
        let mut gpu_delegated_orig: Vec<usize> = Vec::new();
        let mut first_reject_idx: Option<(usize, u32)> = None;
        let mut total_steps_gpu = 0u64;
        let mut max_scratch_words_used = 0u32;
        let mut delegate_reasons = [0u64; 8];
        delegate_reasons[1] = non_eligible_count as u64;
        delegate_reasons[6] = cpu_stolen_count as u64;

        for &job_idx in &eligible_job_indices[..gpu_handled_end] {
            let job = pkt_jobs[job_idx as usize];
            let v = verdicts[job_idx as usize];
            total_steps_gpu += v.steps_used as u64;
            if v.scratch_used > max_scratch_words_used {
                max_scratch_words_used = v.scratch_used;
            }
            match v.status {
                STATUS_VERIFIED_GPU => {
                    gpu_verified_count += 1;
                }
                STATUS_REJECTED_GPU => {
                    gpu_rejected_count += 1;
                    let orig_idx = job.orig_decl_idx as usize;
                    if first_reject_idx
                        .map(|(cur, _)| orig_idx < cur)
                        .unwrap_or(true)
                    {
                        first_reject_idx = Some((orig_idx, v.reason));
                    }
                }
                STATUS_STOLEN_T2 => {}
                _ => {
                    let b = (v.reason as usize).min(delegate_reasons.len() - 1);
                    delegate_reasons[b] += 1;
                    gpu_delegated_orig.push(job.orig_decl_idx as usize);
                }
            }
        }

        let delegated_count = non_eligible_count + gpu_delegated_orig.len() + cpu_stolen_count;
        let gpu_phase_ns = pcie_upload_ns + gpu_kernel_ns + gpu_readback_ns;
        let mut host_fallback_ns = cpu_end_from_scope_ns.saturating_sub(gpu_phase_ns);
        let mut first_gpu_reject = None;

        if let Some((rej_orig, reason_code)) = first_reject_idx {
            let active_env: &LoadedEnvironment = match env_opt {
                Some(e) => e,
                None => match lazy_loaded_env.as_ref() {
                    Some(e) => e,
                    None => {
                        let loader = unused_loader
                            .take()
                            .expect("lazy_loader available when env not yet loaded");
                        match loader() {
                            Ok(loaded) => {
                                lazy_loaded_env = Some(loaded);
                                lazy_loaded_env.as_ref().unwrap()
                            }
                            Err(v) => {
                                return Ok(GpuVerifyReport {
                                    verdict: v,
                                    total_decls,
                                    eligible_jobs_count: eligible_job_indices.len(),
                                    gpu_verified_count,
                                    gpu_rejected_count,
                                    delegated_count,
                                    host_verified_delegated: 0,
                                    tier2_promoted_count,
                                    pcie_upload_ns,
                                    gpu_kernel_ns,
                                    max_quantum_ns,
                                    gpu_readback_ns,
                                    host_fallback_ns,
                                    total_steps_gpu,
                                    max_scratch_words_used,
                                    delegate_reasons,
                                    first_gpu_reject: None,
                                });
                            }
                        }
                    }
                },
            };
            let name = active_env.decl_name_str(rej_orig);
            let reason_s = typecheck_reason_str(reason_code);
            let msg = format!("GPU rejected `{name}`: {reason_s} (code {reason_code})");
            first_gpu_reject = Some((rej_orig, name.clone(), reason_code));
            let mut prefix_indices: Vec<usize> = gpu_delegated_orig
                .iter()
                .copied()
                .filter(|&idx| idx < rej_orig)
                .collect();
            prefix_indices.push(rej_orig);
            let t_h = Instant::now();
            let (gpu_prefix_res, _) =
                verify_delegated_exact_with(active_env, &prefix_indices, host_threads, opts);
            host_fallback_ns += t_h.elapsed().as_nanos();
            let final_verdict = match gpu_prefix_res {
                Ok(()) => VerificationVerdict::Error {
                    message: format!(
                        "GPU/host mismatch: {msg}, but exact host checker accepted `{name}`"
                    ),
                    line_or_pos: rej_orig as u64,
                },
                Err(gpu_v) => match earliest_verdict(Err(gpu_v), cpu_res) {
                    Ok(()) => unreachable!(),
                    Err(v) => v,
                },
            };
            return Ok(GpuVerifyReport {
                verdict: final_verdict,
                total_decls,
                eligible_jobs_count: eligible_job_indices.len(),
                gpu_verified_count,
                gpu_rejected_count,
                delegated_count,
                host_verified_delegated: 0,
                tier2_promoted_count,
                pcie_upload_ns,
                gpu_kernel_ns,
                max_quantum_ns,
                gpu_readback_ns,
                host_fallback_ns,
                total_steps_gpu,
                max_scratch_words_used,
                delegate_reasons,
                first_gpu_reject,
            });
        }

        let (verdict, host_verified_delegated) = match cpu_res {
            Ok(()) => (
                VerificationVerdict::Accepted {
                    file_records,
                    fold_records: file_records,
                },
                delegated_count,
            ),
            Err(v) => (v, 0),
        };

        Ok(GpuVerifyReport {
            verdict,
            total_decls,
            eligible_jobs_count: eligible_job_indices.len(),
            gpu_verified_count,
            gpu_rejected_count,
            delegated_count,
            host_verified_delegated,
            tier2_promoted_count,
            pcie_upload_ns,
            gpu_kernel_ns,
            max_quantum_ns,
            gpu_readback_ns,
            host_fallback_ns,
            total_steps_gpu,
            max_scratch_words_used,
            delegate_reasons,
            first_gpu_reject,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_gpu_arena::loader::{build_olean_input, load_environment, InputSpec};
    use con_gpu_arena::soa_pack::{pack_arena, ArenaLimitsConfig};
    use con_gpu_arena::verify_host::verify_host_parallel;
    use std::path::Path;

    #[test]
    fn unresolved_sorry_delegates_and_other_missing_names_reject() {
        use con_gpu_arena::soa_pack::JOB_FLAG_VAL_GUARD_OK;

        let ctx = GpuContext::shared_vulkan_high_perf().expect("Vulkan adapter required");
        let pipe = TypecheckGpuPipeline::new(&ctx);
        let fixtures = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/missing_constant");
        for (fixture, is_sorry) in [("sorry.ndjson", true), ("unknown.ndjson", false)] {
            let env = load_environment(&InputSpec::Ndjson { path: fixtures.join(fixture) }).unwrap();
            let target = env.decls.len() - 1;
            assert_eq!(env.decl_name_str(target), "pntTest");
            let (host, _) = verify_host_parallel(&env, Some(1));
            let expected_exit = if is_sorry { 2 } else { 1 };
            assert_eq!(host.exit_code(), expected_exit);
            assert_eq!(host.failure_pos(), Some(target as u64));

            let mut pkt = pack_arena(&env, ArenaLimitsConfig::default());
            let job = pkt.jobs.iter().position(|j| j.orig_decl_idx as usize == target).unwrap();
            assert_eq!(pkt.jobs[job].flags & JOB_FLAG_VAL_GUARD_OK, 0);
            for skip_value_guard in [false, true] {
                // Exercise both the declaration guard and the inference instruction directly.
                if skip_value_guard {
                    pkt.jobs[job].flags |= JOB_FLAG_VAL_GUARD_OK;
                }
                let rep = pipe.verify_packet_hybrid_range_with(
                    &ctx, &env, &pkt, Some(1), target, VerifyOptions::default(),
                ).unwrap();
                assert_eq!(rep.verdict, host);
                if is_sorry {
                    assert_eq!(rep.delegate_reasons[2], 1, "sorryAx must delegate as unmodeled");
                    assert_eq!(rep.gpu_rejected_count, 0);
                } else {
                    assert_eq!(rep.first_gpu_reject, Some((target, "pntTest".to_owned(), 15)));
                }
            }
        }
    }

    #[test]
    fn gpu_typecheck_matches_host_on_e2e_samples() {
        let ctx = GpuContext::shared_vulkan_high_perf().expect("Vulkan GPU required");
        let pipe = TypecheckGpuPipeline::new(&ctx);

        let e2e_dir = Path::new("c:/Users/devin/Desktop/lean/vendor/con-leche/tests/e2e");
        let expected_path =
            Path::new("c:/Users/devin/Desktop/lean/vendor/con-leche/tests/e2e-expected.txt");
        if !e2e_dir.exists() || !expected_path.exists() {
            return;
        }
        let text = std::fs::read_to_string(expected_path).unwrap();
        let mut tested = 0usize;
        let mut gpu_verified_sum = 0usize;
        let mut gpu_rejected_sum = 0usize;

        for line in text.lines().take(60) {
            let trimmed = line.trim();
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            let mut parts = trimmed.split_whitespace();
            let code: u8 = parts.next().unwrap().parse().unwrap();
            let fname = parts.next().unwrap();
            let path = e2e_dir.join(fname);
            if !path.exists() {
                continue;
            }
            let env = match load_environment(&InputSpec::Ndjson { path: path.clone() }) {
                Ok(e) => e,
                Err(_) => {
                    assert_ne!(code, 0, "valid fixture {fname} failed load");
                    continue;
                }
            };
            let (host_verdict, _) = verify_host_parallel(&env, Some(2));
            let pkt = pack_arena(&env, ArenaLimitsConfig::default());
            let rep = pipe
                .verify_packet_hybrid(&ctx, &env, &pkt, Some(2))
                .expect("GPU hybrid should complete");
            assert_eq!(
                rep.verdict.exit_code(),
                host_verdict.exit_code(),
                "fixture {fname}: gpu={:?} vs host={:?}",
                rep.verdict,
                host_verdict
            );
            assert_eq!(
                rep.verdict.exit_code(),
                code,
                "fixture {fname}: got {:?}, expected code {code}",
                rep.verdict
            );
            gpu_verified_sum += rep.gpu_verified_count;
            gpu_rejected_sum += rep.gpu_rejected_count;
            tested += 1;
        }
        eprintln!(
            "E2E differential sample: tested={tested}, gpu_verified_sum={gpu_verified_sum}, gpu_rejected_sum={gpu_rejected_sum}"
        );
        assert!(tested > 10);
        assert!(
            gpu_rejected_sum > 0,
            "expected GPU to reject some negative e2e tests directly"
        );
    }

    #[test]
    fn gpu_typecheck_init_hybrid_differential() {
        let init_path =
            "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init.olean";
        if !Path::new(init_path).exists() {
            return;
        }
        let ctx = GpuContext::shared_vulkan_high_perf().expect("Vulkan GPU required");
        let pipe = TypecheckGpuPipeline::new(&ctx);

        let spec = build_olean_input(&[init_path.to_string()], &[], None, true);
        let env = load_environment(&spec).expect("Init should load");
        let cfg = ArenaLimitsConfig::default();
        let pkt = pack_arena(&env, cfg);
        if std::env::var_os("CON_GPU_TRACE").is_some() {
            eprintln!("[TRACE] Init loaded & packed: decls={}, pack_ms={}", env.decls.len(), pkt.pack_ns / 1_000_000);
        }
        let rep = pipe
            .verify_packet_hybrid(&ctx, &env, &pkt, None)
            .expect("Init GPU hybrid should run");

        eprintln!(
            "Init RX 7900 XTX: verdict={:?}, total={}, eligible={}, gpu_verified={}, gpu_rejected={}, delegated={}, tier2_promoted={}, pcie_upload_ms={}, gpu_kernel_ms={}, max_quantum_ms={}, gpu_readback_ms={}, host_fallback_ms={}, steps_gpu={}, max_scratch_words={}, delegate_reasons={:?}",
            rep.verdict,
            rep.total_decls,
            rep.eligible_jobs_count,
            rep.gpu_verified_count,
            rep.gpu_rejected_count,
            rep.delegated_count,
            rep.tier2_promoted_count,
            rep.pcie_upload_ns / 1_000_000,
            rep.gpu_kernel_ns / 1_000_000,
            rep.max_quantum_ns / 1_000_000,
            rep.gpu_readback_ns / 1_000_000,
            rep.host_fallback_ns / 1_000_000,
            rep.total_steps_gpu,
            rep.max_scratch_words_used,
            rep.delegate_reasons,
        );
        assert!(
            matches!(rep.verdict, VerificationVerdict::Accepted { .. }),
            "{:?}",
            rep.verdict
        );
        assert_eq!(rep.gpu_rejected_count, 0);
        assert!(
            rep.max_quantum_ns < 1_200_000_000,
            "quantum exceeded 1200ms WDDM TDR guard ceiling: {} ms",
            rep.max_quantum_ns / 1_000_000
        );
        assert!(
            rep.gpu_verified_count > 10_000,
            "expected high native GPU coverage, got {}",
            rep.gpu_verified_count
        );
    }

    #[test]
    fn gpu_typecheck_wave_f_exact_reductions() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
        use con_ron_core::arena::checker;
        use con_ron_core::arena::env::{
            IConstantInfo, IConstantVal, IDeclaration, IIndCaps, IRecRule, IRecRuleFire,
        };
        use con_ron_core::arena::handle::{EIdx, NIdx};
        use con_ron_core::arena::monad::{
            intern_e_app, intern_e_bvar, intern_e_const, intern_e_forall_e, intern_e_lam,
            intern_e_lit, intern_e_sort, intern_l_node, intern_ls_node, intern_name, AState,
        };
        use con_ron_core::arena::pins::{
            intern_reserved_pins, max_nat_size_default, pin_empty_levels, pin_eq, pin_nat,
            pin_nat_div, pin_nat_mod, pin_nat_pred, pin_nat_shift_left, pin_nat_shift_right,
            pin_nat_zero, pin_quot, pin_quot_mk, pin_zero_level,
        };
        use con_ron_core::arena::store::{EStore, LNodeView, PersTier};
        use con_ron_core::arena::stream_index;
        use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
        use con_ron_core::frontend::olean::records::read_oleans_full;
        use con_ron_core::frontend::prepare;
        use con_ron_core::frontend::prelude::builtin_prelude_e;
        use con_ron_core::kernel::{expr, name, pins_decode};
        use con_ron_core::ron::hashmap::Dup;
        use con_ron_core::ron::nat::{self as ron_nat, Nat as RonNat};

        fn ok<T, E>(r: Result<T, E>, msg: &str) -> T {
            match r {
                Ok(v) => v,
                Err(_) => panic!("{msg}"),
            }
        }
        fn segs(pers: &PersTier, st: &mut AState, parts: &[&str]) -> NIdx {
            let mut nm = name::anonymous();
            for &s in parts {
                nm = name::mk_str(nm, s.chars().map(|c| c as u32).collect());
            }
            ok(intern_name(pers, st, &nm), "intern_name")
        }
        fn finish_env(
            empty_pers: &PersTier,
            mut st: AState,
            prelude_ix: prepare::PreludeIx,
            decls: Vec<IDeclaration>,
        ) -> LoadedEnvironment {
            let prepared = ok(
                prepare::prepare_d(empty_pers, &mut st, prelude_ix, decls, &DeclUsedConsts),
                "prepare_d",
            );
            let file_records = prepared.decls.len();
            let pins_decoded = ok(pins_decode::decode_embedded(), "pins_decode");
            let max_nat = max_nat_size_default();
            let ipins = ok(
                checker::intern_all_pins(empty_pers, &mut st, &pins_decoded, &max_nat),
                "intern_all_pins",
            );
            let ix = ok(
                stream_index::build_index(
                    empty_pers,
                    &mut st,
                    stream_index::stream_index_empty(),
                    &prepared.decls,
                    0,
                ),
                "build_index",
            );
            let pers = checker::freeze_tier(&mut st.store, ix);
            LoadedEnvironment {
                pers,
                pins: st.pins,
                ipins,
                decls: prepared.decls,
                file_records,
                synthesized: prepared.synthesised,
                hoisted: prepared.hoisted.len(),
                olean: None,
                load_ns: 0,
                materialize_ns: 0,
                index_ns: 0,
                thm_materialized_count: 0,
                closure_fingerprint: None,
                closure_roots: Vec::new(),
                closure_manifest: Vec::new(),
                module_hashes: std::collections::HashMap::new(),
                preverified_prefix: 0,
            }
        }

        fn build_env<F>(mut add_case: F) -> LoadedEnvironment
        where
            F: FnMut(&PersTier, &mut AState, &mut Vec<IDeclaration>),
        {
            let empty_pers = PersTier::empty();
            let mut st = AState::init(EStore::empty());
            ok(intern_reserved_pins(&empty_pers, &mut st), "pins");
            let prelude_ix = ok(builtin_prelude_e(&empty_pers, &mut st), "prelude");

            let mut decls = Vec::new();
            add_case(&empty_pers, &mut st, &mut decls);
            finish_env(&empty_pers, st, prelude_ix, decls)
        }

        fn build_with_nat_oleans<F>(lean_lib: &str, mut add_case: F) -> LoadedEnvironment
        where
            F: FnMut(&PersTier, &mut AState, &mut Vec<IDeclaration>),
        {
            let empty_pers = PersTier::empty();
            let mut st = AState::init(EStore::empty());
            ok(intern_reserved_pins(&empty_pers, &mut st), "pins");
            let prelude_ix = ok(builtin_prelude_e(&empty_pers, &mut st), "prelude");
            let sp = vec![con_gpu_arena::fs::str_to_cp(lean_lib)];
            let roots = vec![
                segs(&empty_pers, &mut st, &["Init", "Data", "Nat", "Div"]),
                segs(&empty_pers, &mut st, &["Init", "Data", "Nat", "Bitwise"]),
            ];
            let mut decls = ok(
                read_oleans_full(
                    &con_gpu_arena::fs::StdFs,
                    &empty_pers,
                    &mut st.store,
                    &sp,
                    &roots,
                    &None,
                ),
                "read_oleans_full",
            );
            add_case(&empty_pers, &mut st, &mut decls);
            finish_env(&empty_pers, st, prelude_ix, decls)
        }

        fn ap_many(pers: &PersTier, st: &mut AState, mut f: EIdx, args: &[EIdx]) -> EIdx {
            for a in args {
                f = ok(intern_e_app(pers, st, f, a.dup2()), "intern_app");
            }
            f
        }
        fn lam(pers: &PersTier, st: &mut AState, ty: EIdx, body: EIdx) -> EIdx {
            ok(intern_e_lam(pers, st, ty, body), "intern_lam")
        }
        fn pi(pers: &PersTier, st: &mut AState, ty: EIdx, body: EIdx) -> EIdx {
            ok(intern_e_forall_e(pers, st, ty, body), "intern_pi")
        }
        fn lit_u64(pers: &PersTier, st: &mut AState, v: u64) -> EIdx {
            lit(pers, st, ron_nat::from_u64(v))
        }
        fn lit(pers: &PersTier, st: &mut AState, v: RonNat) -> EIdx {
            ok(intern_e_lit(pers, st, expr::literal_nat(v)), "intern_lit")
        }
        fn push_idx_box_ind(
            pers: &PersTier,
            st: &mut AState,
            decls: &mut Vec<IDeclaration>,
        ) -> (EIdx, EIdx, NIdx) {
            let empty_ls = ok(pin_empty_levels(st), "empty_ls");
            let zero_l = ok(pin_zero_level(st), "zero_l");
            let one_l = ok(intern_l_node(pers, st, LNodeView::Succ(zero_l)), "one_l");
            let nat_e = ok(intern_e_const(pers, st, ok(pin_nat(st), "Nat"), empty_ls.dup2()), "nat");
            let nat_zero_e = ok(
                intern_e_const(pers, st, ok(pin_nat_zero(st), "Nat.zero"), empty_ls.dup2()),
                "nat_zero",
            );
            let b0 = ok(intern_e_bvar(pers, st, 0), "b0");
            let b1 = ok(intern_e_bvar(pers, st, 1), "b1");
            let b3 = ok(intern_e_bvar(pers, st, 3), "b3");

            let u_n = segs(pers, st, &["u"]);
            let u_l = ok(intern_l_node(pers, st, LNodeView::Param(u_n.dup2())), "u_l");
            let sort_u = ok(intern_e_sort(pers, st, u_l), "Sort u");
            let type0 = ok(intern_e_sort(pers, st, one_l), "Type 0");
            let idx_box_n = segs(pers, st, &["WaveF", "IdxBox"]);
            let idx_mk_n = segs(pers, st, &["WaveF", "IdxBox", "mk"]);
            let idx_rec_n = segs(pers, st, &["WaveF", "IdxBox", "rec"]);
            let idx_box_c = ok(intern_e_const(pers, st, idx_box_n.dup2(), empty_ls.dup2()), "IdxBox");
            let idx_mk_c = ok(intern_e_const(pers, st, idx_mk_n.dup2(), empty_ls), "IdxBox.mk");
            let idx_box_ty = pi(pers, st, nat_e.dup2(), type0);
            let idx_mk_res = ap_many(pers, st, idx_box_c.dup2(), &[nat_zero_e.dup2()]);
            let idx_mk_ty = pi(pers, st, nat_e.dup2(), idx_mk_res);
            let idx_box_b0 = ap_many(pers, st, idx_box_c.dup2(), &[b0.dup2()]);
            let idx_motive_inner = pi(pers, st, idx_box_b0.dup2(), sort_u);
            let idx_motive_ty = pi(pers, st, nat_e.dup2(), idx_motive_inner);
            let idx_mk_b0 = ap_many(pers, st, idx_mk_c.dup2(), &[b0.dup2()]);
            let idx_minor_app = ap_many(pers, st, b1.dup2(), &[nat_zero_e, idx_mk_b0]);
            let idx_minor_ty = pi(pers, st, nat_e.dup2(), idx_minor_app);
            let idx_rec_ret = ap_many(pers, st, b3, &[b1.dup2(), b0.dup2()]);
            let idx_rec_t = pi(pers, st, idx_box_b0, idx_rec_ret);
            let idx_rec_n_t = pi(pers, st, nat_e.dup2(), idx_rec_t);
            let idx_rec_min = pi(pers, st, idx_minor_ty.dup2(), idx_rec_n_t);
            let idx_rec_ty = pi(pers, st, idx_motive_ty.dup2(), idx_rec_min);
            let rhs_app = ap_many(pers, st, b1, &[b0]);
            let rhs_l1 = lam(pers, st, nat_e, rhs_app);
            let rhs_l2 = lam(pers, st, idx_minor_ty, rhs_l1);
            let idx_rule_rhs = lam(pers, st, idx_motive_ty, rhs_l2);
            decls.push(IDeclaration::IndDecl(
                vec![
                    IConstantInfo::IndInfo(
                        IConstantVal {
                            name: idx_box_n.dup2(),
                            level_params: Vec::new(),
                            ty: idx_box_ty,
                        },
                        IIndCaps {
                            eta: false,
                            all: vec![idx_box_n.dup2()],
                            nparams: 0,
                            n_idx: 1,
                            ctors: vec![idx_mk_n.dup2()],
                            never_zero: true,
                        },
                    ),
                    IConstantInfo::CtorInfo(
                        IConstantVal {
                            name: idx_mk_n.dup2(),
                            level_params: Vec::new(),
                            ty: idx_mk_ty,
                        },
                        0,
                        1,
                        idx_box_n,
                    ),
                    IConstantInfo::RecInfo(
                        IConstantVal {
                            name: idx_rec_n.dup2(),
                            level_params: vec![u_n],
                            ty: idx_rec_ty,
                        },
                        3,
                        2,
                        false,
                        vec![IRecRule {
                            ctor: idx_mk_n,
                            nfields: 1,
                            fire: IRecRuleFire::Plain,
                            rhs: idx_rule_rhs,
                        }],
                    ),
                ],
                0,
            ));
            (idx_box_c, idx_mk_c, idx_rec_n)
        }
        fn eq_nat_thm(
            pers: &PersTier,
            st: &mut AState,
            name_parts: &[&str],
            lhs: EIdx,
            rhs: EIdx,
            proof_val: EIdx,
        ) -> IDeclaration {
            let zero_l = ok(pin_zero_level(st), "zero_l");
            let one_l = ok(intern_l_node(pers, st, LNodeView::Succ(zero_l)), "one_l");
            let one_ls = ok(intern_ls_node(pers, st, vec![one_l]), "one_ls");
            let empty_ls = ok(pin_empty_levels(st), "empty_ls");
            let nat_e = ok(intern_e_const(pers, st, ok(pin_nat(st), "Nat"), empty_ls), "nat_e");
            let eq_n = ok(pin_eq(st), "Eq");
            let eq_1 = ok(intern_e_const(pers, st, eq_n, one_ls), "Eq.{1}");
            let ty = ap_many(pers, st, eq_1, &[nat_e, lhs, rhs]);
            let nm = segs(pers, st, name_parts);
            IDeclaration::ThmDecl(
                IConstantVal {
                    name: nm,
                    level_params: Vec::new(),
                    ty,
                },
                proof_val,
            )
        }
        fn eq_refl_nat(pers: &PersTier, st: &mut AState, x: EIdx) -> EIdx {
            let zero_l = ok(pin_zero_level(st), "zero_l");
            let one_l = ok(intern_l_node(pers, st, LNodeView::Succ(zero_l)), "one_l");
            let one_ls = ok(intern_ls_node(pers, st, vec![one_l]), "one_ls");
            let empty_ls = ok(pin_empty_levels(st), "empty_ls");
            let nat_e = ok(intern_e_const(pers, st, ok(pin_nat(st), "Nat"), empty_ls), "nat_e");
            let refl_n = segs(pers, st, &["Eq", "refl"]);
            let refl_1 = ok(intern_e_const(pers, st, refl_n, one_ls), "Eq.refl.{1}");
            ap_many(pers, st, refl_1, &[nat_e, x])
        }

        let ctx = GpuContext::shared_vulkan_high_perf().expect("Vulkan GPU required");
        let pipe = TypecheckGpuPipeline::new(&ctx);

        // 1. Standalone valid exact reductions: Eq.rec (is_k), Quot.{lift,ind}, Indexed never_zero iota.
        let valid_env = build_env(|pers, st, decls| {
            let empty_ls = ok(pin_empty_levels(st), "empty_ls");
            let zero_l = ok(pin_zero_level(st), "zero_l");
            let prop_e = ok(intern_e_sort(pers, st, zero_l.dup2()), "Prop");
            let one_l = ok(intern_l_node(pers, st, LNodeView::Succ(zero_l.dup2())), "one_l");
            let one_ls = ok(intern_ls_node(pers, st, vec![one_l.dup2()]), "one_ls");
            let one_one_ls = ok(
                intern_ls_node(pers, st, vec![one_l.dup2(), one_l.dup2()]),
                "one_one_ls",
            );
            let nat_e = ok(intern_e_const(pers, st, ok(pin_nat(st), "Nat"), empty_ls.dup2()), "nat");
            let nat_zero_e = ok(
                intern_e_const(pers, st, ok(pin_nat_zero(st), "Nat.zero"), empty_ls.dup2()),
                "nat_zero",
            );
            let eq_1 = ok(intern_e_const(pers, st, ok(pin_eq(st), "Eq"), one_ls.dup2()), "Eq.{1}");
            let b0 = ok(intern_e_bvar(pers, st, 0), "b0");
            let b1 = ok(intern_e_bvar(pers, st, 1), "b1");
            let b2 = ok(intern_e_bvar(pers, st, 2), "b2");
            let b3 = ok(intern_e_bvar(pers, st, 3), "b3");

            let l7 = lit_u64(pers, st, 7);
            let l42 = lit_u64(pers, st, 42);
            let l99 = lit_u64(pers, st, 99);

            // Eq.rec (is_k fast path)
            let eq_rec_n = segs(pers, st, &["Eq", "rec"]);
            let eq_rec_11 = ok(intern_e_const(pers, st, eq_rec_n, one_one_ls.dup2()), "Eq.rec");
            let eq_7_b0 = ap_many(pers, st, eq_1.dup2(), &[nat_e.dup2(), l7.dup2(), b0.dup2()]);
            let eq_rec_m2 = lam(pers, st, eq_7_b0, nat_e.dup2());
            let eq_rec_motive = lam(pers, st, nat_e.dup2(), eq_rec_m2);
            let eq_refl_7 = eq_refl_nat(pers, st, l7.dup2());
            let eq_rec_app = ap_many(
                pers,
                st,
                eq_rec_11,
                &[nat_e.dup2(), l7.dup2(), eq_rec_motive, l42.dup2(), l7.dup2(), eq_refl_7],
            );
            let pr_eq_rec = eq_refl_nat(pers, st, l42.dup2());
            decls.push(eq_nat_thm(pers, st, &["WaveF", "eq_rec_k"], eq_rec_app, l42, pr_eq_rec));

            // Quot.lift & Quot.ind
            let eq_nat_b1_b0 = ap_many(pers, st, eq_1.dup2(), &[nat_e.dup2(), b1.dup2(), b0.dup2()]);
            let qr_inner = lam(pers, st, nat_e.dup2(), eq_nat_b1_b0.dup2());
            let quot_rel = lam(pers, st, nat_e.dup2(), qr_inner);
            let quot_c = ok(intern_e_const(pers, st, ok(pin_quot(st), "Quot"), one_ls.dup2()), "Quot1");
            let quot_mk_c = ok(intern_e_const(pers, st, ok(pin_quot_mk(st), "Quot.mk"), one_ls.dup2()), "Quot.mk1");
            let quot_lift_n = segs(pers, st, &["Quot", "lift"]);
            let quot_ind_n = segs(pers, st, &["Quot", "ind"]);
            let quot_nat_r = ap_many(pers, st, quot_c, &[nat_e.dup2(), quot_rel.dup2()]);
            let quot_mk_7 = ap_many(pers, st, quot_mk_c, &[nat_e.dup2(), quot_rel.dup2(), l7.dup2()]);
            let id_nat = lam(pers, st, nat_e.dup2(), l7.dup2());
            let eq_7_7_coh = eq_refl_nat(pers, st, l7.dup2());
            let coh3 = lam(pers, st, eq_nat_b1_b0, eq_7_7_coh);
            let coh2 = lam(pers, st, nat_e.dup2(), coh3);
            let coh_h = lam(pers, st, nat_e.dup2(), coh2);
            let q_lift_11 = ok(intern_e_const(pers, st, quot_lift_n, one_one_ls), "Quot.lift");
            let q_lift_app = ap_many(
                pers,
                st,
                q_lift_11,
                &[nat_e.dup2(), quot_rel.dup2(), nat_e.dup2(), id_nat, coh_h, quot_mk_7.dup2()],
            );
            let pr_qlift = eq_refl_nat(pers, st, l7.dup2());
            decls.push(eq_nat_thm(pers, st, &["WaveF", "quot_lift"], q_lift_app, l7.dup2(), pr_qlift));

            let eq_7_7 = ap_many(pers, st, eq_1.dup2(), &[nat_e.dup2(), l7.dup2(), l7.dup2()]);
            let q_ind_motive = lam(pers, st, quot_nat_r, eq_7_7.dup2());
            let q_ind_minor_body = eq_refl_nat(pers, st, l7);
            let q_ind_minor = lam(pers, st, nat_e.dup2(), q_ind_minor_body);
            let q_ind_1 = ok(intern_e_const(pers, st, quot_ind_n, one_ls.dup2()), "Quot.ind");
            let q_ind_app = ap_many(
                pers,
                st,
                q_ind_1,
                &[nat_e.dup2(), quot_rel, q_ind_motive, q_ind_minor, quot_mk_7],
            );
            decls.push(IDeclaration::ThmDecl(
                IConstantVal {
                    name: segs(pers, st, &["WaveF", "quot_ind"]),
                    level_params: Vec::new(),
                    ty: eq_7_7,
                },
                q_ind_app,
            ));

            // Indexed never_zero inductive: IdxBox : Nat -> Type 0
            let _ = (one_l, b2, b3);
            let (idx_box_c, idx_mk_c, idx_rec_n) = push_idx_box_ind(pers, st, decls);

            let idx_box_b0 = ap_many(pers, st, idx_box_c, &[b0.dup2()]);
            let idx_m2 = lam(pers, st, idx_box_b0, nat_e.dup2());
            let idx_box_motive = lam(pers, st, nat_e.dup2(), idx_m2);
            let idx_minor_id = lam(pers, st, nat_e, b0);
            let idx_rec_1 = ok(intern_e_const(pers, st, idx_rec_n, one_ls), "IdxBox.rec.{1}");
            let idx_mk_99 = ap_many(pers, st, idx_mk_c, &[l99.dup2()]);
            let idx_rec_app = ap_many(
                pers,
                st,
                idx_rec_1,
                &[idx_box_motive, idx_minor_id, nat_zero_e, idx_mk_99],
            );
            let pr_idx = eq_refl_nat(pers, st, l99.dup2());
            decls.push(eq_nat_thm(pers, st, &["WaveF", "idx_never_zero_iota"], idx_rec_app, l99, pr_idx));
            let _ = prop_e;
        });

        let (valid_host, _) = verify_host_parallel(&valid_env, Some(2));
        let valid_pkt = pack_arena(&valid_env, ArenaLimitsConfig::default());
        let valid_rep = pipe
            .verify_packet_hybrid(&ctx, &valid_env, &valid_pkt, Some(2))
            .expect("Wave F valid GPU hybrid");
        assert!(matches!(valid_host, VerificationVerdict::Accepted { .. }), "{valid_host:?}");
        assert!(matches!(valid_rep.verdict, VerificationVerdict::Accepted { .. }), "{:?}", valid_rep.verdict);
        assert_eq!(valid_rep.gpu_rejected_count, 0);
        assert!(
            valid_rep.gpu_verified_count >= 4,
            "expected all standalone Wave F theorems verified natively on GPU, got {} (reasons={:?})",
            valid_rep.gpu_verified_count,
            valid_rep.delegate_reasons
        );

        // 2. Real Lean 4 Init.Data.Nat.{Div,Bitwise} + Wave F Nat ops & 64-bit shift overflow + bad div 0
        let lean_lib = "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean";
        if Path::new(lean_lib).join("Init/Data/Nat/Div.olean").exists() {
            let nat_env = build_with_nat_oleans(lean_lib, |pers, st, decls| {
                let empty_ls = ok(pin_empty_levels(st), "empty_ls");
                let pred_c = ok(intern_e_const(pers, st, ok(pin_nat_pred(st), "pred"), empty_ls.dup2()), "pred_c");
                let div_c = ok(intern_e_const(pers, st, ok(pin_nat_div(st), "div"), empty_ls.dup2()), "div_c");
                let mod_c = ok(intern_e_const(pers, st, ok(pin_nat_mod(st), "mod"), empty_ls.dup2()), "mod_c");
                let shr_c = ok(intern_e_const(pers, st, ok(pin_nat_shift_right(st), "shr"), empty_ls.dup2()), "shr_c");
                let shl_c = ok(intern_e_const(pers, st, ok(pin_nat_shift_left(st), "shl"), empty_ls), "shl_c");

                let l0 = lit_u64(pers, st, 0);
                let l1 = lit_u64(pers, st, 1);
                let l3 = lit_u64(pers, st, 3);
                let l4 = lit_u64(pers, st, 4);
                let l5 = lit_u64(pers, st, 5);
                let l32 = lit_u64(pers, st, 32);
                let l35 = lit_u64(pers, st, 35);
                let l47 = lit_u64(pers, st, 47);
                let l64 = lit_u64(pers, st, 64);
                let l99 = lit_u64(pers, st, 99);
                let l_big_n = lit_u64(pers, st, 1_000_000_000_003);
                let l_100k = lit_u64(pers, st, 100_000);
                let l_10m = lit_u64(pers, st, 10_000_000);
                let l_hi = lit_u64(pers, st, 0x1_0000_0005);
                let l_shl35 = lit_u64(pers, st, 1u64 << 35);
                let l_pow64 = lit(pers, st, RonNat { limbs: vec![0, 1] });

                let lhs_pred = ap_many(pers, st, pred_c.dup2(), &[l5]);
                let pr_pred = eq_refl_nat(pers, st, l4.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_pred_5"], lhs_pred, l4, pr_pred));

                let lhs_pred0 = ap_many(pers, st, pred_c, &[l0.dup2()]);
                let pr_pred0 = eq_refl_nat(pers, st, l0.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_pred_0"], lhs_pred0, l0.dup2(), pr_pred0));

                let lhs_div = ap_many(pers, st, div_c.dup2(), &[l_big_n.dup2(), l_100k.dup2()]);
                let pr_div = eq_refl_nat(pers, st, l_10m.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_div_u64"], lhs_div, l_10m, pr_div));

                let lhs_div0 = ap_many(pers, st, div_c, &[l47.dup2(), l0.dup2()]);
                let pr_div0 = eq_refl_nat(pers, st, l0.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_div_zero"], lhs_div0, l0.dup2(), pr_div0));

                let lhs_mod = ap_many(pers, st, mod_c.dup2(), &[l_big_n, l_100k]);
                let pr_mod = eq_refl_nat(pers, st, l3.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_mod_u64"], lhs_mod, l3, pr_mod));

                let lhs_mod0 = ap_many(pers, st, mod_c, &[l47.dup2(), l0.dup2()]);
                let pr_mod0 = eq_refl_nat(pers, st, l47.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_mod_zero"], lhs_mod0, l47, pr_mod0));

                let lhs_shr = ap_many(pers, st, shr_c.dup2(), &[l_hi, l32]);
                let pr_shr = eq_refl_nat(pers, st, l1.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_shr_32"], lhs_shr, l1.dup2(), pr_shr));

                let lhs_shr64 = ap_many(pers, st, shr_c, &[l99, l64.dup2()]);
                let pr_shr64 = eq_refl_nat(pers, st, l0.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_shr_64"], lhs_shr64, l0, pr_shr64));

                let lhs_shl = ap_many(pers, st, shl_c.dup2(), &[l1.dup2(), l35]);
                let pr_shl = eq_refl_nat(pers, st, l_shl35.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_shl_35"], lhs_shl, l_shl35, pr_shl));

                // 64-bit shift overflow delegates cleanly to host (`REASON_UNMODELED`)
                let lhs_ov = ap_many(pers, st, shl_c, &[l1, l64]);
                let pr_ov = eq_refl_nat(pers, st, l_pow64.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "nat_shl_64_overflow"], lhs_ov, l_pow64, pr_ov));
            });
            let (nat_host, _) = verify_host_parallel(&nat_env, Some(4));
            let nat_pkt = pack_arena(&nat_env, ArenaLimitsConfig::default());
            let nat_rep = pipe
                .verify_packet_hybrid(&ctx, &nat_env, &nat_pkt, Some(4))
                .expect("Wave F real Nat olean GPU hybrid");
            assert!(matches!(nat_host, VerificationVerdict::Accepted { .. }), "{nat_host:?}");
            assert!(matches!(nat_rep.verdict, VerificationVerdict::Accepted { .. }), "{:?}", nat_rep.verdict);
            assert_eq!(nat_rep.gpu_rejected_count, 0);
            assert!(
                nat_rep.delegated_count >= 1,
                "expected >= 64-bit shift overflow to delegate cleanly"
            );

            // Bad Nat.div x 0 = 1 must be REJECTED directly by GPU & host.
            let bad_nat_env = build_with_nat_oleans(lean_lib, |pers, st, decls| {
                let empty_ls = ok(pin_empty_levels(st), "empty_ls");
                let div_c = ok(intern_e_const(pers, st, ok(pin_nat_div(st), "div"), empty_ls), "div");
                let l47 = lit_u64(pers, st, 47);
                let l0 = lit_u64(pers, st, 0);
                let l1 = lit_u64(pers, st, 1);
                let lhs = ap_many(pers, st, div_c, &[l47, l0]);
                let pr = eq_refl_nat(pers, st, l1.dup2());
                decls.push(eq_nat_thm(pers, st, &["WaveF", "bad_div_0"], lhs, l1, pr));
            });
            let (bn_host, _) = verify_host_parallel(&bad_nat_env, Some(4));
            let bn_pkt = pack_arena(&bad_nat_env, ArenaLimitsConfig::default());
            let bn_rep = pipe
                .verify_packet_hybrid(&ctx, &bad_nat_env, &bn_pkt, Some(4))
                .expect("Wave F bad div 0 GPU hybrid");
            assert!(matches!(bn_host, VerificationVerdict::Rejected { .. }), "{bn_host:?}");
            assert!(matches!(bn_rep.verdict, VerificationVerdict::Rejected { .. }), "{:?}", bn_rep.verdict);
            assert_eq!(bn_rep.gpu_rejected_count, 1);
        }

        // 3. Invalid standalone reductions/motives must be REJECTED by both GPU and host:
        //    (a) IdxBox invalid motive, (b) Quot.ind invalid minor.
        for bad_kind in 0..2u8 {
            let bad_env = build_env(|pers, st, decls| {
                let empty_ls = ok(pin_empty_levels(st), "empty_ls");
                let zero_l = ok(pin_zero_level(st), "zero_l");
                let one_l = ok(intern_l_node(pers, st, LNodeView::Succ(zero_l)), "one_l");
                let one_ls = ok(intern_ls_node(pers, st, vec![one_l]), "one_ls");
                let nat_e = ok(intern_e_const(pers, st, ok(pin_nat(st), "Nat"), empty_ls.dup2()), "nat");
                let nat_zero_e = ok(
                    intern_e_const(pers, st, ok(pin_nat_zero(st), "Nat.zero"), empty_ls.dup2()),
                    "nat_zero",
                );
                let eq_1 = ok(intern_e_const(pers, st, ok(pin_eq(st), "Eq"), one_ls.dup2()), "Eq.{1}");
                let b0 = ok(intern_e_bvar(pers, st, 0), "b0");
                let b1 = ok(intern_e_bvar(pers, st, 1), "b1");
                if bad_kind == 0 {
                    let (idx_box_c, idx_mk_c, idx_rec_n) = push_idx_box_ind(pers, st, decls);
                    let idx_box_b0 = ap_many(pers, st, idx_box_c, &[b0.dup2()]);
                    let bad_m2 = lam(pers, st, idx_box_b0, b1);
                    let bad_motive = lam(pers, st, nat_e.dup2(), bad_m2);
                    let idx_rec_1 = ok(intern_e_const(pers, st, idx_rec_n, one_ls), "rec1");
                    let minor_id = lam(pers, st, nat_e.dup2(), b0);
                    let l99 = lit_u64(pers, st, 99);
                    let idx_mk_99 = ap_many(pers, st, idx_mk_c, &[l99]);
                    let bad_term = ap_many(
                        pers,
                        st,
                        idx_rec_1,
                        &[bad_motive, minor_id, nat_zero_e, idx_mk_99],
                    );
                    decls.push(IDeclaration::ThmDecl(
                        IConstantVal { name: segs(pers, st, &["WaveF", "bad_idx_motive"]), level_params: Vec::new(), ty: nat_e },
                        bad_term,
                    ));
                } else {
                    let l7 = lit_u64(pers, st, 7);
                    let l8 = lit_u64(pers, st, 8);
                    let eq_b1_b0 = ap_many(pers, st, eq_1.dup2(), &[nat_e.dup2(), b1, b0.dup2()]);
                    let qr2 = lam(pers, st, nat_e.dup2(), eq_b1_b0);
                    let quot_rel = lam(pers, st, nat_e.dup2(), qr2);
                    let quot_c = ok(intern_e_const(pers, st, ok(pin_quot(st), "Quot"), one_ls.dup2()), "Q1");
                    let quot_mk_c = ok(intern_e_const(pers, st, ok(pin_quot_mk(st), "Quot.mk"), one_ls.dup2()), "QM1");
                    let quot_ind_n = segs(pers, st, &["Quot", "ind"]);
                    let quot_nat_r = ap_many(pers, st, quot_c, &[nat_e.dup2(), quot_rel.dup2()]);
                    let quot_mk_7 = ap_many(pers, st, quot_mk_c, &[nat_e.dup2(), quot_rel.dup2(), l7.dup2()]);
                    let eq_7_8 = ap_many(pers, st, eq_1, &[nat_e.dup2(), l7.dup2(), l8]);
                    let q_motive = lam(pers, st, quot_nat_r, eq_7_8.dup2());
                    let bad_refl = eq_refl_nat(pers, st, l7);
                    let q_bad_minor = lam(pers, st, nat_e.dup2(), bad_refl);
                    let q_ind_1 = ok(intern_e_const(pers, st, quot_ind_n, one_ls), "QI1");
                    let bad_proof = ap_many(
                        pers,
                        st,
                        q_ind_1,
                        &[nat_e, quot_rel, q_motive, q_bad_minor, quot_mk_7],
                    );
                    decls.push(IDeclaration::ThmDecl(
                        IConstantVal { name: segs(pers, st, &["WaveF", "bad_quot_ind"]), level_params: Vec::new(), ty: eq_7_8 },
                        bad_proof,
                    ));
                }
            });
            let (bad_host, _) = verify_host_parallel(&bad_env, Some(2));
            let bad_pkt = pack_arena(&bad_env, ArenaLimitsConfig::default());
            let bad_rep = pipe
                .verify_packet_hybrid(&ctx, &bad_env, &bad_pkt, Some(2))
                .expect("Wave F bad case GPU hybrid");
            assert!(matches!(bad_host, VerificationVerdict::Rejected { .. }), "bad_kind={bad_kind}: {bad_host:?}");
            assert!(matches!(bad_rep.verdict, VerificationVerdict::Rejected { .. }), "bad_kind={bad_kind}: {:?}", bad_rep.verdict);
            assert_eq!(
                bad_rep.gpu_rejected_count, 1,
                "expected bad_kind={bad_kind} to be rejected directly by GPU"
            );
        }
            })
            .expect("spawn")
            .join()
            .expect("join");
    }

    #[test]
    fn gpu_snapshot_lazy_loader_skips_when_100pct_gpu_and_loads_on_fallback_or_reject() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                use std::sync::atomic::{AtomicUsize, Ordering};
                use con_ron_core::arena::checker;
                use con_ron_core::arena::env::{IConstantVal, IDeclaration};
                use con_ron_core::arena::monad::{
                    intern_e_bvar, intern_e_forall_e, intern_e_lam, intern_e_sort, intern_name,
                    AState,
                };
                use con_ron_core::arena::pins::{
                    intern_reserved_pins, max_nat_size_default, pin_zero_level,
                };
                use con_ron_core::arena::store::{EStore, PersTier};
                use con_ron_core::arena::stream_index;
                use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
                use con_ron_core::frontend::prepare;
                use con_ron_core::frontend::prelude::builtin_prelude_e;
                use con_ron_core::kernel::{name, pins_decode};
                use con_ron_core::ron::hashmap::Dup;

                fn ok<T, E>(r: Result<T, E>, msg: &str) -> T {
                    match r {
                        Ok(v) => v,
                        Err(_) => panic!("{msg}"),
                    }
                }

                let build_thm = |bad: bool| -> LoadedEnvironment {
                    let empty_pers = PersTier::empty();
                    let mut st = AState::init(EStore::empty());
                    ok(intern_reserved_pins(&empty_pers, &mut st), "pins");
                    let prelude_ix = ok(builtin_prelude_e(&empty_pers, &mut st), "prelude");
                    let zero_l = ok(pin_zero_level(&mut st), "zero_l");
                    let prop_e = ok(intern_e_sort(&empty_pers, &mut st, zero_l), "prop");
                    let (ty, val) = if bad {
                        // Prop : Type 0 != Prop -> ill-typed theorem proof
                        (prop_e.dup2(), prop_e)
                    } else {
                        let b0 = ok(intern_e_bvar(&empty_pers, &mut st, 0), "b0");
                        let b1 = ok(intern_e_bvar(&empty_pers, &mut st, 1), "b1");
                        let inner_ty = ok(intern_e_forall_e(&empty_pers, &mut st, b0.dup2(), b1), "inner_ty");
                        let full_ty =
                            ok(intern_e_forall_e(&empty_pers, &mut st, prop_e.dup2(), inner_ty), "full_ty");
                        let inner_lam = ok(intern_e_lam(&empty_pers, &mut st, b0.dup2(), b0), "inner_lam");
                        let full_lam = ok(intern_e_lam(&empty_pers, &mut st, prop_e, inner_lam), "full_lam");
                        (full_ty, full_lam)
                    };
                    let mut nm = name::anonymous();
                    nm = name::mk_str(nm, "Snap".chars().map(|c| c as u32).collect());
                    nm = name::mk_str(
                        nm,
                        (if bad { "bad_prop" } else { "id_prop" })
                            .chars()
                            .map(|c| c as u32)
                            .collect(),
                    );
                    let nidx = ok(intern_name(&empty_pers, &mut st, &nm), "intern_name");
                    let decls = vec![IDeclaration::ThmDecl(
                        IConstantVal {
                            name: nidx,
                            level_params: Vec::new(),
                            ty,
                        },
                        val,
                    )];
                    let prepared = ok(
                        prepare::prepare_d(&empty_pers, &mut st, prelude_ix, decls, &DeclUsedConsts),
                        "prepare_d",
                    );
                    let file_records = prepared.decls.len();
                    let pins_decoded = ok(pins_decode::decode_embedded(), "pins_decode");
                    let max_nat = max_nat_size_default();
                    let ipins = ok(
                        checker::intern_all_pins(&empty_pers, &mut st, &pins_decoded, &max_nat),
                        "intern_all_pins",
                    );
                    let ix = ok(
                        stream_index::build_index(
                            &empty_pers,
                            &mut st,
                            stream_index::stream_index_empty(),
                            &prepared.decls,
                            0,
                        ),
                        "build_index",
                    );
                    let pers = checker::freeze_tier(&mut st.store, ix);
                    LoadedEnvironment {
                        pers,
                        pins: st.pins,
                        ipins,
                        decls: prepared.decls,
                        file_records,
                        synthesized: prepared.synthesised,
                        hoisted: prepared.hoisted.len(),
                        olean: None,
                        load_ns: 0,
                        materialize_ns: 0,
                        index_ns: 0,
                        thm_materialized_count: 0,
                        closure_fingerprint: None,
                        closure_roots: Vec::new(),
                        closure_manifest: Vec::new(),
                        module_hashes: std::collections::HashMap::new(),
                        preverified_prefix: 0,
                    }
                };

                let ctx = GpuContext::shared_vulkan_high_perf().expect("Vulkan GPU required");
                let pipe = TypecheckGpuPipeline::new(&ctx);

                // 1. 100%-GPU verified theorem slice (after synthesized prelude) -> lazy_loader MUST NOT be called.
                let pure_env = build_thm(false);
                let pure_start = pure_env.decls.len() - 1;
                let pure_pkt =
                    con_gpu_arena::soa_pack::pack_arena_from(&pure_env, ArenaLimitsConfig::default(), pure_start);
                let calls = AtomicUsize::new(0);
                let pure_rep = pipe
                    .verify_snapshot_hybrid_with(
                        &ctx,
                        &pure_pkt,
                        pure_env.file_records,
                        Some(2),
                        pure_start,
                        VerifyOptions::default(),
                        || {
                            calls.fetch_add(1, Ordering::SeqCst);
                            Ok(build_thm(false))
                        },
                    )
                    .expect("snapshot pure verify");
                assert!(
                    matches!(pure_rep.verdict, VerificationVerdict::Accepted { .. }),
                    "{:?}",
                    pure_rep.verdict
                );
                assert_eq!(pure_rep.gpu_verified_count, 1);
                assert_eq!(pure_rep.delegated_count, 0);
                assert_eq!(
                    calls.load(Ordering::SeqCst),
                    0,
                    "100% GPU snapshot verification must skip lazy_loader"
                );

                // 2. Ill-typed theorem slice rejected by GPU -> lazy_loader invoked once to cross-check & reject.
                let bad_env = build_thm(true);
                let bad_start = bad_env.decls.len() - 1;
                let bad_pkt =
                    con_gpu_arena::soa_pack::pack_arena_from(&bad_env, ArenaLimitsConfig::default(), bad_start);
                let calls = AtomicUsize::new(0);
                let bad_rep = pipe
                    .verify_snapshot_hybrid_with(
                        &ctx,
                        &bad_pkt,
                        bad_env.file_records,
                        Some(2),
                        bad_start,
                        VerifyOptions::default(),
                        || {
                            calls.fetch_add(1, Ordering::SeqCst);
                            Ok(build_thm(true))
                        },
                    )
                    .expect("snapshot bad verify");
                assert!(
                    matches!(bad_rep.verdict, VerificationVerdict::Rejected { .. }),
                    "{:?}",
                    bad_rep.verdict
                );
                assert_eq!(bad_rep.gpu_rejected_count, 1);
                assert_eq!(
                    calls.load(Ordering::SeqCst),
                    1,
                    "GPU-rejected snapshot must invoke lazy_loader once"
                );

                // 3. Init/Prelude.olean via snapshot -> lazy_loader invoked once concurrently with GPU & Accepted.
                let prelude_path = Path::new(
                    "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean/Init/Prelude.olean",
                );
                if prelude_path.exists() {
                    let sp = vec![std::path::PathBuf::from(
                        "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean",
                    )];
                    let spec = build_olean_input(
                        &[prelude_path.to_string_lossy().into_owned()],
                        &sp,
                        None,
                        true,
                    );
                    let env = load_environment(&spec).expect("load Prelude");
                    let pkt = pack_arena(&env, ArenaLimitsConfig::default());
                    let calls = AtomicUsize::new(0);
                    let rep = pipe
                        .verify_snapshot_hybrid_with(
                            &ctx,
                            &pkt,
                            env.file_records,
                            Some(4),
                            0,
                            VerifyOptions::default(),
                            || {
                                calls.fetch_add(1, Ordering::SeqCst);
                                load_environment(&spec)
                            },
                        )
                        .expect("snapshot Prelude verify");
                    assert!(matches!(rep.verdict, VerificationVerdict::Accepted { .. }), "{:?}", rep.verdict);
                    assert_eq!(calls.load(Ordering::SeqCst), 1);
                }
            })
            .expect("spawn")
            .join()
            .expect("join");
    }

    #[test]
    fn wave_j_gpu_nat_pow_gcd_zero_eta_and_opaque_spine_verified_and_sound() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                use con_ron_core::arena::checker;
                use con_ron_core::arena::env::{IConstantVal, IDeclaration};
                use con_ron_core::arena::monad::{
                    intern_e_app, intern_e_bvar, intern_e_const, intern_e_forall_e, intern_e_lam,
                    intern_e_lit, intern_l_node, intern_ls_node, intern_name, AState,
                };
                use con_ron_core::arena::pins::{
                    intern_reserved_pins, max_nat_size_default, pin_empty_levels, pin_eq,
                    pin_nat, pin_nat_add, pin_nat_gcd, pin_nat_pow, pin_zero_level,
                };
                use con_ron_core::arena::store::{EStore, LNodeView, PersTier};
                use con_ron_core::arena::stream_index;
                use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
                use con_ron_core::frontend::olean::records::read_oleans_full;
                use con_ron_core::frontend::prepare::{self, PreludeIx};
                use con_ron_core::frontend::prelude::builtin_prelude_e;
                use con_ron_core::kernel::env::ReducibilityHint;
                use con_ron_core::kernel::expr::literal_nat;
                use con_ron_core::kernel::{name, pins_decode};
                use con_ron_core::ron::hashmap::Dup;
                use con_ron_core::ron::nat::Nat as RonNat;

                fn ok<T, E>(r: Result<T, E>, msg: &str) -> T {
                    match r {
                        Ok(v) => v,
                        Err(_) => panic!("{msg}"),
                    }
                }
                fn segs(pers: &PersTier, st: &mut AState, xs: &[&str]) -> con_ron_core::arena::handle::NIdx {
                    let mut acc = name::anonymous();
                    for &s in xs {
                        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
                        acc = name::mk_str(acc, cps);
                    }
                    ok(intern_name(pers, st, &acc), "intern_name")
                }
                fn finish(
                    empty_pers: &PersTier,
                    mut st: AState,
                    prelude_ix: PreludeIx,
                    decls: Vec<IDeclaration>,
                ) -> LoadedEnvironment {
                    let file_records = decls.len();
                    let prepared = ok(
                        prepare::prepare_d(empty_pers, &mut st, prelude_ix, decls, &DeclUsedConsts),
                        "prepare_d",
                    );
                    let pins_dec = ok(pins_decode::decode_embedded(), "decode pins");
                    let ipins = ok(
                        checker::intern_all_pins(empty_pers, &mut st, &pins_dec, &max_nat_size_default()),
                        "intern_all_pins",
                    );
                    let ix = ok(
                        stream_index::build_index(
                            empty_pers,
                            &mut st,
                            stream_index::stream_index_empty(),
                            &prepared.decls,
                            0,
                        ),
                        "build_index",
                    );
                    let pers = checker::freeze_tier(&mut st.store, ix);
                    LoadedEnvironment {
                        pers,
                        pins: st.pins,
                        ipins,
                        decls: prepared.decls,
                        file_records,
                        synthesized: prepared.synthesised,
                        hoisted: prepared.hoisted.len(),
                        olean: None,
                        load_ns: 0,
                        materialize_ns: 0,
                        index_ns: 0,
                        thm_materialized_count: 0,
                        closure_fingerprint: None,
                        closure_roots: Vec::new(),
                        closure_manifest: Vec::new(),
                        module_hashes: std::collections::HashMap::new(),
                        preverified_prefix: 0,
                    }
                }
                let ap = |pers: &PersTier,
                          st: &mut AState,
                          mut f: con_ron_core::arena::handle::EIdx,
                          args: &[con_ron_core::arena::handle::EIdx]| {
                    for a in args {
                        f = ok(intern_e_app(pers, st, f, a.dup2()), "app");
                    }
                    f
                };
                let lit_u64 = |pers: &PersTier, st: &mut AState, v: u64| {
                    let nat = if v == 0 {
                        RonNat { limbs: Vec::new() }
                    } else {
                        RonNat { limbs: vec![v] }
                    };
                    ok(intern_e_lit(pers, st, literal_nat(nat)), "lit")
                };

                let ctx = GpuContext::shared_vulkan_high_perf().expect("Vulkan GPU required");
                let pipe = TypecheckGpuPipeline::new(&ctx);
                let lean_lib = "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean";
                if !Path::new(lean_lib).join("Init/Prelude.olean").exists() {
                    return;
                }

                // 1. Real `Init.Prelude` (`PUnit` 0-field structure eta) + `Opaque`/`Abbrev` same-head spine + negative case
                let build_struct_and_spine = |bad_opaque: bool| -> LoadedEnvironment {
                    let empty_pers = PersTier::empty();
                    let mut st = AState::init(EStore::empty());
                    ok(intern_reserved_pins(&empty_pers, &mut st), "pins");
                    let prelude_ix = ok(builtin_prelude_e(&empty_pers, &mut st), "prelude");
                    let sp = vec![con_gpu_arena::fs::str_to_cp(lean_lib)];
                    let roots = vec![segs(&empty_pers, &mut st, &["Init", "Prelude"])];
                    let mut decls = ok(
                        read_oleans_full(
                            &con_gpu_arena::fs::StdFs,
                            &empty_pers,
                            &mut st.store,
                            &sp,
                            &roots,
                            &None,
                        ),
                        "read Prelude.olean",
                    );
                    let empty_ls = ok(pin_empty_levels(&st), "empty_ls");
                    let zero_l = ok(pin_zero_level(&mut st), "zero_l");
                    let one_l = ok(intern_l_node(&empty_pers, &mut st, LNodeView::Succ(zero_l)), "one_l");
                    let one_ls = ok(intern_ls_node(&empty_pers, &mut st, vec![one_l]), "one_ls");
                    let n_nat = ok(pin_nat(&st), "Nat");
                    let nat_e = ok(intern_e_const(&empty_pers, &mut st, n_nat, empty_ls.dup2()), "Nat");
                    let n_add = ok(pin_nat_add(&st), "Nat.add");
                    let add_e = ok(intern_e_const(&empty_pers, &mut st, n_add, empty_ls), "Nat.add");
                    let n_eq = ok(pin_eq(&st), "Eq");
                    let eq_1 = ok(intern_e_const(&empty_pers, &mut st, n_eq, one_ls.dup2()), "Eq");
                    let n_eq_refl = segs(&empty_pers, &mut st, &["Eq", "refl"]);
                    let eq_refl_1 = ok(intern_e_const(&empty_pers, &mut st, n_eq_refl, one_ls.dup2()), "Eq.refl");
                    let n_punit = segs(&empty_pers, &mut st, &["PUnit"]);
                    let punit_1 = ok(intern_e_const(&empty_pers, &mut st, n_punit, one_ls.dup2()), "PUnit");
                    let n_punit_unit = segs(&empty_pers, &mut st, &["PUnit", "unit"]);
                    let punit_unit_1 = ok(intern_e_const(&empty_pers, &mut st, n_punit_unit, one_ls), "PUnit.unit");
                    let b0 = ok(intern_e_bvar(&empty_pers, &mut st, 0), "b0");
                    let l2 = lit_u64(&empty_pers, &mut st, 2);
                    let l3 = lit_u64(&empty_pers, &mut st, 3);
                    let l5 = lit_u64(&empty_pers, &mut st, 5);
                    let l6 = lit_u64(&empty_pers, &mut st, 6);

                    // `op_id (x : Nat) : Nat := x` (`@[irreducible]` / `Opaque` hint) and `ab_id` (`Abbrev` hint)
                    let nat_to_nat = ok(intern_e_forall_e(&empty_pers, &mut st, nat_e.dup2(), nat_e.dup2()), "Nat->Nat");
                    let id_fn = ok(intern_e_lam(&empty_pers, &mut st, nat_e.dup2(), b0.dup2()), "id_fn");
                    let op_n = segs(&empty_pers, &mut st, &["WaveJ", "op_id"]);
                    let ab_n = segs(&empty_pers, &mut st, &["WaveJ", "ab_id"]);
                    let op_decl = IDeclaration::DefnDecl(
                        IConstantVal { name: op_n.dup2(), level_params: Vec::new(), ty: nat_to_nat.dup2() },
                        id_fn.dup2(),
                        ReducibilityHint::Opaque,
                    );
                    let ab_decl = IDeclaration::DefnDecl(
                        IConstantVal { name: ab_n.dup2(), level_params: Vec::new(), ty: nat_to_nat },
                        id_fn,
                        ReducibilityHint::Abbrev,
                    );

                    let empty_ls2 = ok(pin_empty_levels(&st), "empty_ls2");
                    let op_c = ok(intern_e_const(&empty_pers, &mut st, op_n, empty_ls2.dup2()), "op_c");
                    let ab_c = ok(intern_e_const(&empty_pers, &mut st, ab_n, empty_ls2), "ab_c");

                    // 0-field eta theorem: forall (x : PUnit.{1}), Eq PUnit.{1} x PUnit.unit.{1} := fun x => Eq.refl PUnit.{1} x
                    let eq_u = ap(&empty_pers, &mut st, eq_1.dup2(), &[punit_1.dup2(), b0.dup2(), punit_unit_1]);
                    let eta_ty = ok(intern_e_forall_e(&empty_pers, &mut st, punit_1.dup2(), eq_u), "eta_ty");
                    let refl_u_b0 = ap(&empty_pers, &mut st, eq_refl_1.dup2(), &[punit_1.dup2(), b0]);
                    let eta_val = ok(intern_e_lam(&empty_pers, &mut st, punit_1, refl_u_b0), "eta_val");
                    let eta_thm = IDeclaration::ThmDecl(
                        IConstantVal { name: segs(&empty_pers, &mut st, &["WaveJ", "zero_field_eta"]), level_params: Vec::new(), ty: eta_ty },
                        eta_val,
                    );

                    let two_plus_three = ap(&empty_pers, &mut st, add_e, &[l2, l3]);
                    let op_2_3 = ap(&empty_pers, &mut st, op_c.dup2(), &[two_plus_three.dup2()]);
                    let op_5 = ap(&empty_pers, &mut st, op_c.dup2(), &[l5.dup2()]);
                    let op_6 = ap(&empty_pers, &mut st, op_c, &[l6]);
                    let ab_2_3 = ap(&empty_pers, &mut st, ab_c.dup2(), &[two_plus_three]);
                    let ab_5 = ap(&empty_pers, &mut st, ab_c, &[l5]);

                    let op_thm = if bad_opaque {
                        let ty = ap(&empty_pers, &mut st, eq_1.dup2(), &[nat_e.dup2(), op_5.dup2(), op_6]);
                        let pr = ap(&empty_pers, &mut st, eq_refl_1.dup2(), &[nat_e.dup2(), op_5]);
                        IDeclaration::ThmDecl(
                            IConstantVal { name: segs(&empty_pers, &mut st, &["WaveJ", "bad_opaque_spine"]), level_params: Vec::new(), ty },
                            pr,
                        )
                    } else {
                        let ty = ap(&empty_pers, &mut st, eq_1.dup2(), &[nat_e.dup2(), op_2_3, op_5.dup2()]);
                        let pr = ap(&empty_pers, &mut st, eq_refl_1.dup2(), &[nat_e.dup2(), op_5]);
                        IDeclaration::ThmDecl(
                            IConstantVal { name: segs(&empty_pers, &mut st, &["WaveJ", "opaque_spine"]), level_params: Vec::new(), ty },
                            pr,
                        )
                    };
                    let ab_thm = IDeclaration::ThmDecl(
                        IConstantVal {
                            name: segs(&empty_pers, &mut st, &["WaveJ", "abbrev_spine"]),
                            level_params: Vec::new(),
                            ty: ap(&empty_pers, &mut st, eq_1, &[nat_e.dup2(), ab_2_3, ab_5.dup2()]),
                        },
                        ap(&empty_pers, &mut st, eq_refl_1, &[nat_e, ab_5]),
                    );

                    decls.extend([op_decl, ab_decl, eta_thm, op_thm, ab_thm]);
                    finish(&empty_pers, st, prelude_ix, decls)
                };

                let good_ss = build_struct_and_spine(false);
                let good_start = good_ss.decls.len() - 5;
                let (h_ok, _) = verify_host_parallel(&good_ss, Some(4));
                assert!(matches!(h_ok, VerificationVerdict::Accepted { .. }), "{h_ok:?}");
                let good_pkt = con_gpu_arena::soa_pack::pack_arena_from(&good_ss, ArenaLimitsConfig::default(), good_start);
                let g_rep = pipe
                    .verify_packet_hybrid_range_with(&ctx, &good_ss, &good_pkt, Some(4), good_start, VerifyOptions::default())
                    .expect("WaveJ struct/spine GPU");
                assert!(matches!(g_rep.verdict, VerificationVerdict::Accepted { .. }), "{:?}", g_rep.verdict);
                assert_eq!(g_rep.gpu_verified_count, 5, "op_decl/ab_decl + zero-field PUnit eta + opaque/abbrev spine must verify on GPU: {g_rep:?}");
                assert_eq!(g_rep.delegated_count, 0);

                let bad_ss = build_struct_and_spine(true);
                let bad_start = bad_ss.decls.len() - 5;
                let (h_bad, _) = verify_host_parallel(&bad_ss, Some(4));
                assert!(matches!(h_bad, VerificationVerdict::Rejected { .. }), "{h_bad:?}");
                let bad_pkt = con_gpu_arena::soa_pack::pack_arena_from(&bad_ss, ArenaLimitsConfig::default(), bad_start);
                let b_rep = pipe
                    .verify_packet_hybrid_range_with(&ctx, &bad_ss, &bad_pkt, Some(4), bad_start, VerifyOptions::default())
                    .expect("WaveJ bad opaque GPU");
                assert!(matches!(b_rep.verdict, VerificationVerdict::Rejected { .. }), "{:?}", b_rep.verdict);
                assert_eq!(b_rep.gpu_rejected_count, 1);

                // 2. Real Init.Data.Nat.Gcd (includes Nat.pow and Nat.gcd): exact GPU reduction & overflow delegation
                if Path::new(lean_lib).join("Init/Data/Nat/Gcd.olean").exists() {
                    let build_gcd_env = |bad: bool| -> LoadedEnvironment {
                        let empty_pers = PersTier::empty();
                        let mut st = AState::init(EStore::empty());
                        ok(intern_reserved_pins(&empty_pers, &mut st), "pins");
                        let prelude_ix = ok(builtin_prelude_e(&empty_pers, &mut st), "prelude");
                        let sp = vec![con_gpu_arena::fs::str_to_cp(lean_lib)];
                        let roots = vec![segs(&empty_pers, &mut st, &["Init", "Data", "Nat", "Gcd"])];
                        let mut decls = ok(
                            read_oleans_full(
                                &con_gpu_arena::fs::StdFs,
                                &empty_pers,
                                &mut st.store,
                                &sp,
                                &roots,
                                &None,
                            ),
                            "read Gcd.olean",
                        );
                        let empty_ls = ok(pin_empty_levels(&st), "empty_ls");
                        let zero_l = ok(pin_zero_level(&mut st), "zero_l");
                        let one_l = ok(intern_l_node(&empty_pers, &mut st, LNodeView::Succ(zero_l)), "one_l");
                        let one_ls = ok(intern_ls_node(&empty_pers, &mut st, vec![one_l]), "one_ls");
                        let n_nat = ok(pin_nat(&st), "Nat");
                        let nat_e = ok(intern_e_const(&empty_pers, &mut st, n_nat, empty_ls.dup2()), "Nat");
                        let n_eq = ok(pin_eq(&st), "Eq");
                        let eq_1 = ok(intern_e_const(&empty_pers, &mut st, n_eq, one_ls.dup2()), "Eq");
                        let n_eq_refl = segs(&empty_pers, &mut st, &["Eq", "refl"]);
                        let eq_refl_1 = ok(intern_e_const(&empty_pers, &mut st, n_eq_refl, one_ls), "Eq.refl");
                        let n_pow = ok(pin_nat_pow(&st), "Nat.pow");
                        let pow_c = ok(intern_e_const(&empty_pers, &mut st, n_pow, empty_ls.dup2()), "Nat.pow");
                        let n_gcd = ok(pin_nat_gcd(&st), "Nat.gcd");
                        let gcd_c = ok(intern_e_const(&empty_pers, &mut st, n_gcd, empty_ls), "Nat.gcd");

                        let l0 = lit_u64(&empty_pers, &mut st, 0);
                        let l1 = lit_u64(&empty_pers, &mut st, 1);
                        let l2 = lit_u64(&empty_pers, &mut st, 2);
                        let l10 = lit_u64(&empty_pers, &mut st, 10);
                        let l18 = lit_u64(&empty_pers, &mut st, 18);
                        let l48 = lit_u64(&empty_pers, &mut st, 48);
                        let l65 = lit_u64(&empty_pers, &mut st, 65);
                        let l6 = lit_u64(&empty_pers, &mut st, 6);
                        let l7 = lit_u64(&empty_pers, &mut st, 7);
                        let l1024 = lit_u64(&empty_pers, &mut st, 1024);
                        let l_pow40 = 1u64 << 40;
                        let l_g1 = lit_u64(&empty_pers, &mut st, l_pow40 * 3);
                        let l_g2 = lit_u64(&empty_pers, &mut st, l_pow40 * 5);
                        let l_g_res = lit_u64(&empty_pers, &mut st, l_pow40);
                        let big_2_65 = ok(
                            intern_e_lit(&empty_pers, &mut st, literal_nat(RonNat { limbs: vec![0, 2] })),
                            "2^65",
                        );

                        let push_eq = |st: &mut AState,
                                       decls: &mut Vec<IDeclaration>,
                                       name_s: &str,
                                       lhs: con_ron_core::arena::handle::EIdx,
                                       rhs: con_ron_core::arena::handle::EIdx| {
                            let ty = ap(&empty_pers, st, eq_1.dup2(), &[nat_e.dup2(), lhs, rhs.dup2()]);
                            let pr = ap(&empty_pers, st, eq_refl_1.dup2(), &[nat_e.dup2(), rhs]);
                            decls.push(IDeclaration::ThmDecl(
                                IConstantVal { name: segs(&empty_pers, st, &["WaveJ", name_s]), level_params: Vec::new(), ty },
                                pr,
                            ));
                        };

                        if bad {
                            let lhs = ap(&empty_pers, &mut st, gcd_c, &[l48, l18]);
                            push_eq(&mut st, &mut decls, "bad_gcd", lhs, l7);
                        } else {
                            let p1 = ap(&empty_pers, &mut st, pow_c.dup2(), &[l2.dup2(), l10]);
                            push_eq(&mut st, &mut decls, "pow_2_10", p1, l1024);
                            let p2_r = lit_u64(&empty_pers, &mut st, 1);
                            let p2_l = ap(&empty_pers, &mut st, pow_c.dup2(), &[l1, l65.dup2()]);
                            push_eq(&mut st, &mut decls, "pow_1_big", p2_l, p2_r);
                            let p3_z = lit_u64(&empty_pers, &mut st, 0);
                            let p3_r = lit_u64(&empty_pers, &mut st, 1);
                            let p3_l = ap(&empty_pers, &mut st, pow_c.dup2(), &[l0, p3_z]);
                            push_eq(&mut st, &mut decls, "pow_0_0", p3_l, p3_r);
                            let g1 = ap(&empty_pers, &mut st, gcd_c.dup2(), &[l48, l18]);
                            push_eq(&mut st, &mut decls, "gcd_48_18", g1, l6);
                            let g2 = ap(&empty_pers, &mut st, gcd_c, &[l_g1, l_g2]);
                            push_eq(&mut st, &mut decls, "gcd_u64", g2, l_g_res);
                            // 2^65 overflows 64 bits -> cleanly delegates to host exact evaluator & passes!
                            let p4 = ap(&empty_pers, &mut st, pow_c, &[l2, l65]);
                            push_eq(&mut st, &mut decls, "pow_2_65_ovf", p4, big_2_65);
                        }
                        finish(&empty_pers, st, prelude_ix, decls)
                    };

                    let ok_env = build_gcd_env(false);
                    let start = ok_env.decls.len() - 6;
                    let pkt = con_gpu_arena::soa_pack::pack_arena_from(&ok_env, ArenaLimitsConfig::default(), start);
                    let rep = pipe
                        .verify_packet_hybrid_range_with(&ctx, &ok_env, &pkt, Some(4), start, VerifyOptions::default())
                        .expect("WaveJ Nat pow/gcd GPU");
                    assert!(matches!(rep.verdict, VerificationVerdict::Accepted { .. }), "{:?}", rep.verdict);
                    assert_eq!(rep.gpu_verified_count, 5, "5 u64 pow/gcd theorems must verify on GPU: {rep:?}");
                    assert_eq!(rep.delegated_count, 1, "2^65 overflow must delegate once cleanly: {rep:?}");

                    let bad_env = build_gcd_env(true);
                    let bstart = bad_env.decls.len() - 1;
                    let bpkt = con_gpu_arena::soa_pack::pack_arena_from(&bad_env, ArenaLimitsConfig::default(), bstart);
                    let brep = pipe
                        .verify_packet_hybrid_range_with(&ctx, &bad_env, &bpkt, Some(4), bstart, VerifyOptions::default())
                        .expect("WaveJ bad gcd GPU");
                    assert!(matches!(brep.verdict, VerificationVerdict::Rejected { .. }), "{:?}", brep.verdict);
                    assert_eq!(brep.gpu_rejected_count, 1);
                }
            })
            .expect("spawn")
            .join()
            .expect("join");
    }

    #[test]
    fn paged_e_nodes_8gb_reader_handles_page_crossing_above_2_28() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let lean_lib = "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean";
                if !Path::new(lean_lib).join("Init/Prelude.olean").exists() {
                    return;
                }
                use con_ron_core::arena::checker;
                use con_ron_core::arena::env::{IConstantVal, IDeclaration};
                use con_ron_core::arena::monad::{
                    intern_e_app, intern_e_const, intern_e_lit, intern_l_node, intern_ls_node,
                    intern_name, AState,
                };
                use con_ron_core::arena::pins::{
                    intern_reserved_pins, max_nat_size_default, pin_empty_levels, pin_eq, pin_nat,
                    pin_nat_add, pin_zero_level,
                };
                use con_ron_core::arena::store::{EStore, LNodeView, PersTier};
                use con_ron_core::arena::stream_index;
                use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
                use con_ron_core::frontend::olean::records::read_oleans_full;
                use con_ron_core::frontend::prepare;
                use con_ron_core::frontend::prelude::builtin_prelude_e;
                use con_ron_core::kernel::expr::literal_nat;
                use con_ron_core::kernel::{name, pins_decode};
                use con_ron_core::ron::hashmap::Dup;
                use con_ron_core::ron::nat::Nat as RonNat;

                fn ok<T, E>(r: Result<T, E>, msg: &str) -> T {
                    match r {
                        Ok(v) => v,
                        Err(_) => panic!("{msg}"),
                    }
                }
                fn segs(pers: &PersTier, st: &mut AState, parts: &[&str]) -> con_ron_core::arena::handle::NIdx {
                    let mut acc = name::anonymous();
                    for &s in parts {
                        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
                        acc = name::mk_str(acc, cps);
                    }
                    ok(intern_name(pers, st, &acc), "intern_name")
                }

                let build_thm = |bad: bool| -> LoadedEnvironment {
                    let empty_pers = PersTier::empty();
                    let mut st = AState::init(EStore::empty());
                    ok(intern_reserved_pins(&empty_pers, &mut st), "pins");
                    let prelude_ix = ok(builtin_prelude_e(&empty_pers, &mut st), "prelude");
                    let sp = vec![con_gpu_arena::fs::str_to_cp(lean_lib)];
                    let roots = vec![segs(&empty_pers, &mut st, &["Init", "Prelude"])];
                    let mut decls = ok(
                        read_oleans_full(&con_gpu_arena::fs::StdFs, &empty_pers, &mut st.store, &sp, &roots, &None),
                        "read Prelude",
                    );
                    let empty_ls = ok(pin_empty_levels(&st), "empty_ls");
                    let zero_l = ok(pin_zero_level(&st), "zero_l");
                    let one_l = ok(intern_l_node(&empty_pers, &mut st, LNodeView::Succ(zero_l)), "one_l");
                    let one_ls = ok(intern_ls_node(&empty_pers, &mut st, vec![one_l]), "one_ls");
                    let n_nat = ok(pin_nat(&st), "Nat");
                    let n_eq = ok(pin_eq(&st), "Eq");
                    let n_eq_refl = segs(&empty_pers, &mut st, &["Eq", "refl"]);
                    let n_add = ok(pin_nat_add(&st), "add");
                    let nat_e = ok(intern_e_const(&empty_pers, &mut st, n_nat, empty_ls.dup2()), "Nat");
                    let eq_1 = ok(intern_e_const(&empty_pers, &mut st, n_eq, one_ls.dup2()), "Eq");
                    let eq_refl_1 = ok(intern_e_const(&empty_pers, &mut st, n_eq_refl, one_ls), "Eq.refl");
                    let l2 = ok(intern_e_lit(&empty_pers, &mut st, literal_nat(RonNat { limbs: vec![2] })), "2");
                    let l3 = ok(intern_e_lit(&empty_pers, &mut st, literal_nat(RonNat { limbs: vec![3] })), "3");
                    let l5 = ok(intern_e_lit(&empty_pers, &mut st, literal_nat(RonNat { limbs: vec![5] })), "5");
                    let l6 = ok(intern_e_lit(&empty_pers, &mut st, literal_nat(RonNat { limbs: vec![6] })), "6");
                    let add_c = ok(intern_e_const(&empty_pers, &mut st, n_add, empty_ls), "add");
                    let a1 = ok(intern_e_app(&empty_pers, &mut st, add_c, l2), "app1");
                    let lhs = ok(intern_e_app(&empty_pers, &mut st, a1, l3), "app2");
                    let rhs = if bad { l6 } else { l5.dup2() };
                    let eq_a = ok(intern_e_app(&empty_pers, &mut st, eq_1, nat_e.dup2()), "eq1");
                    let eq_b = ok(intern_e_app(&empty_pers, &mut st, eq_a, lhs), "eq2");
                    let ty = ok(intern_e_app(&empty_pers, &mut st, eq_b, rhs), "ty");
                    let rf1 = ok(intern_e_app(&empty_pers, &mut st, eq_refl_1, nat_e), "rf1");
                    let pr = ok(intern_e_app(&empty_pers, &mut st, rf1, l5), "pr");
                    let nm = segs(&empty_pers, &mut st, &["PageCrossThm"]);
                    decls.push(IDeclaration::ThmDecl(IConstantVal { name: nm, level_params: Vec::new(), ty }, pr));

                    let prepared = ok(prepare::prepare_d(&empty_pers, &mut st, prelude_ix, decls, &DeclUsedConsts), "prep");
                    let file_records = prepared.decls.len();
                    let pins_decoded = ok(pins_decode::decode_embedded(), "pins_dec");
                    let ipins = ok(checker::intern_all_pins(&empty_pers, &mut st, &pins_decoded, &max_nat_size_default()), "ipins");
                    let ix = ok(stream_index::build_index(&empty_pers, &mut st, stream_index::stream_index_empty(), &prepared.decls, 0), "idx");
                    let pers = checker::freeze_tier(&mut st.store, ix);
                    LoadedEnvironment {
                        pers,
                        pins: st.pins,
                        ipins,
                        decls: prepared.decls,
                        file_records,
                        synthesized: prepared.synthesised,
                        hoisted: prepared.hoisted.len(),
                        olean: None,
                        load_ns: 0,
                        materialize_ns: 0,
                        index_ns: 0,
                        thm_materialized_count: 0,
                        closure_fingerprint: None,
                        closure_roots: Vec::new(),
                        closure_manifest: Vec::new(),
                        module_hashes: std::collections::HashMap::new(),
                        preverified_prefix: 0,
                    }
                };

                let shift_packet_to_page1 = |mut pkt: GpuArenaPacket| -> GpuArenaPacket {
                    let split_off = pkt.header.off_app as usize;
                    let orig_len = pkt.e_nodes.len();
                    let mut paged = vec![0u32; E_NODES_PAGE_WORDS + orig_len];
                    paged[..split_off].copy_from_slice(&pkt.e_nodes[..split_off]);
                    paged[E_NODES_PAGE_WORDS + split_off..E_NODES_PAGE_WORDS + orig_len]
                        .copy_from_slice(&pkt.e_nodes[split_off..orig_len]);
                    let d = E_NODES_PAGE_WORDS as u32;
                    pkt.header.off_app += d;
                    pkt.header.off_app_der += d;
                    pkt.header.off_lam += d;
                    pkt.header.off_lam_der += d;
                    pkt.header.off_forall += d;
                    pkt.header.off_forall_der += d;
                    pkt.header.off_let += d;
                    pkt.header.off_let_der += d;
                    pkt.header.off_lit += d;
                    pkt.header.off_lit_der += d;
                    pkt.header.off_proj += d;
                    pkt.header.off_proj_der += d;
                    pkt.header.e_nodes_len = paged.len() as u32;
                    pkt.e_nodes = paged;
                    pkt
                };

                let ctx = GpuContext::shared_vulkan_high_perf().expect("Vulkan GPU required");
                let pipe = TypecheckGpuPipeline::new(&ctx);

                let env_ok = build_thm(false);
                let start = env_ok.decls.len() - 1;
                let pkt_ok = shift_packet_to_page1(con_gpu_arena::soa_pack::pack_arena_from(
                    &env_ok,
                    ArenaLimitsConfig::default(),
                    start,
                ));
                assert!(pkt_ok.header.off_lit as usize >= E_NODES_PAGE_WORDS);
                let rep = pipe
                    .verify_snapshot_hybrid_with(
                        &ctx,
                        &pkt_ok,
                        env_ok.file_records,
                        Some(4),
                        start,
                        VerifyOptions::default(),
                        || -> Result<LoadedEnvironment, VerificationVerdict> {
                            panic!("paged e_nodes theorem must verify 100% on GPU without delegating");
                        },
                    )
                    .expect("paged GPU verify");
                assert!(matches!(rep.verdict, VerificationVerdict::Accepted { .. }), "{:?}", rep.verdict);
                assert_eq!(rep.gpu_verified_count, 1);
                assert_eq!(rep.delegated_count, 0);

                let env_bad = build_thm(true);
                let bstart = env_bad.decls.len() - 1;
                let bfile_records = env_bad.file_records;
                let pkt_bad = shift_packet_to_page1(con_gpu_arena::soa_pack::pack_arena_from(
                    &env_bad,
                    ArenaLimitsConfig::default(),
                    bstart,
                ));
                let brep = pipe
                    .verify_snapshot_hybrid_with(
                        &ctx,
                        &pkt_bad,
                        bfile_records,
                        Some(4),
                        bstart,
                        VerifyOptions::default(),
                        move || Ok(env_bad),
                    )
                    .expect("paged GPU reject");
                assert!(matches!(brep.verdict, VerificationVerdict::Rejected { .. }), "{:?}", brep.verdict);
                assert_eq!(brep.gpu_rejected_count, 1);
                assert_eq!(brep.delegated_count, 0);
            })
            .expect("spawn")
            .join()
            .expect("join");
    }

    #[test]
    fn gpu_bignat_256bit_and_string_lit_equality_without_delegation() {
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let lean_lib = "C:/Users/devin/.elan/toolchains/leanprover--lean4---v4.35.0/lib/lean";
                if !Path::new(lean_lib).join("Init/Data/Nat/Bitwise/Basic.olean").exists() {
                    return;
                }
                use con_ron_core::arena::checker;
                use con_ron_core::arena::env::{IConstantVal, IDeclaration};
                use con_ron_core::arena::handle::{EIdx, NIdx};
                use con_ron_core::arena::monad::{
                    intern_e_app, intern_e_const, intern_e_lit, intern_l_node, intern_ls_node,
                    intern_name, AState,
                };
                use con_ron_core::arena::pins::{
                    intern_reserved_pins, max_nat_size_default, pin_bool, pin_bool_false,
                    pin_bool_true, pin_empty_levels, pin_eq, pin_nat, pin_nat_add, pin_nat_beq,
                    pin_nat_ble, pin_nat_land, pin_nat_lor, pin_nat_mul, pin_nat_pred,
                    pin_nat_shift_left, pin_nat_sub, pin_nat_succ, pin_nat_xor, pin_string,
                    pin_zero_level,
                };
                use con_ron_core::arena::store::{EStore, LNodeView, PersTier};
                use con_ron_core::arena::stream_index;
                use con_ron_core::frontend::nat_op_ground::DeclUsedConsts;
                use con_ron_core::frontend::olean::records::read_oleans_full;
                use con_ron_core::frontend::prepare;
                use con_ron_core::frontend::prelude::builtin_prelude_e;
                use con_ron_core::kernel::expr::{literal_nat, literal_str};
                use con_ron_core::kernel::{name, pins_decode};
                use con_ron_core::ron::hashmap::Dup;
                use con_ron_core::ron::nat::Nat as RonNat;

                fn ok<T, E>(r: Result<T, E>, msg: &str) -> T {
                    match r {
                        Ok(v) => v,
                        Err(_) => panic!("{msg}"),
                    }
                }
                fn segs(pers: &PersTier, st: &mut AState, parts: &[&str]) -> NIdx {
                    let mut acc = name::anonymous();
                    for &s in parts {
                        let cps: Vec<u32> = s.chars().map(|c| c as u32).collect();
                        acc = name::mk_str(acc, cps);
                    }
                    ok(intern_name(pers, st, &acc), "intern_name")
                }
                let ap = |pers: &PersTier, st: &mut AState, mut f: EIdx, args: &[EIdx]| -> EIdx {
                    for a in args {
                        f = ok(intern_e_app(pers, st, f, a.dup2()), "ap");
                    }
                    f
                };

                #[derive(Clone, Copy)]
                enum BigMode { AllValid, BadAdd, BadStr }

                let build_bignat_env = |mode: BigMode| -> LoadedEnvironment {
                    let empty_pers = PersTier::empty();
                    let mut st = AState::init(EStore::empty());
                    ok(intern_reserved_pins(&empty_pers, &mut st), "pins");
                    let prelude_ix = ok(builtin_prelude_e(&empty_pers, &mut st), "prelude");
                    let sp = vec![con_gpu_arena::fs::str_to_cp(lean_lib)];
                    let roots = vec![segs(&empty_pers, &mut st, &["Init", "Data", "Nat", "Bitwise", "Basic"])];
                    let mut decls = ok(
                        read_oleans_full(&con_gpu_arena::fs::StdFs, &empty_pers, &mut st.store, &sp, &roots, &None),
                        "read Bitwise.Basic",
                    );

                    let empty_ls = ok(pin_empty_levels(&st), "empty_ls");
                    let zero_l = ok(pin_zero_level(&st), "zero_l");
                    let one_l = ok(intern_l_node(&empty_pers, &mut st, LNodeView::Succ(zero_l)), "one_l");
                    let one_ls = ok(intern_ls_node(&empty_pers, &mut st, vec![one_l]), "one_ls");

                    let n_nat = ok(pin_nat(&st), "Nat");
                    let n_bool = ok(pin_bool(&st), "Bool");
                    let n_bool_t = ok(pin_bool_true(&st), "true");
                    let n_bool_f = ok(pin_bool_false(&st), "false");
                    let n_str = ok(pin_string(&st), "String");
                    let n_eq = ok(pin_eq(&st), "Eq");
                    let n_eq_refl = segs(&empty_pers, &mut st, &["Eq", "refl"]);

                    let nat_e = ok(intern_e_const(&empty_pers, &mut st, n_nat, empty_ls.dup2()), "Nat");
                    let bool_e = ok(intern_e_const(&empty_pers, &mut st, n_bool, empty_ls.dup2()), "Bool");
                    let bool_t = ok(intern_e_const(&empty_pers, &mut st, n_bool_t, empty_ls.dup2()), "Bool.true");
                    let bool_f = ok(intern_e_const(&empty_pers, &mut st, n_bool_f, empty_ls.dup2()), "Bool.false");
                    let str_e = ok(intern_e_const(&empty_pers, &mut st, n_str, empty_ls.dup2()), "String");
                    let eq_1 = ok(intern_e_const(&empty_pers, &mut st, n_eq, one_ls.dup2()), "Eq");
                    let eq_refl_1 = ok(intern_e_const(&empty_pers, &mut st, n_eq_refl, one_ls), "Eq.refl");

                    let n_succ = ok(pin_nat_succ(&st), "succ");
                    let n_pred = ok(pin_nat_pred(&st), "pred");
                    let n_add = ok(pin_nat_add(&st), "add");
                    let n_sub = ok(pin_nat_sub(&st), "sub");
                    let n_mul = ok(pin_nat_mul(&st), "mul");
                    let n_shl = ok(pin_nat_shift_left(&st), "shl");
                    let n_beq = ok(pin_nat_beq(&st), "beq");
                    let n_ble = ok(pin_nat_ble(&st), "ble");
                    let n_land = ok(pin_nat_land(&st), "land");
                    let n_lor = ok(pin_nat_lor(&st), "lor");
                    let n_xor = ok(pin_nat_xor(&st), "xor");

                    let c_succ = ok(intern_e_const(&empty_pers, &mut st, n_succ, empty_ls.dup2()), "succ");
                    let c_pred = ok(intern_e_const(&empty_pers, &mut st, n_pred, empty_ls.dup2()), "pred");
                    let c_add = ok(intern_e_const(&empty_pers, &mut st, n_add, empty_ls.dup2()), "add");
                    let c_sub = ok(intern_e_const(&empty_pers, &mut st, n_sub, empty_ls.dup2()), "sub");
                    let c_mul = ok(intern_e_const(&empty_pers, &mut st, n_mul, empty_ls.dup2()), "mul");
                    let c_shl = ok(intern_e_const(&empty_pers, &mut st, n_shl, empty_ls.dup2()), "shl");
                    let c_beq = ok(intern_e_const(&empty_pers, &mut st, n_beq, empty_ls.dup2()), "beq");
                    let c_ble = ok(intern_e_const(&empty_pers, &mut st, n_ble, empty_ls.dup2()), "ble");
                    let c_land = ok(intern_e_const(&empty_pers, &mut st, n_land, empty_ls.dup2()), "land");
                    let c_lor = ok(intern_e_const(&empty_pers, &mut st, n_lor, empty_ls.dup2()), "lor");
                    let c_xor = ok(intern_e_const(&empty_pers, &mut st, n_xor, empty_ls), "xor");

                    let mk_nat = |st: &mut AState, limbs: Vec<u64>| -> EIdx {
                        ok(intern_e_lit(&empty_pers, st, literal_nat(RonNat { limbs })), "bignat")
                    };
                    let mk_str = |st: &mut AState, s: &str| -> EIdx {
                        ok(intern_e_lit(&empty_pers, st, literal_str(s.chars().map(|c| c as u32).collect())), "str")
                    };
                    let push_eq = |st: &mut AState, decls: &mut Vec<IDeclaration>, ty_e: EIdx, name_s: &str, lhs: EIdx, rhs: EIdx| {
                        let ty = ap(&empty_pers, st, eq_1.dup2(), &[ty_e.dup2(), lhs, rhs.dup2()]);
                        let pr = ap(&empty_pers, st, eq_refl_1.dup2(), &[ty_e, rhs]);
                        decls.push(IDeclaration::ThmDecl(
                            IConstantVal { name: segs(&empty_pers, st, &["WaveN", name_s]), level_params: Vec::new(), ty },
                            pr,
                        ));
                    };

                    // Values
                    let u64_max = mk_nat(&mut st, vec![u64::MAX]);
                    let two_64 = mk_nat(&mut st, vec![0, 1]);
                    let a256 = mk_nat(&mut st, vec![0xFFFF_FFFF_FFFF_FFFF, 0x0123_4567_89AB_CDEF, 0xDEAD_BEEF_CAFE_BABE, 0x1111_2222_3333_4444]);
                    let b128 = mk_nat(&mut st, vec![1, 0x0000_0000_0000_0001]);
                    let a256_plus_b128 = mk_nat(&mut st, vec![0, 0x0123_4567_89AB_CDF1, 0xDEAD_BEEF_CAFE_BABE, 0x1111_2222_3333_4444]);
                    let a256_succ = mk_nat(&mut st, vec![0, 0x0123_4567_89AB_CDF0, 0xDEAD_BEEF_CAFE_BABE, 0x1111_2222_3333_4444]);
                    let a256_pred_of_succ = a256.dup2();
                    let mul128_a = mk_nat(&mut st, vec![0x0000_0001_0000_0000, 0x0000_0000_0000_0001]); // 2^64 + 2^32
                    let mul128_b = mk_nat(&mut st, vec![0x0000_0000_0000_0003, 0x0000_0000_0000_0002]); // 2*2^64 + 3
                    // (2^64 + 2^32)*(2*2^64 + 3) = 2*2^128 + (3 + 2*2^32)*2^64 + 3*2^32
                    let mul128_prod = mk_nat(&mut st, vec![0x0000_0003_0000_0000, 3 + (2u64 << 32), 2]);
                    // u64::MAX * u64::MAX = 2^128 - 2^65 + 1 = [1, u64::MAX - 1]
                    let u64max_sq = mk_nat(&mut st, vec![1, u64::MAX - 1]);
                    let c64 = mk_nat(&mut st, vec![64]);
                    let l1 = mk_nat(&mut st, vec![1]);
                    let two_128_minus_2_64 = mk_nat(&mut st, vec![0, u64::MAX]); // u64::MAX << 64

                    let bw_a = mk_nat(&mut st, vec![0xF0F0_F0F0_0F0F_0F0F, 0xAAAA_5555_FFFF_0000, 0x1234_5678_9ABC_DEF0]);
                    let bw_b = mk_nat(&mut st, vec![0x0F0F_F0F0_00FF_FF00, 0x5555_AAAA_0F0F_F0F0, 0x1111_1111_0000_0000]);
                    let bw_and = mk_nat(&mut st, vec![0x0000_F0F0_000F_0F00, 0x0000_0000_0F0F_0000, 0x1010_1010_0000_0000]);
                    let bw_or  = mk_nat(&mut st, vec![0xFFFF_F0F0_0FFF_FF0F, 0xFFFF_FFFF_FFFF_F0F0, 0x1335_5779_9ABC_DEF0]);
                    let bw_xor = mk_nat(&mut st, vec![0xFFFF_0000_0FF0_F00F, 0xFFFF_FFFF_F0F0_F0F0, 0x0325_4769_9ABC_DEF0]);

                    match mode {
                        BigMode::BadAdd => {
                            let bad_sum = ap(&empty_pers, &mut st, c_add, &[a256.dup2(), b128]);
                            push_eq(&mut st, &mut decls, nat_e, "bad_bignat_add", bad_sum, a256);
                        }
                        BigMode::BadStr => {
                            let s1 = mk_str(&mut st, "alpha");
                            let s2 = mk_str(&mut st, "beta");
                            push_eq(&mut st, &mut decls, str_e, "bad_str", s1, s2);
                        }
                        BigMode::AllValid => {
                            // 1. succ u64 overflow -> BigNat
                            let e1 = ap(&empty_pers, &mut st, c_succ.dup2(), &[u64_max.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "succ_u64_ovf", e1, two_64.dup2());
                            // 2. succ 256-bit
                            let e2 = ap(&empty_pers, &mut st, c_succ, &[a256.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "succ_256", e2, a256_succ.dup2());
                            // 3. pred 256-bit
                            let e3 = ap(&empty_pers, &mut st, c_pred, &[a256_succ.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "pred_256", e3, a256_pred_of_succ);
                            // 4. add u64 overflow promotion + mixed 256+128
                            let e4a = ap(&empty_pers, &mut st, c_add.dup2(), &[u64_max.dup2(), l1.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "add_u64_ovf", e4a, two_64);
                            let e4b = ap(&empty_pers, &mut st, c_add, &[a256.dup2(), b128.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "add_256_128", e4b, a256_plus_b128.dup2());
                            // 5. sub (256+128) - 128 = 256
                            let e5 = ap(&empty_pers, &mut st, c_sub, &[a256_plus_b128.dup2(), b128.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "sub_256_128", e5, a256.dup2());
                            // 6. mul u64 overflow promotion + BigNat mul
                            let e6a = ap(&empty_pers, &mut st, c_mul.dup2(), &[u64_max.dup2(), u64_max.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "mul_u64_ovf", e6a, u64max_sq);
                            let e6b = ap(&empty_pers, &mut st, c_mul, &[mul128_a, mul128_b]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "mul_bignat", e6b, mul128_prod);
                            // 7. shl u64 overflow -> BigNat
                            let e7 = ap(&empty_pers, &mut st, c_shl, &[u64_max, c64]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "shl_u64_ovf", e7, two_128_minus_2_64);
                            // 8. beq / ble on 256-bit
                            let e8a = ap(&empty_pers, &mut st, c_beq.dup2(), &[a256_succ.dup2(), a256_succ.dup2()]);
                            push_eq(&mut st, &mut decls, bool_e.dup2(), "beq_true", e8a, bool_t.dup2());
                            let e8b = ap(&empty_pers, &mut st, c_beq, &[a256_succ.dup2(), b128.dup2()]);
                            push_eq(&mut st, &mut decls, bool_e.dup2(), "beq_false", e8b, bool_f.dup2());
                            let e9a = ap(&empty_pers, &mut st, c_ble.dup2(), &[a256, a256_succ.dup2()]);
                            push_eq(&mut st, &mut decls, bool_e.dup2(), "ble_true", e9a, bool_t);
                            let e9b = ap(&empty_pers, &mut st, c_ble, &[a256_succ, b128]);
                            push_eq(&mut st, &mut decls, bool_e, "ble_false", e9b, bool_f);
                            // 9. land / lor / xor 192-bit BigNat
                            let e10 = ap(&empty_pers, &mut st, c_land, &[bw_a.dup2(), bw_b.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "land_big", e10, bw_and);
                            let e11 = ap(&empty_pers, &mut st, c_lor, &[bw_a.dup2(), bw_b.dup2()]);
                            push_eq(&mut st, &mut decls, nat_e.dup2(), "lor_big", e11, bw_or);
                            let e12 = ap(&empty_pers, &mut st, c_xor, &[bw_a, bw_b]);
                            push_eq(&mut st, &mut decls, nat_e, "xor_big", e12, bw_xor);
                            // 10. String literal equality
                            let s = mk_str(&mut st, "con-gpu-wave-n-exact-str");
                            push_eq(&mut st, &mut decls, str_e, "str_eq_refl", s.dup2(), s);
                        }
                    }

                    let prepared = ok(prepare::prepare_d(&empty_pers, &mut st, prelude_ix, decls, &DeclUsedConsts), "prep");
                    let file_records = prepared.decls.len();
                    let pins_decoded = ok(pins_decode::decode_embedded(), "pins_dec");
                    let ipins = ok(checker::intern_all_pins(&empty_pers, &mut st, &pins_decoded, &max_nat_size_default()), "ipins");
                    let ix = ok(stream_index::build_index(&empty_pers, &mut st, stream_index::stream_index_empty(), &prepared.decls, 0), "idx");
                    let pers = checker::freeze_tier(&mut st.store, ix);
                    LoadedEnvironment {
                        pers,
                        pins: st.pins,
                        ipins,
                        decls: prepared.decls,
                        file_records,
                        synthesized: prepared.synthesised,
                        hoisted: prepared.hoisted.len(),
                        olean: None,
                        load_ns: 0,
                        materialize_ns: 0,
                        index_ns: 0,
                        thm_materialized_count: 0,
                        closure_fingerprint: None,
                        closure_roots: Vec::new(),
                        closure_manifest: Vec::new(),
                        module_hashes: std::collections::HashMap::new(),
                        preverified_prefix: 0,
                    }
                };

                let ctx = GpuContext::shared_vulkan_high_perf().expect("Vulkan GPU required");
                let pipe = TypecheckGpuPipeline::new(&ctx);

                let ok_env = build_bignat_env(BigMode::AllValid);
                let start = ok_env.decls.len() - 17;
                let pkt = con_gpu_arena::soa_pack::pack_arena_from(&ok_env, ArenaLimitsConfig::default(), start);
                let rep = pipe
                    .verify_packet_hybrid_range_with(&ctx, &ok_env, &pkt, Some(4), start, VerifyOptions::default())
                    .expect("WaveN BigNat + String GPU");
                assert!(matches!(rep.verdict, VerificationVerdict::Accepted { .. }), "{:?}", rep.verdict);
                assert_eq!(rep.gpu_verified_count, 17, "All 17 BigNat/String theorems must verify natively on GPU: {rep:?}");
                assert_eq!(rep.delegated_count, 0, "Zero delegation allowed for <=64-limb BigNat & String: {rep:?}");

                for bad_mode in [BigMode::BadAdd, BigMode::BadStr] {
                    let bad_env = build_bignat_env(bad_mode);
                    let bstart = bad_env.decls.len() - 1;
                    let bpkt = con_gpu_arena::soa_pack::pack_arena_from(&bad_env, ArenaLimitsConfig::default(), bstart);
                    let brep = pipe
                        .verify_packet_hybrid_range_with(&ctx, &bad_env, &bpkt, Some(4), bstart, VerifyOptions::default())
                        .expect("WaveN BigNat/String negative GPU");
                    assert!(matches!(brep.verdict, VerificationVerdict::Rejected { .. }), "{:?}", brep.verdict);
                    assert_eq!(brep.gpu_rejected_count, 1);
                    assert_eq!(brep.delegated_count, 0);
                }
            })
            .expect("spawn")
            .join()
            .expect("join");
    }
}
