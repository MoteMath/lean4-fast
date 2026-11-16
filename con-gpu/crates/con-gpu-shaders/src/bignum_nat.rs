use std::time::Instant;

use bytemuck::{Pod, Zeroable};

use crate::device::GpuContext;

pub const BIGNUM_SHADER_WGSL: &str = include_str!("wgsl/bignum_nat.wgsl");

#[repr(u32)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BignumOp {
    Add = 0,
    Sub = 1,
    Mul = 2,
    Cmp = 3,
    Beq = 4,
    Ble = 5,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct BignumHeader {
    pub num_tasks: u32,
    pub in_stride: u32,
    pub out_stride: u32,
    pub pad0: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct GpuBignumTask {
    pub op: u32,
    pub a_len: u32,
    pub b_len: u32,
    pub flags: u32,
}

#[repr(C)]
#[derive(Clone, Copy, Debug, Default, Pod, Zeroable)]
pub struct GpuBignumMeta {
    pub out_len: u32,
    pub cmp_res: u32,
    pub bool_res: u32,
    pub overflow: u32,
}

#[derive(Clone, Debug)]
pub struct BignumBatchJob {
    pub op: BignumOp,
    /// Little-endian `u32` limbs.
    pub a_limbs: Vec<u32>,
    /// Little-endian `u32` limbs.
    pub b_limbs: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BignumBatchOutput {
    pub limbs: Vec<u32>,
    pub cmp_lt_eq_gt: u32,
    pub bool_res: bool,
    pub overflow: bool,
}

pub struct BignumBatchReport {
    pub outputs: Vec<BignumBatchOutput>,
    pub pcie_upload_ns: u128,
    pub gpu_kernel_ns: u128,
    pub gpu_total_ns: u128,
}

pub struct BignumNatPipeline {
    pipeline: wgpu::ComputePipeline,
    bgl: wgpu::BindGroupLayout,
}

impl BignumNatPipeline {
    pub fn new(ctx: &GpuContext) -> Self {
        let shader = ctx
            .device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("bignum_nat.wgsl"),
                source: wgpu::ShaderSource::Wgsl(BIGNUM_SHADER_WGSL.into()),
            });

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

        let bgl = ctx
            .device
            .create_bind_group_layout(&wgpu::BindGroupLayoutDescriptor {
                label: Some("bignum-bgl"),
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
                    rw_storage(4),
                    rw_storage(5),
                ],
            });

        let pl = ctx
            .device
            .create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("bignum-pl"),
                bind_group_layouts: &[Some(&bgl)],
                immediate_size: 0,
            });

        let pipeline = ctx
            .device
            .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("bignum-pipeline"),
                layout: Some(&pl),
                module: &shader,
                entry_point: Some("main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        Self { pipeline, bgl }
    }

    pub fn eval_batch(
        &self,
        ctx: &GpuContext,
        jobs: &[BignumBatchJob],
    ) -> Result<BignumBatchReport, String> {
        if jobs.is_empty() {
            return Ok(BignumBatchReport {
                outputs: Vec::new(),
                pcie_upload_ns: 0,
                gpu_kernel_ns: 0,
                gpu_total_ns: 0,
            });
        }

        let t_total = Instant::now();

        let max_in = jobs
            .iter()
            .map(|j| j.a_limbs.len().max(j.b_limbs.len()))
            .max()
            .unwrap_or(1)
            .max(1);
        let in_stride = max_in as u32;
        let out_stride = (max_in * 2 + 1) as u32;
        let num_tasks = jobs.len();

        let mut tasks_gpu = Vec::with_capacity(num_tasks);
        let mut a_flat = vec![0u32; num_tasks * in_stride as usize];
        let mut b_flat = vec![0u32; num_tasks * in_stride as usize];

        for (i, j) in jobs.iter().enumerate() {
            let base = i * in_stride as usize;
            a_flat[base..base + j.a_limbs.len()].copy_from_slice(&j.a_limbs);
            b_flat[base..base + j.b_limbs.len()].copy_from_slice(&j.b_limbs);
            tasks_gpu.push(GpuBignumTask {
                op: j.op as u32,
                a_len: j.a_limbs.len() as u32,
                b_len: j.b_limbs.len() as u32,
                flags: 0,
            });
        }

        let hdr = BignumHeader {
            num_tasks: num_tasks as u32,
            in_stride,
            out_stride,
            pad0: 0,
        };

        let t_upload = Instant::now();
        let hdr_buf = ctx.create_uniform_buffer("bignum-hdr", &hdr);
        let tasks_buf = ctx.create_storage_buffer_init("bignum-tasks", &tasks_gpu, wgpu::BufferUsages::empty());
        let a_buf = ctx.create_storage_buffer_init("bignum-a", &a_flat, wgpu::BufferUsages::empty());
        let b_buf = ctx.create_storage_buffer_init("bignum-b", &b_flat, wgpu::BufferUsages::empty());
        let out_limbs_len = num_tasks * out_stride as usize;
        let out_limbs_buf = ctx.create_storage_buffer_zeroed(
            "bignum-out-limbs",
            (out_limbs_len * 4) as u64,
            wgpu::BufferUsages::COPY_SRC,
        );
        let out_meta_buf = ctx.create_storage_buffer_zeroed(
            "bignum-out-meta",
            (num_tasks * std::mem::size_of::<GpuBignumMeta>()) as u64,
            wgpu::BufferUsages::COPY_SRC,
        );
        let pcie_upload_ns = t_upload.elapsed().as_nanos();

        let bg = ctx.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("bignum-bg"),
            layout: &self.bgl,
            entries: &[
                wgpu::BindGroupEntry {
                    binding: 0,
                    resource: hdr_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 1,
                    resource: tasks_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 2,
                    resource: a_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 3,
                    resource: b_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 4,
                    resource: out_limbs_buf.as_entire_binding(),
                },
                wgpu::BindGroupEntry {
                    binding: 5,
                    resource: out_meta_buf.as_entire_binding(),
                },
            ],
        });

        let wgs = ((num_tasks as u32) + 63) / 64;
        let t0 = Instant::now();
        let mut encoder = ctx
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("bignum-dispatch"),
            });
        {
            let mut pass = encoder.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("bignum-pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.pipeline);
            pass.set_bind_group(0, &bg, &[]);
            pass.dispatch_workgroups(wgs, 1, 1);
        }
        ctx.queue.submit(Some(encoder.finish()));
        ctx.wait_idle();
        let gpu_kernel_ns = t0.elapsed().as_nanos();

        let flat_out: Vec<u32> = ctx.read_buffer_vec(&out_limbs_buf, out_limbs_len)?;
        let metas: Vec<GpuBignumMeta> = ctx.read_buffer_vec(&out_meta_buf, num_tasks)?;

        let mut outputs = Vec::with_capacity(num_tasks);
        for (i, m) in metas.iter().enumerate() {
            let base = i * out_stride as usize;
            let len = (m.out_len as usize).min(out_stride as usize);
            outputs.push(BignumBatchOutput {
                limbs: flat_out[base..base + len].to_vec(),
                cmp_lt_eq_gt: m.cmp_res,
                bool_res: m.bool_res != 0,
                overflow: m.overflow != 0,
            });
        }

        Ok(BignumBatchReport {
            outputs,
            pcie_upload_ns,
            gpu_kernel_ns,
            gpu_total_ns: t_total.elapsed().as_nanos(),
        })
    }
}

/// Convert `con_ron_core::ron::nat::Nat` (`u64` limbs) into trimmed little-endian `u32` limbs.
pub fn nat_to_u32_limbs(limbs64: &[u64]) -> Vec<u32> {
    let mut out = Vec::with_capacity(limbs64.len() * 2);
    for &w in limbs64 {
        out.push((w & 0xFFFF_FFFF) as u32);
        out.push((w >> 32) as u32);
    }
    while matches!(out.last(), Some(&0)) {
        out.pop();
    }
    out
}

/// Convert little-endian `u32` limbs back into `u64` limbs matching `con_ron_core::ron::nat::Nat`.
pub fn u32_limbs_to_u64(limbs32: &[u32]) -> Vec<u64> {
    let mut out = Vec::with_capacity((limbs32.len() + 1) / 2);
    let mut i = 0;
    while i < limbs32.len() {
        let lo = limbs32[i] as u64;
        let hi = if i + 1 < limbs32.len() {
            (limbs32[i + 1] as u64) << 32
        } else {
            0u64
        };
        out.push(lo | hi);
        i += 2;
    }
    while matches!(out.last(), Some(&0)) {
        out.pop();
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use con_ron_core::ron::nat;

    fn from_u64(x: u64) -> nat::Nat {
        if x == 0 {
            nat::Nat { limbs: Vec::new() }
        } else {
            nat::Nat { limbs: vec![x] }
        }
    }

    fn split_u64(x: u64) -> Vec<u32> {
        nat_to_u32_limbs(&from_u64(x).limbs)
    }

    fn limbs_from_u64s(ws: &[u64]) -> nat::Nat {
        let mut limbs = ws.to_vec();
        while matches!(limbs.last(), Some(&0)) {
            limbs.pop();
        }
        nat::Nat { limbs }
    }

    #[test]
    fn gpu_bignum_matches_exact_host_nat() {
        let ctx = GpuContext::new_vulkan_high_perf()
            .expect("Vulkan GPU context required (RX 7900 XTX)");
        eprintln!(
            "Using GPU: {} (backend={}, max_storage={})",
            ctx.info.name, ctx.info.backend, ctx.info.max_storage_buffer_binding_size
        );

        let pipe = BignumNatPipeline::new(&ctx);

        let pairs: Vec<(nat::Nat, nat::Nat)> = vec![
            (from_u64(0), from_u64(0)),
            (from_u64(0), from_u64(42)),
            (from_u64(42), from_u64(0)),
            (from_u64(0xFFFF_FFFF), from_u64(1)),
            (from_u64(0xFFFF_FFFF), from_u64(0xFFFF_FFFF)),
            (from_u64(u64::MAX), from_u64(1)),
            (from_u64(u64::MAX), from_u64(u64::MAX)),
            (
                limbs_from_u64s(&[0xFFFF_FFFF_FFFF_FFFF, 0xFFFF_FFFF_FFFF_FFFF, 0xDEAD_BEEF]),
                limbs_from_u64s(&[1, 0, 0xCAFE_BABE_1234_5678]),
            ),
            (
                limbs_from_u64s(&[0x1234_5678_9ABC_DEF0, 0xFEDC_BA98_7654_3210, 0x0001_0002_0003_0004]),
                limbs_from_u64s(&[0xAAAA_BBBB_CCCC_DDDD, 0x9999_8888_7777_6666, 0x0001_0002_0003_0004]),
            ),
            (
                limbs_from_u64s(&[5, 0, 0, 1]),
                limbs_from_u64s(&[6, 0, 0, 1]),
            ),
        ];

        let mut jobs = Vec::new();
        let mut expected_add = Vec::new();
        let mut expected_sub = Vec::new();
        let mut expected_mul = Vec::new();
        let mut expected_beq = Vec::new();
        let mut expected_ble = Vec::new();

        for (a, b) in &pairs {
            let al = nat_to_u32_limbs(&a.limbs);
            let bl = nat_to_u32_limbs(&b.limbs);

            jobs.push(BignumBatchJob {
                op: BignumOp::Add,
                a_limbs: al.clone(),
                b_limbs: bl.clone(),
            });
            expected_add.push(nat::add(a, b));

            jobs.push(BignumBatchJob {
                op: BignumOp::Sub,
                a_limbs: al.clone(),
                b_limbs: bl.clone(),
            });
            expected_sub.push(nat::sub(a, b));

            jobs.push(BignumBatchJob {
                op: BignumOp::Mul,
                a_limbs: al.clone(),
                b_limbs: bl.clone(),
            });
            expected_mul.push(nat::mul(a, b));

            jobs.push(BignumBatchJob {
                op: BignumOp::Beq,
                a_limbs: al.clone(),
                b_limbs: bl.clone(),
            });
            expected_beq.push(nat::beq(a, b));

            jobs.push(BignumBatchJob {
                op: BignumOp::Ble,
                a_limbs: al,
                b_limbs: bl,
            });
            expected_ble.push(nat::ble(a, b));
        }

        let report = pipe.eval_batch(&ctx, &jobs).expect("GPU bignum batch");
        assert_eq!(report.outputs.len(), jobs.len());

        for idx in 0..pairs.len() {
            let o_add = &report.outputs[idx * 5];
            let o_sub = &report.outputs[idx * 5 + 1];
            let o_mul = &report.outputs[idx * 5 + 2];
            let o_beq = &report.outputs[idx * 5 + 3];
            let o_ble = &report.outputs[idx * 5 + 4];

            assert!(!o_add.overflow, "unexpected add overflow at {idx}");
            assert!(!o_sub.overflow, "unexpected sub overflow at {idx}");
            assert!(!o_mul.overflow, "unexpected mul overflow at {idx}");

            assert_eq!(
                u32_limbs_to_u64(&o_add.limbs),
                expected_add[idx].limbs,
                "Add mismatch at {idx}"
            );
            assert_eq!(
                u32_limbs_to_u64(&o_sub.limbs),
                expected_sub[idx].limbs,
                "Sub mismatch at {idx}"
            );
            assert_eq!(
                u32_limbs_to_u64(&o_mul.limbs),
                expected_mul[idx].limbs,
                "Mul mismatch at {idx}"
            );
            assert_eq!(o_beq.bool_res, expected_beq[idx], "Beq mismatch at {idx}");
            assert_eq!(o_ble.bool_res, expected_ble[idx], "Ble mismatch at {idx}");
        }

        let _ = split_u64(1);
    }
}
