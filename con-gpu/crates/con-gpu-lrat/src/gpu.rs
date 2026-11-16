use std::time::Instant;

use con_gpu_shaders::device::GpuContext;

use crate::cpu::{verify_lrat_steps_cpu, LratStatus};
use crate::parser::{GpuLratVerdict, LratHeader, LratProblem};

pub const LRAT_SHADER_WGSL: &str = include_str!("wgsl/lrat_verify.wgsl");

pub const LRAT_STATUS_VERIFIED: u32 = 0;
pub const LRAT_STATUS_REJECTED: u32 = 1;
pub const LRAT_STATUS_DELEGATE: u32 = 2;

pub fn lrat_reason_str(code: u32) -> &'static str {
    match code {
        0 => "ok",
        1 => "empty hint list",
        2 => "non-causal hint (hint_id >= clause_id)",
        3 => "undefined or future hint clause",
        4 => "deleted hint clause used after deletion",
        5 => "non-unit hint clause",
        6 => "already satisfied hint clause",
        7 => "RUP propagation failed to derive conflict",
        8 => "invalid clause ID or literal 0",
        9 => "RAT step delegated to host",
        10 => "literal scratch capacity delegated to host",
        _ => "unknown rejection reason",
    }
}

pub struct LratGpuPipeline {
    pipeline: wgpu::ComputePipeline,
    bgl: wgpu::BindGroupLayout,
}

impl LratGpuPipeline {
    pub fn new(ctx: &GpuContext) -> Self {
        let shader = ctx
            .device
            .create_shader_module(wgpu::ShaderModuleDescriptor {
                label: Some("lrat_verify.wgsl"),
                source: wgpu::ShaderSource::Wgsl(LRAT_SHADER_WGSL.into()),
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
                label: Some("lrat-bgl"),
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
                    ro_storage(5),
                    ro_storage(6),
                    ro_storage(7),
                    ro_storage(8),
                    rw_storage(9),
                    rw_storage(10),
                ],
            });

        let pl = ctx
            .device
            .create_pipeline_layout(&wgpu::PipelineLayoutDescriptor {
                label: Some("lrat-pl"),
                bind_group_layouts: &[Some(&bgl)],
                immediate_size: 0,
            });

        let pipeline = ctx
            .device
            .create_compute_pipeline(&wgpu::ComputePipelineDescriptor {
                label: Some("lrat-pipeline"),
                layout: Some(&pl),
                module: &shader,
                entry_point: Some("main"),
                compilation_options: wgpu::PipelineCompilationOptions::default(),
                cache: None,
            });

        Self { pipeline, bgl }
    }

    pub fn verify_gpu(&self, ctx: &GpuContext, prob: &LratProblem) -> Result<LratStatus, String> {
        let t_total = Instant::now();
        if let Some(err) = &prob.parse_error {
            return Ok(LratStatus::Rejected {
                step_idx: 0,
                clause_id: 0,
                reason: err.clone(),
                rejected_count: 1,
            });
        }
        if prob.steps.is_empty() {
            if prob.cnf_has_empty_clause {
                return Ok(LratStatus::Accepted {
                    total_steps: 0,
                    gpu_verified_steps: 0,
                    delegated_steps: 0,
                    has_empty_clause: true,
                    thread_count: 1,
                    elapsed_ns: t_total.elapsed().as_nanos(),
                    gpu_kernel_ns: 0,
                    pcie_upload_ns: 0,
                });
            }
            return Ok(LratStatus::Rejected {
                step_idx: 0,
                clause_id: 0,
                reason: "LRAT proof has 0 steps and no empty CNF clause".to_string(),
                rejected_count: 1,
            });
        }

        let t_up = Instant::now();
        let hdr = LratHeader {
            num_steps: prob.steps.len() as u32,
            max_clause_id: prob.max_clause_id,
            num_cnf_clauses: prob.num_cnf_clauses,
            pad0: 0,
        };
        let hdr_buf = ctx.create_uniform_buffer("lrat-hdr", &hdr);
        let steps_buf = ctx.create_storage_buffer_init("lrat-steps", &prob.steps, wgpu::BufferUsages::empty());
        let flags_buf = ctx.create_storage_buffer_init("lrat-flags", &prob.step_flags, wgpu::BufferUsages::empty());
        let hints_buf = ctx.create_storage_buffer_init("lrat-hints", &prob.hints, wgpu::BufferUsages::empty());
        let lits_buf = ctx.create_storage_buffer_init("lrat-lits", &prob.clause_lits, wgpu::BufferUsages::empty());
        let off_buf = ctx.create_storage_buffer_init("lrat-off", &prob.clause_off, wgpu::BufferUsages::empty());
        let len_buf = ctx.create_storage_buffer_init("lrat-len", &prob.clause_len, wgpu::BufferUsages::empty());
        let birth_buf = ctx.create_storage_buffer_init("lrat-birth", &prob.clause_birth_step, wgpu::BufferUsages::empty());
        let del_buf = ctx.create_storage_buffer_init("lrat-del", &prob.clause_deleted_at, wgpu::BufferUsages::empty());
        let verdicts_buf = ctx.create_storage_buffer_zeroed(
            "lrat-verdicts",
            (prob.steps.len() * std::mem::size_of::<GpuLratVerdict>()) as u64,
            wgpu::BufferUsages::COPY_SRC,
        );
        let summary_buf = ctx.create_storage_buffer_zeroed(
            "lrat-summary",
            16,
            wgpu::BufferUsages::COPY_SRC,
        );
        let pcie_upload_ns = t_up.elapsed().as_nanos();

        let bg = ctx.device.create_bind_group(&wgpu::BindGroupDescriptor {
            label: Some("lrat-bg"),
            layout: &self.bgl,
            entries: &[
                wgpu::BindGroupEntry { binding: 0, resource: hdr_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 1, resource: steps_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 2, resource: flags_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 3, resource: hints_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 4, resource: lits_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 5, resource: off_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 6, resource: len_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 7, resource: birth_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 8, resource: del_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 9, resource: verdicts_buf.as_entire_binding() },
                wgpu::BindGroupEntry { binding: 10, resource: summary_buf.as_entire_binding() },
            ],
        });

        let wgs = ((prob.steps.len() as u32) + 63) / 64;
        let t_k = Instant::now();
        let mut enc = ctx
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("lrat-dispatch"),
            });
        {
            let mut pass = enc.begin_compute_pass(&wgpu::ComputePassDescriptor {
                label: Some("lrat-pass"),
                timestamp_writes: None,
            });
            pass.set_pipeline(&self.pipeline);
            pass.set_bind_group(0, &bg, &[]);
            pass.dispatch_workgroups(wgs, 1, 1);
        }
        ctx.queue.submit(Some(enc.finish()));
        ctx.wait_idle();
        let gpu_kernel_ns = t_k.elapsed().as_nanos();

        let summary: Vec<u32> = ctx.read_buffer_vec(&summary_buf, 4)?;
        let verdicts: Vec<GpuLratVerdict> = ctx.read_buffer_vec(&verdicts_buf, prob.steps.len())?;

        let gpu_verified = summary[0] as usize;
        let gpu_delegated = summary[1] as usize;
        let gpu_rejected = summary[2] as usize;
        let mut has_empty = prob.cnf_has_empty_clause || summary[3] > 0;

        if gpu_rejected > 0 {
            for (idx, v) in verdicts.iter().enumerate() {
                if v.status == LRAT_STATUS_REJECTED {
                    return Ok(LratStatus::Rejected {
                        step_idx: idx,
                        clause_id: v.clause_id,
                        reason: format!("GPU LRAT rejected: {}", lrat_reason_str(v.reason)),
                        rejected_count: gpu_rejected,
                    });
                }
            }
        }

        let mut delegated_indices = Vec::with_capacity(gpu_delegated);
        if gpu_delegated > 0 {
            for (idx, v) in verdicts.iter().enumerate() {
                if v.status == LRAT_STATUS_DELEGATE {
                    delegated_indices.push(idx);
                }
            }
            match verify_lrat_steps_cpu(prob, &delegated_indices, None) {
                Err((step_idx, clause_id, reason)) => {
                    return Ok(LratStatus::Rejected {
                        step_idx,
                        clause_id,
                        reason,
                        rejected_count: 1,
                    });
                }
                Ok((del_empty, _, _)) => {
                    if del_empty {
                        has_empty = true;
                    }
                }
            }
        }

        if !has_empty {
            return Ok(LratStatus::Rejected {
                step_idx: prob.steps.len(),
                clause_id: 0,
                reason: "LRAT proof does not verify an empty clause".to_string(),
                rejected_count: 1,
            });
        }

        Ok(LratStatus::Accepted {
            total_steps: prob.steps.len(),
            gpu_verified_steps: gpu_verified,
            delegated_steps: delegated_indices.len(),
            has_empty_clause: true,
            thread_count: 1,
            elapsed_ns: t_total.elapsed().as_nanos(),
            gpu_kernel_ns,
            pcie_upload_ns,
        })
    }
}
