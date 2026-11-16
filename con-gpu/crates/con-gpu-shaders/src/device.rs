use std::sync::{Arc, Mutex, OnceLock};

use bytemuck::Pod;
use wgpu::util::DeviceExt;

static VULKAN_INIT_MUTEX: Mutex<()> = Mutex::new(());
static SHARED_GPU_CTX: OnceLock<Result<Arc<GpuContext>, String>> = OnceLock::new();

/// Metadata describing the selected Vulkan/wgpu device (all integer fields, zero floats).
#[derive(Clone, Debug)]
pub struct GpuDeviceInfo {
    pub name: String,
    pub vendor: u32,
    pub device: u32,
    pub device_type: String,
    pub backend: String,
    pub driver: String,
    pub driver_info: String,
    pub max_storage_buffer_binding_size: u64,
    pub max_buffer_size: u64,
    pub max_compute_workgroup_storage_size: u32,
    pub max_compute_invocations_per_workgroup: u32,
    pub max_compute_workgroups_per_dimension: u32,
}

/// Shared `wgpu` Vulkan high-performance compute context for `con-gpu`.
pub struct GpuContext {
    pub instance: wgpu::Instance,
    pub adapter: wgpu::Adapter,
    pub device: wgpu::Device,
    pub queue: wgpu::Queue,
    pub info: GpuDeviceInfo,
}

impl GpuContext {
    /// Return a process-wide shared high-performance Vulkan context, initialized at most once.
    pub fn shared_vulkan_high_perf() -> Result<Arc<GpuContext>, String> {
        SHARED_GPU_CTX
            .get_or_init(|| Self::new_vulkan_high_perf().map(Arc::new))
            .clone()
    }

    /// Initialize a discrete/high-performance Vulkan compute device, requesting the
    /// adapter's full limits (critical for large storage buffers on the RX 7900 XTX).
    pub fn new_vulkan_high_perf() -> Result<Self, String> {
        let _guard = VULKAN_INIT_MUTEX
            .lock()
            .unwrap_or_else(|e| e.into_inner());
        let instance = wgpu::Instance::new(wgpu::InstanceDescriptor {
            backends: wgpu::Backends::VULKAN,
            ..wgpu::InstanceDescriptor::new_without_display_handle()
        });

        let adapter = pollster::block_on(instance.request_adapter(&wgpu::RequestAdapterOptions {
            power_preference: wgpu::PowerPreference::HighPerformance,
            compatible_surface: None,
            force_fallback_adapter: false,
            apply_limit_buckets: false,
        }))
        .map_err(|e| format!("failed to acquire Vulkan HighPerformance adapter: {e}"))?;

        let raw_info = adapter.get_info();
        let adapter_limits = adapter.limits();

        let (device, queue) = pollster::block_on(adapter.request_device(&wgpu::DeviceDescriptor {
            label: Some("con-gpu-vulkan-device"),
            required_features: adapter.features() & wgpu::Features::PIPELINE_CACHE,
            required_limits: adapter_limits.clone(),
            experimental_features: wgpu::ExperimentalFeatures::disabled(),
            memory_hints: wgpu::MemoryHints::Performance,
            trace: wgpu::Trace::Off,
        }))
        .map_err(|e| format!("failed to create Vulkan compute device: {e}"))?;

        let info = GpuDeviceInfo {
            name: raw_info.name,
            vendor: raw_info.vendor,
            device: raw_info.device,
            device_type: format!("{:?}", raw_info.device_type),
            backend: format!("{:?}", raw_info.backend),
            driver: raw_info.driver,
            driver_info: raw_info.driver_info,
            max_storage_buffer_binding_size: adapter_limits.max_storage_buffer_binding_size as u64,
            max_buffer_size: adapter_limits.max_buffer_size,
            max_compute_workgroup_storage_size: adapter_limits.max_compute_workgroup_storage_size,
            max_compute_invocations_per_workgroup: adapter_limits
                .max_compute_invocations_per_workgroup,
            max_compute_workgroups_per_dimension: adapter_limits
                .max_compute_workgroups_per_dimension,
        };

        Ok(Self {
            instance,
            adapter,
            device,
            queue,
            info,
        })
    }

    pub fn create_uniform_buffer<T: Pod>(&self, label: &str, data: &T) -> wgpu::Buffer {
        self.device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some(label),
                contents: bytemuck::bytes_of(data),
                usage: wgpu::BufferUsages::UNIFORM | wgpu::BufferUsages::COPY_DST,
            })
    }

    pub fn create_storage_buffer_init<T: Pod>(
        &self,
        label: &str,
        data: &[T],
        extra_usage: wgpu::BufferUsages,
    ) -> wgpu::Buffer {
        let bytes = if data.is_empty() {
            &[0u8; 4][..]
        } else {
            bytemuck::cast_slice(data)
        };
        self.device
            .create_buffer_init(&wgpu::util::BufferInitDescriptor {
                label: Some(label),
                contents: bytes,
                usage: wgpu::BufferUsages::STORAGE | extra_usage,
            })
    }

    pub fn create_storage_buffer_zeroed(
        &self,
        label: &str,
        byte_len: u64,
        usage: wgpu::BufferUsages,
    ) -> wgpu::Buffer {
        let size = byte_len.max(4);
        self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some(label),
            size,
            usage: wgpu::BufferUsages::STORAGE | usage,
            mapped_at_creation: false,
        })
    }

    pub fn wait_idle(&self) {
        let _ = self.device.poll(wgpu::PollType::wait_indefinitely());
    }

    pub fn read_buffer_vec<T: Pod + Default>(
        &self,
        src: &wgpu::Buffer,
        count: usize,
    ) -> Result<Vec<T>, String> {
        self.read_buffer_range_vec(src, 0, count)
    }

    pub fn read_buffer_range_vec<T: Pod + Default>(
        &self,
        src: &wgpu::Buffer,
        src_elem_offset: usize,
        count: usize,
    ) -> Result<Vec<T>, String> {
        if count == 0 {
            return Ok(Vec::new());
        }
        let elem_size = std::mem::size_of::<T>();
        let byte_offset = (src_elem_offset * elem_size) as u64;
        let byte_size = (count * elem_size) as u64;
        let staging = self.device.create_buffer(&wgpu::BufferDescriptor {
            label: Some("con-gpu-readback-staging"),
            size: byte_size,
            usage: wgpu::BufferUsages::MAP_READ | wgpu::BufferUsages::COPY_DST,
            mapped_at_creation: false,
        });

        let mut encoder = self
            .device
            .create_command_encoder(&wgpu::CommandEncoderDescriptor {
                label: Some("con-gpu-readback-copy"),
            });
        encoder.copy_buffer_to_buffer(src, byte_offset, &staging, 0, byte_size);
        self.queue.submit(Some(encoder.finish()));

        let slice = staging.slice(..byte_size);
        let (tx, rx) = std::sync::mpsc::sync_channel(1);
        slice.map_async(wgpu::MapMode::Read, move |res| {
            let _ = tx.send(res);
        });
        self.wait_idle();
        rx.recv()
            .map_err(|e| format!("GPU readback channel closed: {e}"))?
            .map_err(|e| format!("GPU staging map_async failed: {e}"))?;

        let data = slice
            .get_mapped_range()
            .map_err(|e| format!("GPU get_mapped_range failed: {e}"))?;
        let typed: &[T] = bytemuck::cast_slice(&data);
        let out = typed[..count].to_vec();
        drop(data);
        staging.unmap();
        Ok(out)
    }
}
