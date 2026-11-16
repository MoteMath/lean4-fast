FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive \
    NVIDIA_VISIBLE_DEVICES=all \
    NVIDIA_DRIVER_CAPABILITIES=all

# Install Vulkan loader + GLVND/EGL + compression/diagnostic tools.
# NEVER install mesa-vulkan-drivers so Vulkan selects the discrete NVIDIA driver only.
RUN apt-get update && \
    apt-get install -y --no-install-recommends \
      ca-certificates \
      libvulkan1 \
      vulkan-tools \
      libglvnd0 \
      libglx0 \
      libegl1 \
      libx11-6 \
      libxext6 \
      zstd \
      tar \
      python3 \
      procps && \
    rm -rf /var/lib/apt/lists/*

WORKDIR /opt/bench

COPY con-gpu /opt/bench/con-gpu
COPY leanchecker /opt/bench/leanchecker
COPY stock/ /opt/bench/stock/
COPY fixtures.tar.zst* /opt/bench/
COPY phase6_nvidia.py /opt/bench/phase6_nvidia.py
COPY run_aws_gpu_bench.sh /opt/bench/run_aws_gpu_bench.sh

RUN chmod +x /opt/bench/con-gpu /opt/bench/leanchecker /opt/bench/run_aws_gpu_bench.sh

ENTRYPOINT ["/opt/bench/run_aws_gpu_bench.sh"]
