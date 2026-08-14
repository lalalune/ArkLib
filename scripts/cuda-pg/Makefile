# CUDA delta* far-line incidence engine (#407) — GPU port of ../rust-pg.
#
#   make            # build for the local GPU (-arch=native)
#   make ARCH=sm_120  # RTX 5080 (Blackwell)
#   make ARCH=sm_90a  # H200 (Hopper)
#   make ARCH=sm_100a # B200 (Blackwell datacenter)
#   ./pg <n> <k> [cap]
#
# Requires CUDA toolkit (nvcc). No external deps.

ARCH ?= native
NVCC ?= nvcc
NVCCFLAGS = -O3 -arch=$(ARCH) -lineinfo --use_fast_math

pg: pg.cu
	$(NVCC) $(NVCCFLAGS) -o pg pg.cu

clean:
	rm -f pg

.PHONY: clean
