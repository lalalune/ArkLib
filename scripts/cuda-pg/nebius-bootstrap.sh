#!/bin/bash
# cloud-init user-data for a Nebius GPU instance: build the delta* engines, validate
# the CUDA kernel against the Rust reference, then run the big search.  Logs to
# /var/log/pg-bootstrap.log; results land in /root/pg-results/.
#
# Used by nebius-launch.sh via --cloud-init-user-data.  Idempotent-ish; safe to re-run.
set -eux
exec > /var/log/pg-bootstrap.log 2>&1
export DEBIAN_FRONTEND=noninteractive

# --- toolchain -------------------------------------------------------------
if ! command -v nvcc >/dev/null 2>&1; then
  apt-get update -y
  apt-get install -y build-essential git curl wget
  if ! apt-get install -y nvidia-cuda-toolkit; then
    # fallback to NVIDIA apt repo (Ubuntu 22.04) if distro toolkit is too old/absent
    . /etc/os-release || true
    wget -q "https://developer.download.nvidia.com/compute/cuda/repos/ubuntu2204/x86_64/cuda-keyring_1.1-1_all.deb"
    dpkg -i cuda-keyring_1.1-1_all.deb
    apt-get update -y && apt-get install -y cuda-toolkit
  fi
fi
export PATH="/usr/local/cuda/bin:$PATH"
command -v cargo >/dev/null 2>&1 || { curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y; }
. "$HOME/.cargo/env" || true

# --- detect GPU arch -> nvcc -arch ----------------------------------------
CC=$(nvidia-smi --query-gpu=compute_cap --format=csv,noheader 2>/dev/null | head -1 | tr -d '.')
case "$CC" in
  89) ARCH=sm_89 ;;          # L40S (Ada)
  90) ARCH=sm_90a ;;         # H100 / H200 (Hopper)
  100|103) ARCH=sm_100a ;;   # B200 (Blackwell DC)
  120) ARCH=sm_120 ;;        # RTX 50xx (Blackwell consumer)
  *)  ARCH=native ;;
esac
echo "GPU compute_cap=$CC -> ARCH=$ARCH"

# --- fetch repo + build ----------------------------------------------------
cd /root
[ -d ArkLib ] || git clone --depth 1 https://github.com/lalalune/ArkLib.git
cd ArkLib/scripts
( cd rust-pg && cargo build --release )
cd cuda-pg
make ARCH="$ARCH"

mkdir -p /root/pg-results
RES=/root/pg-results

# --- 1) validate CUDA vs Rust on small n (correctness gate) ---------------
./validate.sh 2>&1 | tee "$RES/validate.out" || echo "VALIDATION FAILED — see above" | tee -a "$RES/validate.out"

# --- 2) n=32 p-dependence correctness target (cross-witness gamma) --------
# dir-max over-determined incidence at k=2,s=4 must be p-dependent: 897 at most
# primes, 705 at p=32993. (Confirms the kernel handles cross-witness dedup.)
{
  echo "## n=32 k=2 p-dependence (expect maxI 897 at 32801/32833/65537, 705 at 32993):"
  for pr in 32801 32833 32993 65537; do
    echo "--- p=$pr ---"; ./pg 32 2 0 "$pr" | grep -E "s=4 |=>" || ./pg 32 2 0 "$pr" | head -6
  done
} 2>&1 | tee "$RES/pdep32.out"

# --- 3) the big delta* search (the point of renting the box) --------------
# prize rate rho=1/4 across n; raise cap so the sweep can reach the binding.
{
  for nk in "32 8" "36 9" "40 10" "44 11"; do
    set -- $nk
    echo "===== n=$1 k=$2 (rho=1/4) ====="
    timeout 36000 ./pg "$1" "$2" 200000000000 || echo "  (timed out / cap hit)"
  done
} 2>&1 | tee "$RES/deltastar-rho4.out"

# --- 4) binding p-(in)dependence scan: same n,k across 3 primes -----------
# resolves the open gap in the decoupling refutation (is delta* itself p-dependent?).
{
  for nk in "24 6" "28 7" "32 8"; do
    set -- $nk; n=$1; k=$2
    primes=$(python3 - "$n" <<'PY'
import sys
n=int(sys.argv[1])
def isp(x):
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return x>1
base=n**4; f=[]; p=base
while len(f)<3:
    if p%n==1 and isp(p): f.append(p)
    p+=1
print(*f)
PY
)
    echo "### n=$n k=$k  primes: $primes"
    for pr in $primes; do
      echo "  -- p=$pr --"; timeout 36000 ./pg "$n" "$k" 200000000000 "$pr" | grep "=>" || echo "  (no s* / timeout)"
    done
  done
} 2>&1 | tee "$RES/binding-pdep.out"

echo "BOOTSTRAP_DONE" | tee "$RES/DONE"
