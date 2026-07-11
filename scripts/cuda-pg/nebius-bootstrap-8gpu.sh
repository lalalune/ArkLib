#!/bin/bash
set -ex
export HOME=/root
export PATH=/usr/local/cuda/bin:/root/.cargo/bin:$PATH
export DEBIAN_FRONTEND=noninteractive
exec > /var/log/pg-bootstrap.log 2>&1
apt-get update -y && apt-get install -y git build-essential curl python3
command -v cargo >/dev/null 2>&1 || curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh -s -- -y
export PATH=/root/.cargo/bin:$PATH
cd /root; rm -rf ArkLib
git clone --depth 1 https://github.com/lalalune/ArkLib.git
cd ArkLib/scripts && ( cd rust-pg && cargo build --release )
cd cuda-pg && make ARCH=sm_90a            # H100 = Hopper sm_90a
mkdir -p /root/pg-results; RES=/root/pg-results
nvidia-smi --query-gpu=index,name --format=csv,noheader > "$RES/gpus.txt"
# correctness gate (GPU0)
CUDA_VISIBLE_DEVICES=0 ./validate.sh > "$RES/validate.out" 2>&1 || true
# multi-GPU rho=1/4 sweep: one config per GPU, time-boxed 20min each, all parallel
CFG=( "32 8" "34 9" "36 9" "38 10" "40 10" "42 11" "44 11" "48 12" )
for g in 0 1 2 3 4 5 6 7; do
  set -- ${CFG[$g]}; n=$1; k=$2
  ( CUDA_VISIBLE_DEVICES=$g timeout 1200 ./pg "$n" "$k" 500000000000 \
      > "$RES/dstar_n${n}_k${k}.out" 2>&1 || echo "  (timeout/cap)" >> "$RES/dstar_n${n}_k${k}.out" ) &
done
wait
# binding p-dependence scan on GPU0 (n=24,28,32 across 3 primes) once sweep frees up
{ for nk in "24 6" "28 7" "32 8"; do set -- $nk; n=$1; k=$2;
  ps=$(python3 -c "
def isp(x):
 d=2
 while d*d<=x:
  if x%d==0: return False
  d+=1
 return x>1
n=$n;b=n**4;f=[];p=b
while len(f)<3:
 if p%n==1 and isp(p): f.append(p)
 p+=1
print(*f)")
  echo "### n=$n k=$k primes: $ps"
  for pr in $ps; do echo " p=$pr:"; CUDA_VISIBLE_DEVICES=0 timeout 1200 ./pg "$n" "$k" 500000000000 "$pr" | grep "=>" || echo timeout; done
done; } > "$RES/binding-pdep.out" 2>&1
grep -h "=>" "$RES"/dstar_*.out > "$RES/SUMMARY.txt" 2>/dev/null || true
echo ALLDONE > "$RES/DONE"
