#!/usr/bin/env bash
# run_sweep.sh — saturate all visible GPUs with the list-size ladder sweep.
# Shards a candidate worst-word list across N GPUs (one persistent worker per GPU).
# Usage:  ./run_sweep.sh <n> <k> [num_gpus]
#   e.g.  ./run_sweep.sh 128 8 8      ./run_sweep.sh 64 8 8
# Output: results/<n>_<k>/<word>.txt  +  a MAX summary printed at the end.
set -euo pipefail
N=${1:?n}; K=${2:?k}; G=${3:-$(nvidia-smi -L 2>/dev/null | wc -l)}; G=${G:-1}
BIN=./ladder
[ -x "$BIN" ] || { echo "build first: nvcc -O3 -arch=sm_90 -o ladder ladder.cu"; exit 1; }
OUT="results/${N}_${K}"; mkdir -p "$OUT"

# candidate worst-case words = GAPPED frequency supports only.
# CONTIGUOUS-band words (consecutive x^{n-1}+x^{n-2}, x^{n-1}+x^k, x^k+x^{k+1}) are PROVABLY
# benign (agreement <= k+1, _ContiguousBandBenign.lean) -- they are NOT floor witnesses, skip them.
# The floor witness has a GAP in {a,b} U {0..k-1}; worst empirically = one small gap near a band edge.
half=$((N/2))
cands=(
  "$((N-1)),$((N-3))"  "$((N-1)),$((N-4))"  "$((N-2)),$((N-4))"    # gap near top edge (n-1,n-3 family)
  "$((N-1)),$((K+1))"  "$((N-1)),$((K+2))"  "$((N-2)),${K}"        # gap between band {0..k-1} and a/b
  "$((N-3)),$((N-5))"  "$((N-1)),$((K+3))"  "$((half+1)),${K}"     # wider gaps
  "$((N-1)),$((half+1))"  "$((half-1)),$((K+1))"  "m${half}"       # spread + antipodal baseline (orbit=const)
)
echo "n=$N k=$K  gpus=$G  candidates=${#cands[@]}"
echo "${cands[@]}" | tr ' ' '\n' > "$OUT/_candidates.txt"

# job pool: assign candidate i to GPU (i % G); keep G workers busy
pids=()
launch(){ local gpu=$1 word=$2; local safe=${word//,/_}; safe=${safe//\//_}
  CUDA_VISIBLE_DEVICES=$gpu $BIN "$N" "$K" "$word" > "$OUT/${safe}.txt" 2>&1 &
  pids+=($!); }
i=0
for w in "${cands[@]}"; do
  gpu=$((i % G))
  # throttle: at most G in flight
  while [ "$(jobs -rp | wc -l)" -ge "$G" ]; do wait -n; done
  echo "  [gpu $gpu] $w"
  launch "$gpu" "$w"
  i=$((i+1))
done
wait
echo "=== MAX list per t across all candidate words (n=$N k=$K) ==="
# collate: for each t, the max L over words
awk '/t=/{ match($0,/t=([0-9]+)/,a); match($0,/L=([0-9]+|OVERFLOW[^ ]*)/,b);
          if(a[1]!=""){ key=a[1]; v=b[1]; if(v=="OVERFLOW"||v=="OVERFLOW(>50000000)") v=999999999;
          if(v+0>max[key]){max[key]=v+0; arg[key]=FILENAME}}}
     END{ n=asorti(max,idx,"@ind_num_desc"); for(j=1;j<=n;j++){ t=idx[j];
          printf "  t=%s  MAX L=%s  @ %s\n", t, max[t], arg[t]} }' "$OUT"/*.txt
echo "results in $OUT/"
