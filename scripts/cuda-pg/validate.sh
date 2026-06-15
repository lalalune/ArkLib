#!/usr/bin/env bash
# Validate the CUDA delta* engine against the Rust reference (scripts/rust-pg) on
# small n where the CPU is fast and gives exact ground truth. Compares the binding
# s*, delta*, and per-s maxI lines (the answer-bearing output), ignoring the argmax
# (a,b) tuple which can differ on ties.
#
# Usage: ./validate.sh            # default cases n=8,12,16,20
#        ./validate.sh 24 6 ...   # custom "n k" pairs
set -euo pipefail
cd "$(dirname "$0")"

RUST=../rust-pg/target/release/pg
[ -x "$RUST" ] || { echo "building rust reference..."; (cd ../rust-pg && cargo build --release); }
[ -x ./pg ]   || { echo "building cuda engine..."; make; }

# extract the comparable signal: every "s=.. maxI=.. GOOD/bad" and the final "=> s*.. delta*.."
norm() { grep -E '^\s+(s=|=> s\*)' | sed -E 's/ at \([0-9]+, [0-9]+\)//'; }

CASES=("${@:-8 4 12 3 16 4 20 5}")
# reflow into pairs
set -- ${CASES[@]:-8 4 12 3 16 4 20 5}
fail=0
while [ $# -ge 2 ]; do
  n=$1; k=$2; shift 2
  echo "=== n=$n k=$k ==="
  r=$("$RUST" "$n" "$k" | norm)
  c=$(./pg "$n" "$k" | norm)
  if [ "$r" == "$c" ]; then
    echo "  MATCH"; echo "$c" | sed 's/^/    /'
  else
    echo "  MISMATCH"; fail=1
    diff <(echo "$r") <(echo "$c") | sed 's/^/    /' || true
  fi
done
echo
[ $fail -eq 0 ] && echo "ALL MATCH — CUDA engine validated against Rust." || { echo "VALIDATION FAILED"; exit 1; }
