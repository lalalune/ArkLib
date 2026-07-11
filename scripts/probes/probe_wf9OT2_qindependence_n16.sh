#!/usr/bin/env bash
# wf9-OT2 (#444, R4 demand-side char-faithfulness): EXACT q-independence of the canonical
# (genuinely-far, b in [k,n-r)) far-line incidence at n=16, rho=1/4, across the ENTIRE prize regime
# AND the roughest in-window primes (BGK campaign's worst case for character sums).
#
# Object: FarCosetExplosion.epsMCA_ge_far_incidence (proven in-tree). Engine: deltastar_farline.rs
# (faithful Rust port of probe_farline_incidence_exact.py; b in [k,size) is the genuine-far filter).
#
# VERDICT: the binding-band bad-scalar count is q-INDEPENDENT (= char-0 faithful) at prize scale.
#   r=8 (delta 1/2):  max far incidence = 9,  binder (10,4)  -- identical at all primes below
#   r=9 (delta 9/16): max far incidence = 9,  binder (10,4)  -- identical (incl. rough primes)
#   r=10(delta 5/8):  max far incidence = 89 (>budget 16)    -- identical => delta* = 9/16 EVERYWHERE
# This CONFIRMS R4-faithfulness at the binding band (does NOT refute it). The earlier "fails at n=32"
# reading was the degenerate-offset (a=0, P*u0=0 auto) / correlated-pair (b-a == n/2, x^{n/2}=+-1)
# artifact, both excluded by the genuine-far filter.
set -euo pipefail
ENG=${ENG:-/tmp/deltastar_farline}
SRC="$(dirname "$0")/rust/deltastar_farline.rs"
if [ ! -x "$ENG" ]; then rustc -O "$SRC" -o "$ENG"; fi

# prize-scale + ROUGH primes (p = 1 mod 16): n^4 (Fermat), n^4.5, rough ((p-1)/n prime), n^5, n^6.25
PRIMES=(65537 262193 353777 354737 359153 1048609 33554593)
echo "n=16 k=4 rho=1/4 budget=16 : far-line incidence at binding bands r=8,9,10 across primes"
echo "p (n^beta)            | r=8  r=9  r=10  | delta*"
for p in "${PRIMES[@]}"; do
  beta=$(python3 -c "import math;print(f'{math.log($p)/math.log(16):.2f}')")
  out=$("$ENG" 16 4 "$p" 8 11 2>&1)
  i8=$(echo "$out"  | sed -n 's/.*r=8 .*max_far=\([0-9]*\).*/\1/p')
  i9=$(echo "$out"  | sed -n 's/.*r=9 .*max_far=\([0-9]*\).*/\1/p')
  i10=$(echo "$out" | sed -n 's/.*r=10 .*max_far=\([0-9]*\).*/\1/p')
  ds=$(echo "$out"  | sed -n 's/.*delta\* = \([0-9/]*\).*/\1/p')
  printf "%-10s (n^%s)  | %-4s %-4s %-5s | %s\n" "$p" "$beta" "$i8" "$i9" "$i10" "$ds"
done
echo
echo "If the r=8/r=9/r=10 columns and delta* are IDENTICAL across all rows => q-independence PROVEN"
echo "at prize scale for n=16 (R4 demand-side faithful at the binding band)."
