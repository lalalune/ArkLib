#!/usr/bin/env python3
"""probe_cstar_extrapolation_underdetermined.py  (#444 ASYMPTOTIC-CLAIM GUARD)

DecouplingCrossingDepthGrowsInN.lean asserts (prose + framing) from the 6-point table
  cStarQuarter(n) = [3,4,3,4,5,5] at n = [8,12,16,20,24,32]
the ASYMPTOTIC LAW "c*(n)/n -> 0" and hence "delta* -> capacity (3/4)" / "off-BGK survives".

The brief's ASYMPTOTIC-CLAIM GUARD (Shaw's growth-law-conflict resolution) says this reading is
UNJUSTIFIED: a sub-leading O(log n) dip in the small-n tail is NOT a sub-linear LAW.

THIS PROBE: a finite data table CANNOT pin the asymptotic RATE. We show BOTH a bounded/sub-linear law
(c*/n -> 0) AND a genuinely LINEAR law with positive slope (c*/n -> const > 0) fit the SAME 6 points
within the +-1 parity granularity the file itself invokes for its {3,4} wobble. Two laws with OPPOSITE
asymptotics => the table does NOT entail c*/n -> 0 => the file's capacity/off-BGK conclusion is an
asymptotic OVER-CLAIM. (Rule 4: a precisely-mapped over-claim with a constraint = a result.)

HONEST NOTE: the PURE cliff floor(n/4) (s* fully hugging s_top=floor(n/2)) OVERSHOOTS the table at
large n -- the table sits BELOW the full cliff, i.e. the O(log) dip is real at small n. So we do NOT
claim s* hugs the cliff exactly; we claim only that a POSITIVE-SLOPE linear law (slope ~1/10) fits the
table just as well as a bounded one, so the rate is under-determined.
"""
N   = [8, 12, 16, 20, 24, 32]
CS  = [3,  4,  3,  4,  5,  5]
import math

def maxres(f):
    return max(abs(c - round(f(n))) for n, c in zip(N, CS))

laws = {
    "log2(n)-1          (sub-linear)":  lambda n: math.log2(n) - 1.0,
    "1.5*ln(n)-0.1      (sub-linear)":  lambda n: 1.5*math.log(n) - 0.1,
    "const 4            (bounded)":     lambda n: 4.0,
    "n/10 + 2 (int)     (LINEAR int)":  lambda n: n//10 + 2,
    "0.10*n + 2.5       (LINEAR)":      lambda n: 0.10*n + 2.5,
    "0.12*n + 2.2       (LINEAR)":      lambda n: 0.12*n + 2.2,
    "floor(n/4)         (PURE cliff)":  lambda n: n//4,
}

print(f"{'law':<36} {'max|resid|':>10}   fits(<=1)?")
print("-"*62)
fits = {}
for name, f in laws.items():
    r = maxres(f)
    fits[name] = r <= 1
    print(f"{name:<36} {r:>10.3f}   {'YES' if r<=1 else 'no'}")

print()
sublin = [k for k in laws if ('sub-linear' in k or 'bounded' in k) and fits[k]]
linear = [k for k in laws if 'LINEAR' in k and fits[k]]
purecliff_fits = fits["floor(n/4)         (PURE cliff)"]
print(f"sub-linear (c*/n->0) laws fitting (<=1): {len(sublin)}  {sublin}")
print(f"LINEAR (c*/n->const>0) laws fitting (<=1): {len(linear)}  {linear}")
print(f"PURE cliff floor(n/4) fits (<=1)? {purecliff_fits}  (expect NO -- overshoots large n)")
print()
if sublin and linear:
    print("VERDICT: the 6-point table is UNDER-DETERMINED -- both a c*/n->0 law AND a positive-slope")
    print("LINEAR law (c*/n->const>0) fit within +-1. => DecouplingCrossingDepthGrowsInN's")
    print("'c*/n->0 / delta*->capacity / off-BGK survives' is an asymptotic OVER-CLAIM. CONFIRMED.")
else:
    print("VERDICT: not both fit -- re-examine.")

print()
print("Per-n: integer linear law n//10+2 vs cStar (the Lean-formalized witness):")
for n, c in zip(N, CS):
    lin = n//10 + 2
    print(f"  n={n:3d}: cStar={c}  n//10+2={lin}  |diff|={abs(c-lin)}  (ratio lin/n={lin/n:.3f})")
print("  => slope 1/10 > 0: c*/n -> 1/10 != 0 under this fit (vs bounded law's c*/n -> 0).")
