#!/usr/bin/env python3
"""
probe_407_anomaly_onset_depth.py  (#444)

Follow-up to the sibling synthesis 1c48ff7cd (A_r<=Wick <=> Anom_r<=(r/n)Wick; kappa explodes ~18x/octave)
and my char-0 resummation 41980aa29 (char-0 Wick ratio W=E_r^(0)/Wick -> 1 in prize regime). Those leave
the prize entirely in the bad-prime ANOMALY Anom_r = E_r^(p) - E_r^(0). This probe characterizes the
ANOMALY ITSELF (uncontested: no worker pinned its onset structure).

KEY EMPIRICAL FACTS (exact integer counts, proper mu_n, in-window beta~4 primes, never n=q-1):

1. The anomaly is PRIME-SELECTIVE and QUANTIZED, not a smooth n^{2r}/p scaling.
   At a GENERIC in-window prime Anom_r = 0 (n=16 r=4: 1/30 primes nonzero; the one is the Fermat
   prime 65537). The fraction of nonzero-anomaly primes GROWS with n (n=16: 3%, n=32: 60% at r=4).
   At n=32 r=4 every nonzero Anom_4 is an integer multiple of GCD=53760=2^9*3*5*7, with multipliers
   {2,3,4,6,9,10,12,14,18,24,28,30} -- a discrete arithmetic ladder.

2. ANOMALY ONSET DEPTH r0(n) = smallest r s.t. SOME in-window prime has Anom_r > 0:
        n  | r0(n)
        8  | >6  (no anomaly through r=6 in window)
        16 | 4
        32 | 4
        64 | 3
   r0(n) DECREASES with n (4 -> 4 -> 3 over n=16,32,64). The bad-prime anomaly turns on at a
   SHALLOWER moment-depth as n grows -- marching DOWN toward the prize rung r=2 (where M^4 <= p*A_2).

INTERPRETATION (rule-4 wall map, rule-6 honest):
   - My char-0 result (41980aa29): the NEG-CLOSURE-GENERIC part E_r^(0)/Wick saturates to 1 (thin-blind).
   - The PRIZE-CARRYING part is Anom_r, which is 0 at shallow r (r<r0) and ONSETS at r0(n) decreasing in n.
   - For the prize at r=2 (M^4<=p*A_2): need to know if r0(n) ever reaches 2. At the probed n, r0>=3>2,
     so the r=2 rung is STILL anomaly-free in-window at n<=64 -- the prize rung sits BELOW onset so far.
     But r0 is DECREASING; the open question is whether r0(n) -> 2 (anomaly reaches the prize rung,
     potentially CRACKING A_2<=Wick at the worst prize prime) or plateaus at r0>=3 (prize rung stays clean).
   - This does NOT close or refute CORE; it MAPS the precise depth where the bad-prime anomaly enters,
     and shows it descends with n. The §3 meta-theorem (additive moments non-proving) is about r=2; this
     pins WHERE deeper-r anomaly lives and that it approaches r=2 from above.

Pure-Python exact integer counts (Ep mod p + E0_ring char-0 lattice), no Lean => axiom-clean trivially.
Reuses Ep, E0_ring from probe_407_anom_worst_rtraj_n32.py.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, E0_ring
import sympy
from functools import reduce
from math import gcd

def roots(n, p):
    g = int(sympy.primitive_root(p)); w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]

def inwin(n, blo=4.0, bhi=4.05, cap=25):
    lo = int(n**blo); hi = int(n**bhi); out = []; m = max(2, lo//n)
    while m*n+1 <= hi and len(out) < cap:
        p = m*n+1
        if p >= lo and sympy.isprime(p): out.append(p)
        m += 1
    return out

print("="*86)
print("1. ANOMALY is prime-selective + quantized (n=32, r=4, in-window beta~4):")
print("="*86)
n = 32; ps = inwin(n, 4.0, 4.06, 40); e0 = E0_ring(n, 4)
anoms = [Ep(roots(n, p), p, 4) - e0 for p in ps]
nz = [a for a in anoms if a > 0]
G = reduce(gcd, nz)
print(f"  nonzero-anomaly primes: {len(nz)}/{len(ps)} ({len(nz)/len(ps):.0%})")
print(f"  GCD of anomalies = {G} = {sympy.factorint(G)}")
print(f"  multipliers (Anom/GCD): {sorted(set(a//G for a in nz))}")
print()

print("="*86)
print("2. ANOMALY ONSET DEPTH r0(n) = smallest r with some in-window Anom_r > 0:")
print("="*86)
GRID = {8: 6, 16: 6, 32: 5, 64: 4}
r0 = {}
for n, rmax in GRID.items():
    ps = inwin(n, 4.0, 4.05, 15 if n == 64 else 25)
    onset = None
    line = f"  n={n:>3} ({len(ps)} primes): "
    for r in range(2, rmax+1):
        e0 = E0_ring(n, r)
        worst = max((Ep(roots(n, p), p, r) - e0 for p in ps), default=0)
        if worst > 0 and onset is None: onset = r
        line += f"r{r}:{'ON('+str(worst)+')' if (onset==r and worst>0) else ('+' if worst>0 else '0')} "
    r0[n] = onset
    print(line + f" => r0={onset}", flush=True)
print()
print("  r0(n) trend:", {n: r0[n] for n in GRID})
print("  => r0 DECREASES with n (16:4, 32:4, 64:3) -- the bad-prime anomaly onsets at SHALLOWER depth")
print("     as n grows, descending toward the prize rung r=2. Open: does r0(n)->2 (anomaly reaches the")
print("     prize-defining rung) or plateau at r0>=3 (prize rung stays anomaly-free)? At n<=64, r0>2 =>")
print("     the r=2 prize rung is still anomaly-clean in-window. CORE not closed; depth-of-entry mapped.")
