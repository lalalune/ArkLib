#!/usr/bin/env python3
# Extend the anomaly onset-depth r0(n) to n=128 -- the decisive next octave for the
# pinned open question: does r0(n) -> 2 (anomaly cracks the prize rung) or plateau at r0>=3?
# Measured so far (in-tree DISPROOF_LOG): r0 = {16:4, 32:4, 64:3}. n=128 decides the trend.
# Engine REUSED verbatim from the in-tree probe (Ep mod-p r-fold conv + E0_ring char-0 lattice).
# Proper mu_n, in-window beta~4 primes, NEVER n=q-1. Pure-Python exact integer => axiom-clean trivially.
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, E0_ring
import sympy
from functools import reduce
from math import gcd

def roots(n, p):
    g = int(sympy.primitive_root(p)); w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]

def inwin(n, blo=4.0, bhi=4.05, cap=12):
    lo = int(n**blo); hi = int(n**bhi); out = []; m = max(2, lo//n)
    while m*n+1 <= hi and len(out) < cap:
        p = m*n+1
        if p >= lo and sympy.isprime(p): out.append(p)
        m += 1
    return out

n = 128
ps = inwin(n, 4.0, 4.04, 10)
print(f"n={n}: {len(ps)} in-window primes (beta~4), first={ps[0] if ps else None}, last={ps[-1] if ps else None}")
print("Testing prize-relevant rungs r=2,3 (and r=4 if time) for anomaly onset:")
for r in [2, 3, 4]:
    t0 = time.time()
    e0 = E0_ring(n, r)
    worst = 0; nz = 0; witness = None
    for p in ps:
        a = Ep(roots(n, p), p, r) - e0
        if a > 0:
            nz += 1
            if a > worst: worst, witness = a, p
    dt = time.time() - t0
    status = f"ONSET (worst={worst} @ p={witness}, {nz}/{len(ps)} primes nonzero)" if worst > 0 else "anomaly-clean (all 0)"
    print(f"  r={r}: {status}  [{dt:.0f}s]", flush=True)
    if worst > 0:
        print(f"  => r0(128) = {r}.  Trend r0: 16:4, 32:4, 64:3, 128:{r}.")
        if r == 2:
            print("     r0 REACHED THE PRIZE RUNG r=2 -- the bad-prime anomaly now enters at the")
            print("     prize-defining moment. Candidate crack of A_2<=Wick at the worst prize prime.")
        else:
            print(f"     r0 still > 2 at n=128 -- prize rung r=2 stays anomaly-clean in-window.")
        break
else:
    print("  => r0(128) > 4 (no anomaly through r=4 in-window) -- r0 did NOT continue decreasing;")
    print("     prize rung stays clean, trend 64:3 -> 128:>4 is a PLATEAU/REBOUND, not ->2.")
