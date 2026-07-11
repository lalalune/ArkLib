#!/usr/bin/env python3
# RULE-3 GATE on the anomaly onset depth r0(n): is the r=3 onset THINNESS-ESSENTIAL or thickness-generic?
# Plus: does the plateau (r0=3 at n=64,128) hold at n=256 r=2 (next octave of the prize rung)?
# If r0 is the same for thick (non-2-power) n at matched scale, the anomaly onset is thickness-monotone
# => by rule-3 (CORE is FALSE in the thick window) it CANNOT be the prize mechanism.
# Engine REUSED verbatim (Ep mod-p conv + E0_ring char-0 lattice). Exact integer, proper mu_n, NEVER n=q-1.
import sys, os, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, E0_ring
import sympy

def roots(n, p):
    g = int(sympy.primitive_root(p)); w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]

def inwin(n, blo, bhi, cap):
    lo = int(n**blo); hi = int(n**bhi); out = []; m = max(2, lo//n)
    while m*n+1 <= hi and len(out) < cap:
        p = m*n+1
        if p >= lo and sympy.isprime(p): out.append(p)
        m += 1
    return out

def r0_of(n, rmax=4, cap=10):
    ps = inwin(n, 4.0, 4.05, cap)
    if not ps: return None, 0
    for r in range(2, rmax+1):
        e0 = E0_ring(n, r)
        worst = max((Ep(roots(n, p), p, r) - e0 for p in ps), default=0)
        if worst > 0:
            return r, len(ps)
    return f">{rmax}", len(ps)

print("RULE-3 GATE: anomaly onset r0(n) for THIN (2-power) vs THICK (non-2-power 4|n) at matched scale")
print(f"{'n':>5} {'type':>14} {'r0':>5} {'#primes':>8}")
print("-"*40)
# thin 2-power vs thick 4|n composite near matched scales
for (n, desc) in [(32,"thin 2-pow"),(48,"thick 4|n"),(64,"thin 2-pow"),(80,"thick 4|n"),
                  (96,"thick 4|n"),(128,"thin 2-pow"),(112,"thick 4|n")]:
    t0=time.time()
    r0, npr = r0_of(n, rmax=4, cap=8)
    print(f"{n:>5} {desc:>14} {str(r0):>5} {npr:>8}   [{time.time()-t0:.0f}s]", flush=True)
print()
print("READ: if thick 4|n n's have the SAME r0 as thin 2-power n's at matched scale, the anomaly onset")
print("  is thickness-monotone => rule-3 FAIL => the onset depth is NOT a thin-essential prize mechanism.")
print("  if thin n's onset SHALLOWER (smaller r0) than thick => thin-essential signal (rule-3 candidate).")
