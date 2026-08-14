#!/usr/bin/env python3
# FINER RULE-3: the anomaly ONSET DEPTH is thickness-monotone (prior brick). But does the anomaly
# MAGNITUDE structure -- the Anom_3 GCD/multiplier quantization ladder -- carry thin-essential info?
# Test: at the r=3 onset, compare the GCD and multiplier-set of Anom_3 for thin 2-power vs thick 4|n
# at matched scale. If thin n's have a structurally DIFFERENT ladder (finer GCD, distinct multipliers)
# that's a thin-essential candidate; if same ladder structure => thickness-generic, rule-3 FAIL.
# Engine REUSED verbatim. Exact integer, proper mu_n, NEVER n=q-1.
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, E0_ring
import sympy
from functools import reduce
from math import gcd

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

print("RULE-3 on anomaly MAGNITUDE: Anom_3 quantization ladder, thin 2-power vs thick 4|n")
print(f"{'n':>5} {'type':>10} {'#nz/#p':>8} {'GCD':>10} {'GCD factored':>20} {'multipliers':>30}")
print("-"*90)
for (n, desc) in [(64,"thin2pow"),(96,"thick4|n"),(112,"thick4|n"),(128,"thin2pow"),(80,"thick4|n")]:
    ps = inwin(n, 4.0, 4.08, 20)
    e0 = E0_ring(n, 3)
    anoms = [Ep(roots(n, p), p, 3) - e0 for p in ps]
    nz = [a for a in anoms if a > 0]
    if not nz:
        print(f"{n:>5} {desc:>10} {0}/{len(ps)} -- no anomaly at r=3"); continue
    G = reduce(gcd, nz)
    mults = sorted(set(a // G for a in nz))
    print(f"{n:>5} {desc:>10} {len(nz):>3}/{len(ps):<3} {G:>10} {str(dict(sympy.factorint(G))):>20} {str(mults[:8]):>30}", flush=True)
print()
print("READ: if thin and thick share the GCD-factorization pattern (2^a*3*5*7-type) and multiplier ladder")
print("  structure, the anomaly magnitude quantization is thickness-generic too => rule-3 FAIL on magnitude.")
print("  if thin n's GCD has a distinct prime signature / the multiplier ladder differs structurally,")
print("  the anomaly MAGNITUDE (not its onset) could carry thin-essential structure -- a rule-3 candidate.")
