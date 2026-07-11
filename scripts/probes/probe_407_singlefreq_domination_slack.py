#!/usr/bin/env python3
# The wickbound-capability pin reduces the prize to A_{r*} <= Wick at r*~log m, via the
# SINGLE-FREQUENCY-DOMINATES step: M^{2r} <= sum_b |eta_b|^{2r} = p*A_r, tight when r >~ log(#freqs).
# This probe measures the DOMINATION SLACK ratio D_r := (p*A_r)^{1/2r} / M, i.e. how much the moment
# (p*A_r)^{1/2r} OVERSHOOTS the true sup M at finite r -- and whether that slack is THIN-ESSENTIAL.
# If thin mu_n has SMALLER slack (the max freq dominates more cleanly -> fewer competing big freqs),
# a thin advantage could hide in the domination step itself (not the Wick value). Rule-3 gated.
# Exact real periods eta_b (mu_n neg-closed => real), proper mu_n, NEVER n=q-1.
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sympy

def periods(n, p):
    # eta_b const on cosets b*mu_n. The (p-1)/n distinct values = eta over coset reps.
    # Coset reps = a transversal of mu_n in F_p^*. Generate via primitive root h of F_p^*:
    # mu_n = <h^{(p-1)/n}>; cosets indexed by h^j, j=0..(p-1)/n-1. b = h^j is a full rep set.
    g = int(sympy.primitive_root(p)); w = pow(g, (p-1)//n, p)
    mu = [pow(w, i, p) for i in range(n)]
    m = (p-1)//n  # number of cosets
    etas = []
    hj = 1
    for j in range(m):
        b = hj
        s = sum(math.cos(2*math.pi*((b*x) % p)/p) for x in mu)
        etas.append(s)
        hj = (hj * g) % p
    return etas  # (p-1)/n distinct coset values, each computed once

def slack(n, p, rmax=8):
    etas = periods(n, p)
    M = max(abs(e) for e in etas)
    out = []
    for r in range(1, rmax+1):
        Ar = sum(abs(e)**(2*r) for e in etas)  # = p*A_r over coset reps... use sum over reps (proportional)
        # (p*A_r)^{1/2r} vs M: use the rep-sum^{1/2r}; D_r = (sum)^{1/2r}/M, ->1 as r->inf
        D = (Ar)**(1/(2*r)) / M
        out.append(D)
    return M, out

print("SINGLE-FREQ DOMINATION SLACK D_r = (sum_b|eta_b|^2r)^{1/2r} / M  (->1 as r grows; rule-3 thin vs thick)")
print(f"{'n':>4} {'type':>10} {'p':>9}   D_1   D_2   D_3   D_4   D_5   D_6")
print("-"*70)
for (n, desc) in [(16,"thin2pow"),(24,"thick4|n"),(32,"thin2pow"),(48,"thick4|n"),(64,"thin2pow"),(40,"thick4|n")]:
    # proper-subgroup prime, beta~3 (kept moderate for tractability; D_r is scale-stable)
    lo=int(n**3.0); m=max(2,lo//n); p=None
    while p is None:
        if (m*n+1)>=lo and sympy.isprime(m*n+1): p=m*n+1
        m+=1
    M, Ds = slack(n, p, 6)
    print(f"{n:>4} {desc:>10} {p:>9}  " + " ".join(f"{d:.3f}" for d in Ds), flush=True)
print()
print("READ: D_r -> 1 as r grows (single freq dominates). The wickbound pin needs r*~log m for D~1.")
print("  rule-3: if thin n's D_r approaches 1 FASTER (smaller slack at fixed r) than thick at matched scale,")
print("  the domination step is thin-favorable -- a candidate thin-essential edge. If thin/thick same curve,")
print("  the domination slack is thickness-generic (no hidden thin advantage in the single-freq step).")
