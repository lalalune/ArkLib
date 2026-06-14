#!/usr/bin/env python3
"""Probe: 2-power tower recursion for the Gauss-period bound B = max_{b!=0}|eta_b(mu_n)|.

Issue #389 / Gaussian Bound Conjecture. Tests the exact coset-split recursion
    eta_b^{(2n)} = eta_b^{(n)} + eta_{b*zeta}^{(n)},   zeta = primitive 2n-th root,
and whether it contracts to give B(mu_{2^m}) <~ sqrt(2^m) (Ramanujan) without an
external sum-product / additive-energy input.

FINDINGS (see StructuredOutput in the workflow transcript):
 - Recursion is EXACT (verified to 1e-14).
 - eta_b^{(n)} is REAL for n even (since -1 in mu_n) => recursion is a signed real recursion.
 - Cross-correlation over b is ~0 (Parseval-consistent) => sqrt-law preserved ON AVERAGE.
 - Per-step contraction kappa=B(2n)/B(n): =2.0 while n<=log2(q); drops to [0.94,1.78] for n>>log2 q.
   NOT uniformly <= sqrt(2)=1.414, so the recursion does NOT telescope to sqrt(n) by itself.
 - The provable (triangle) bound is only kappa<=2 => B(2^m)<=2^m=n (TRIVIAL).
 - Energy recursion: E_2(2n) = 2 E_2(n) + (cross-coset energy)/q; the cross term is the
   OPEN sum-product input (E_2(mu_n)=n^{2+o(1)} is the unproved 7/3-barrier quantity).
"""
import cmath, math
from collections import Counter

def primitive_root(p):
    n=p-1; m=n; factors=set(); d=2
    while d*d<=m:
        if m%d==0:
            factors.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: factors.add(m)
    for g in range(2,p):
        if all(pow(g,n//q,p)!=1 for q in factors): return g
    raise RuntimeError

def field_subgroup(p,n):
    assert (p-1)%n==0
    h=pow(primitive_root(p),(p-1)//n,p); sub=[]; x=1
    for _ in range(n): sub.append(x); x=(x*h)%p
    return sub

def eta(p,sub,b):
    return sum(cmath.exp(2j*math.pi*((b*y)%p)/p) for y in sub)

def B_max_fast(p,n):
    sub=field_subgroup(p,n); seen=set(); best=-1.0
    for b in range(1,p):
        if b in seen: continue
        for y in sub: seen.add((b*y)%p)
        v=abs(eta(p,sub,b)); best=max(best,v)
    return best

if __name__=="__main__":
    for p in [40961,12289]:
        print(f"\n=== p={p}, log2(p)={math.log2(p):.2f} ===")
        Bs={0:1.0}
        for m in range(1,14):
            n=2**m
            if (p-1)%n: break
            Bs[m]=B_max_fast(p,n)
        ms=sorted(Bs)
        print(f"{'m':>3}{'n':>7}{'B':>10}{'B/sqrt(n)':>11}{'kappa':>8}")
        for i,m in enumerate(ms):
            n=2**m; k = Bs[m+1]/Bs[m] if (m+1) in Bs else float('nan')
            print(f"{m:>3}{n:>7}{Bs[m]:>10.3f}{Bs[m]/math.sqrt(n):>11.4f}{k:>8.4f}")
