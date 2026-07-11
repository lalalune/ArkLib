#!/usr/bin/env python3
"""Probe whether the 2^k TOWER structure gives a provable handle on M = #{u∈μ_n : 1+u∈μ_n}.
Idea: μ_{2^k} closed under squaring. If u,1+u ∈ μ_n, track the squaring orbit of u and of 1+u.
Test: (a) is M bounded by something tower-structural (e.g. #fixed points of a descent map)?
(b) does the squaring map u->u^2 send the solution set {u:1+u∈μ_n} into a SMALLER solution set
(a half-level descent)? If M solutions at level k collapse to <=M/2-ish at level k-1, that's an
elementary recursion proving M small. Empirical only."""
import math
def subgroup_2pow(p,k):
    n=2**k
    if (p-1)%n: return None
    g=None
    for c in range(2,p):
        o=1;y=c%p
        while y!=1:y=(y*c)%p;o+=1
        if o==p-1:g=c;break
    h=pow(g,(p-1)//n,p); return sorted({pow(h,i,p) for i in range(n)})
def solset(p,mu):
    S=set(mu); return [u for u in mu if (1+u)%p in S]
# find primes with 2^k | p-1, n^2 << p
print(f"{'p':>7} {'k':>2} {'n':>5} {'M_k':>4} {'M_{k-1}':>7} {'sq(sol)⊆sol_{k-1}?':>18} {'sol set (sample)'}")
for k in range(3,9):
    n=2**k; target=max(4*n*n,200); p=target
    while True:
        p+=1
        if (p-1)%n: continue
        if all(p%d for d in range(2,int(p**0.5)+1)): break
    muk=subgroup_2pow(p,k)
    if muk is None or len(muk)!=n: continue
    solk=solset(p,muk)
    # level k-1 subgroup = squares of muk = μ_{2^{k-1}}
    muk1=sorted({(x*x)%p for x in muk})
    solk1=solset(p,muk1)
    # is {u^2 : u in solk} ⊆ solk1 ? (does squaring descend solutions?)
    sq_sol=sorted({(u*u)%p for u in solk})
    desc = all(s in set(solk1) for s in sq_sol)
    print(f"{p:>7} {k:>2} {n:>5} {len(solk):>4} {len(solk1):>7} {str(desc):>18}   {solk[:6]}")
