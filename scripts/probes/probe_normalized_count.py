#!/usr/bin/env python3
"""Validate the open sum-product target: N = #{(z1,z2,z3)∈G³ : z1+z2=z3+1} for a multiplicative
subgroup G=⟨ω⟩ of order n in F_p. The reduction (AddEnergyMulHomogeneous) gives E(G)=|G|·N; the
prize needs N ≪ n^{3/2} (⟺ E(G)≪n^{5/2}, Heath-Brown-Konyagin/Shkredov). Confirm N is sub-quadratic
(beats the elementary n²) and tracks n^{3/2} for smooth subgroups, vs ~n²-scale for a random set."""
import itertools, math, random
random.seed(11)
def subgroup(p,n):
    for cand in range(2,p):
        o=1;y=cand%p
        while y!=1:y=(y*cand)%p;o+=1
        if o==p-1:g=cand;break
    if (p-1)%n: return None
    h=pow(g,(p-1)//n,p); return sorted({pow(h,i,p) for i in range(n)})
def Ncount(p,G):
    Gset=set(G); N=0
    for z1 in G:
        for z2 in G:
            z3=(z1+z2-1)%p
            if z3 in Gset: N+=1
    return N
print(f"{'p':>6} {'n':>4} {'N(smooth)':>10} {'n^1.5':>8} {'n^2':>6} {'N/n^1.5':>8} | {'N(random)':>10} {'N_r/n^1.5':>9}")
cases=[(13,6),(41,8),(41,10),(73,8),(73,9),(97,12),(151,15),(241,16),(337,21),(673,24),(1009,28)]
for (p,n) in cases:
    G=subgroup(p,n)
    if G is None or len(G)!=n: continue
    N=Ncount(p,G)
    R=sorted(random.sample(range(1,p),n)); Nr=Ncount(p,R)
    n15=n**1.5
    print(f"{p:>6} {n:>4} {N:>10} {n15:>8.1f} {n*n:>6} {N/n15:>8.3f} | {Nr:>10} {Nr/n15:>9.3f}")
