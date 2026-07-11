#!/usr/bin/env python3
"""
Attack the swarm's CLEANEST open-core form (clean-moments bridge, 674243318)
via MY Mann's-theorem lead.

Prize closes iff E_r(mu_n) = #{(x,y) in mu_n^{2r} : sum x_i = sum y_j} is
Gaussian ((2r-1)!! n^r) up to r ~ log p. KEY: sum x_i - sum y_j = 0 is a
VANISHING SUM of 2r roots of unity, so the deviation from Gaussian =
Mann-structured (coset) vanishing sums (Mann 1965/Conway-Jones).

This probe computes, for small n (dyadic mu_n in F_p):
 (1) E_r(mu_n) exactly via Sum_b |eta_b|^{2r} / p (eta_b = Sum_{x in mu_n} e_p(bx));
 (2) the ratio E_r / ((2r-1)!! n^r) [clean=1];
 (3) the b=0 vs b!=0 split (b=0 = n^{2r}/p main term);
 (4) the "structured excess" = E_r minus the trivial-pairing (diagonal) count,
     which by Mann should be coset-supported and o(n^r) when p >> n^r.
Tests whether the deviation is small + Mann-controlled (=> the conjecture and
the Mann attack route are viable) at moderate n,r.
"""
import cmath, math
from itertools import product

def find_prime(n, lo):
    c=(lo//n+1)*n+1
    while True:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=n
def subgroup(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)]
    raise RuntimeError
def df(r):  # (2r-1)!!
    v=1
    for k in range(1,r+1): v*= (2*k-1)
    return v

def Er_via_moments(p, H, r):
    # E_r = Sum_b |eta_b|^{2r} / p, eta_b = Sum_{x in H} e_p(b x)
    n=len(H); tot=0.0
    for b in range(p):
        s=sum(cmath.exp(2j*math.pi*((b*x)%p)/p) for x in H)
        tot += (abs(s)**2)**r
    return tot/p

print("clean-moments test: E_r(mu_n) vs Gaussian (2r-1)!! n^r [clean ratio -> 1]")
print("n   p(>>n^r)   r | E_r        (2r-1)!!n^r    ratio    | b=0 term n^{2r}/p")
for n in (6, 8, 12):
    for r in (2,3,4):
        p=find_prime(n, max(50, 4*n**r))   # p >> n^r so the clean baseline is meaningful
        if p > 4_000_000: 
            print(f"n={n} r={r}: p={p} too big for full Sum_b"); continue
        H=subgroup(p,n)
        Er=Er_via_moments(p,H,r)
        clean=df(r)*n**r
        b0=n**(2*r)/p
        print(f"{n:3d} {p:9d} {r} | {Er:10.1f}  {clean:10.0f}   {Er/clean:6.3f}  "
              f"| {b0:.2f}  {'CLEAN' if abs(Er/clean-1)<0.15 else 'STRUCTURED-EXCESS'}")
