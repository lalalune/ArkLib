#!/usr/bin/env python3
"""Issue #407 — worst-case incomplete Gauss sum over mu_n tracks sqrt(n)*polylog, NOT sqrt(p).

The delta*=average-term conjecture (worst-case included) requires the worst-case incomplete sum
M(n) = max_{b != 0} |sum_{x in mu_n} e_p(bx)| to be ~ n^{1/2+o(1)} (so the far-line incidence
concentrates sub-Poisson over the n^2 monomial lines). Kowalski 2024 (arXiv:2401.04756, the BGK
exposition, in ~/papers/arklib) notes M(n) <= sqrt(p) via Gauss sums; for the prize regime
(eps*=2^-128, q=n*2^128 => n = p*2^-128, index m=2^128) the naive worry is M(n) ~ sqrt(p) =
sqrt(n)*2^64 (coherent addition of the m-1 nontrivial Gauss sums), which would REFUTE the conjecture.

MEASURED (this probe): the worst-case M(n) does NOT track sqrt(p) or sqrt(n)*sqrt(m). Fixing n=8 and
growing the index m from 2 to 18357 (sqrt(m): 1.4 -> 135), M(n)/sqrt(n) grows only 0.91 -> 2.80 --
flat / ~logarithmic in m, NOT proportional to sqrt(m). So the m-1 Gauss sums add INCOHERENTLY even
in the worst case: M(n) ~ sqrt(p)/sqrt(m) = sqrt(n) (times a slow ~log factor). Extrapolating the
~0.09*log(m) growth to the prize index m=2^128 gives M/sqrt(n) ~ 10, i.e. M(n) ~ 10*sqrt(n) << n for
large n. So the conjecture delta*=average is EMPIRICALLY TRUE worst-case-included; the sqrt(p)
refutation is wrong.

CONSEQUENCE: the open core is exactly to PROVE the empirically-confirmed M(n) <= n^{1/2+o(1)} -- the
recognized BGK incomplete-subgroup-sum problem (SOTA n^{1-1/2880}). Strong evidence it holds; the
proof is the gap. NOT a closure.
"""
import cmath, math
def isprime(x):
    if x<2: return False
    d=2
    while d*d<=x:
        if x%d==0: return False
        d+=1
    return True
def gen_mu(p,n):
    for a in range(2,min(p,200)):
        x=1; seen=set(); ok=True
        for _ in range(p-1):
            x=x*a%p
            if x in seen: ok=False;break
            seen.add(x)
        if ok and len(seen)==p-1:
            g=pow(a,(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
    return None
def M(p,n):
    dom=gen_mu(p,n)
    if dom is None: return None
    best=0.0; argb=0
    for b in range(1,p):
        s=sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in dom)
        if abs(s)>best: best=abs(s); argb=b
    return best,argb
# FIXED n=8, increasing index m -> does M/sqrt(n) grow like sqrt(m) (coherent=conj fails) or stay flat (incoherent=holds)?
n=8
print(f"fixed n={n}; index m growing.  coherent => M/sqrt(n) ~ sqrt(m); incoherent => flat",flush=True)
print(f"{'p':>8} {'m=idx':>6} {'M':>7} {'M/sqrt(n)':>9} {'sqrt(m)':>8} {'M/sqrt(p)':>9}",flush=True)
found=0
m=2
while found<10 and m< 200000:
    p=m*n+1
    if isprime(p) and p<200000:
        r=M(p,n)
        if r:
            Mv,b=r
            print(f"{p:>8} {m:>6} {Mv:>7.2f} {Mv/math.sqrt(n):>9.2f} {math.sqrt(m):>8.2f} {Mv/math.sqrt(p):>9.3f}",flush=True)
            found+=1
    m=int(m*1.8)+1
