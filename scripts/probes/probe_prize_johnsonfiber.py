#!/usr/bin/env python3
"""
NEW (2nd-slate top) attack: the Johnson-scale esymm fiber.

The deep-band explosion is centralBinom(s) cores at SMALL m (radius k+m+1
near capacity). At JOHNSON-scale radius a ~ sqrt(k*n), we need m+1 ~ a
vanishing elementary-symmetric conditions e_1(T)=...=e_{m+1}(T)=0 on
a-subsets T of mu_n. These OVER-DETERMINE T (m+1 ~ a conditions on an
a-subset), so the fiber should be SMALL -- the positive direction the
BGK analysis pointed to.

m_T(X) = prod_{t in T}(X-t) | X^n - 1 (T subset mu_n). e_1=...=e_j=0 means
m_T = X^a + (degree <= a-j-1 terms): the top j coeffs below the lead vanish.
COUNT such T, sweeping a near Johnson and j up to a-k, in dyadic mu_n.
If poly(n) => Johnson-scale list poly => prize winnable (new lead!).
If exponential => dead.

Computable: brute over a-subsets (C(n,a)) checking top-j esymm, moderate n.
"""
import itertools, math
from collections import Counter

def find_prime(n, lo=200):
    c=(lo//n+1)*n+1
    while True:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=n
def smooth(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)]
    raise RuntimeError

def esym_top(roots, p, j):
    """return (e_1,...,e_j) mod p of the multiset roots."""
    # build poly coeffs via prod (X - r); e_i = (-1)^i * coeff[a-i]
    a=len(roots); poly=[1]
    for r in roots:
        new=[0]*(len(poly)+1)
        for i,c in enumerate(poly):
            new[i]=(new[i]+c)%p
            new[i+1]=(new[i+1]-r*c)%p
        poly=new
    # poly[a-i] is coeff of X^{a-i}; e_i = (-1)^i poly[a-i]
    return tuple(((-1)**i*poly[a-i])%p for i in range(1,j+1))

def fiber_count(D, p, a, j):
    """# a-subsets T of D with e_1(T)=...=e_j(T)=0."""
    cnt=0
    for T in itertools.combinations(D, a):
        if all(e==0 for e in esym_top(list(T), p, j)):
            cnt+=1
    return cnt

print("dyadic mu_n: Johnson-scale esymm-fiber counts (over-determined regime)")
print("n   a(~Johnson)  j  | #{a-subsets with e_1..e_j = 0}")
for n in (12,16,20,24):
    p=find_prime(n); D=smooth(p,n); k=3
    aJ=math.isqrt(k*n)  # Johnson agreement
    for a in (aJ-1, aJ):
        if a<k+1 or a>n: continue
        if math.comb(n,a) > 3_000_000: 
            print(f"  n={n} a={a}: C(n,a)={math.comb(n,a)} too big"); continue
        # j = m+1 up to a-k (deep over-determination)
        for j in (max(1,a-k), a-1):
            if j<1 or j>=a: continue
            fc=fiber_count(D,p,a,j)
            print(f"  n={n:3d}  a={a:3d}  j={j:3d} | fiber={fc}  (C(n,a)={math.comb(n,a)})")
