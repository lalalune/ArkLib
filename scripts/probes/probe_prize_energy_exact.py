#!/usr/bin/env python3
"""
EXACT additive energy of mu_{2^mu} (p->infinity clean baseline), free of
finite-p artifacts — the artifact-free Mann attack on the clean-moments core.

For n=2^mu, zeta_n has min poly X^{n/2}+1, so zeta^j -> (+e_j if j<n/2 else
-e_{j-n/2}) in Z^{n/2}. A sum of r roots = a +/-unit-vector sum = integer
vector. E_r^inf(mu_n) = #{(x,y) in mu_n^{2r} : sum x = sum y exactly}
= Sum_v N(v)^2 where N(v) = #{x in mu_n^r : sum x_i = v}.

Compute E_r^inf exactly, compare to the clean/Gaussian baseline, and measure
the growth E_r^inf / n^r vs r (the clean-moments question: is it poly-bounded
= (2r-1)!!-ish, or super-polynomial = structured/fails?). This is the TRUE
clean energy Mann governs; no prime, no contamination.
"""
import math
from collections import Counter
from itertools import product

def df(r):
    v=1
    for k in range(1,r+1): v*=(2*k-1)
    return v
def fact(r):
    return math.factorial(r)

def root_vec(j, half):
    # zeta^j in Z^{half}: +e_j (j<half) or -e_{j-half}
    v=[0]*half
    if j<half: v[j]=1
    else: v[j-half]=-1
    return tuple(v)

def Er_exact(n, r):
    half=n//2
    rv=[root_vec(j,half) for j in range(n)]
    # N(v) = # r-tuples summing to v
    cnt=Counter()
    for tup in product(range(n), repeat=r):
        s=[0]*half
        for j in tup:
            vv=rv[j]
            for t in range(half): s[t]+=vv[t]
        cnt[tuple(s)]+=1
    return sum(c*c for c in cnt.values())

print("EXACT additive energy of mu_{2^mu} (p=inf clean baseline):")
print("n    r | E_r^inf      n^r      E_r/n^r   (2r-1)!!   r!   | verdict")
for mu in (3,4,5):
    n=2**mu
    for r in (2,3,4):
        if n**r > 3_000_000:
            print(f"n={n} r={r}: n^r={n**r} too big"); continue
        E=Er_exact(n,r)
        nr=n**r
        print(f"{n:3d}  {r} | {E:10d}  {nr:8d}  {E/nr:8.2f}  {df(r):6d}  {fact(r):4d}  "
              f"| ratio-to-r!n^r={E/(fact(r)*nr):.3f}")
