#!/usr/bin/env python3
"""
probe_dsj_sstar_two_formulas.py  (#444, register CROSS-DOMAIN-DYNAMICS)

ADVERSARIAL CHECK of the prompt's pinned threshold formula
    s*(n) = n/2 + 1 - 2*(log2 n - 3)
against the in-tree FloorAsymptoticRadius claim  s*/n = 5/8 (constant).

These give DIFFERENT numbers for n>=16 (7 vs 10 at n=16). I want to know:
  (a) what is the MAX number of roots a sparse poly with s monomials can have on mu_n?
      (the "sparse-zero radius" = FloorAsymptotic object)
  (b) what is the worst-direction OVER-DETERMINED far-line incidence
      (max agreement of a degree<k poly with a single received word along a line),
      = the prompt's object (line-list / proximity object).
These are NOT the same. We compute both on small fields and check which (if either)
matches  n/2 + 1 - 2*(log2 n - 3).

rho = 1/4 so k = rho*n = n/4. Far line = polynomial of degree >= k that we test
for agreement with code (degree < k).  Over-determined: agreement s > k means the
agreement set forces a low-degree poly through s>k points => structure.

We brute force exact over a prime p with mu_n a 2-power subgroup, char-0 surrogate
via large prime p = 1 mod n (Teichmuller / direct). Exact integer roots count.
"""
import math
from sympy import isprime

def find_prime(n, want_big=False):
    # prime p == 1 mod n so mu_n exists in F_p
    base = 2 if not want_big else n*1000
    k = base
    while True:
        p = k*n + 1
        if isprime(p):
            return p
        k += 1

def subgroup(p, n):
    # find element of order n
    g = 2
    while True:
        # multiplicative order divides p-1
        x = pow(g, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p)!=1 for q in set(prime_factors(n))):
            break
        g += 1
    return [pow(x, i, p) for i in range(n)]

def prime_factors(m):
    fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1
    if m>1: fs.add(m)
    return fs

def max_sparse_zeros(p, mu, s):
    """Max # of zeros on mu of a poly with at most s monomials (sparse-zero radius).
       Brute over which monomials -- too big in general; we instead do the dual:
       a poly with s nonzero coeffs vanishing on a set Z of mu requires the
       s x |Z| evaluation submatrix to be rank-deficient. We search greedily for
       the largest Z that admits an s-sparse vanishing poly with degrees < n."""
    import itertools
    n = len(mu)
    best = 0
    # degrees available: 0..n-1
    # For tractability only do tiny n
    if n > 16: return None
    # try all degree-subsets of size s, check rank of evaluation matrix vs all points
    from sympy import Matrix
    degs = list(range(n))
    # too expensive: instead sample. Skip for n>12 sparse part.
    return None

# Compare the two formulas numerically (the real point).
print("n   k=n/4  promptS*  5n/8  Johnson(n/2)  m*=S*-k(prompt)")
for L in range(3,9):
    n = 2**L
    k = n//4
    sp = n//2 + 1 - 2*(L-3)
    fa = 5*n//8
    joh = n//2
    print(f"{n:<4}{k:<6}{sp:<9}{fa:<6}{joh:<13}{sp-k}")

print()
print("DELTA implied by each:")
for L in range(3,12):
    n=2**L
    sp=n/2+1-2*(L-3)
    fa=5*n/8
    print(f"n={n:<6} prompt delta*=(1 - sp/n)*?  sp/n={sp/n:.4f}  5n/8 frac={fa/n:.4f}  Johnson frac=0.5")
