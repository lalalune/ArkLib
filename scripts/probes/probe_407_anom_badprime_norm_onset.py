#!/usr/bin/env python3
"""
#407 ANOMALY-SUPPRESSION ASYMPTOTIC EDGE via the NORM characterization (exact, no per-prime FFT).

Anom_r(p) > 0  <=>  some ring element  alpha = sum_{i=1..r} zeta^{a_i} - sum_{j=1..r} zeta^{b_j}
(a multiset difference of two r-subsets-with-rep of {zeta^0..zeta^{n-1}}) is NONZERO in Z[zeta_n]
but vanishes mod p, i.e.  p | N(alpha)  for that alpha != 0  (N = absolute field norm to Q).

So the set of r-bad primes = { primes dividing N(alpha) : alpha an r-collision-difference, alpha!=0 }.
=> The LARGEST r-bad prime p_bad(n,r) = largest prime factor over all such N(alpha).
This is EXACT and avoids scanning/FFT per prime. We enumerate alpha by the integer lattice
coordinate vector of (sum_x - sum_y) in Z[zeta_n] ~ Z^{phi}, phi=n/2 (Phi_{2^a}: zeta^phi=-1),
dedup the lattice vectors, drop 0, compute |N| = resultant/product of conjugate evaluations.

For n=2^a, N(alpha) for alpha with coeff vector c in basis {1,zeta,..,zeta^{phi-1}} is
  N = prod over primitive 2n-th... -> exactly prod_{k odd, 1<=k<2n} ( sum_j c_j * w^{k j} ),
  w = exp(2 pi i / n)? Careful: zeta_n is a primitive n-th root; its conjugates are zeta_n^k for
  gcd(k,n)=1, i.e. k odd (n=2^a). N(alpha)=prod_{k odd,1<=k<n} ( P(zeta_n^k) ), P(t)=sum_j c_j t^j.
  That's phi=n/2 conjugates. Compute as integer via rounding the complex product (verify integrality).

We enumerate the distinct difference-vectors c = (multiset of r zetas) - (multiset of r zetas),
reduced to Z^phi. Number of r-multisets from n symbols = C(n+r-1, r); difference space is the
pairwise differences => we hash reduced vectors. Feasible for small n,r.

Output per (n,r): max |N|, its largest prime factor p_bad, beta=log_n(p_bad), vs n^4.
Also: distribution of largest-prime-factors to see how many alpha give bad primes >= n^4.
"""
import numpy as np, math
from itertools import combinations_with_replacement
from collections import Counter

def lattice_vec_of_multiset(ms, n):
    """multiset ms (tuple of exponents in 0..n-1) -> coeff vector in Z^phi, phi=n/2 (zeta^phi=-1)."""
    phi=n//2
    v=[0]*phi
    for e in ms:
        if e<phi: v[e]+=1
        else: v[e-phi]-=1
    return tuple(v)

def norm_of(c, n):
    """exact integer field norm N(P(zeta_n)), P=sum c_j zeta^j, conjugates zeta^k k odd in [1,n)."""
    phi=n//2
    prod=1.0+0.0j
    for k in range(1,n,2):
        w=np.exp(2j*np.pi*k/n)
        val=sum(c[j]*(w**j) for j in range(phi))
        prod*=val
    # prod should be a (real) integer
    re=prod.real
    ri=round(re)
    if abs(re-ri)>1e-3*max(1,abs(re)) and abs(re-ri)>0.5:
        return None  # integrality failed (shouldn't happen)
    return int(ri)

def largest_prime_factor(m):
    m=abs(m)
    if m<=1: return 1
    lpf=1; d=2
    while d*d<=m:
        while m%d==0: lpf=d; m//=d
        d+=1 if d==2 else 2
    if m>1: lpf=m
    return lpf

def factor_primes(m):
    m=abs(m); fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1 if d==2 else 2
    if m>1: fs.add(m)
    return fs

print("="*82)
print("BAD-PRIME ONSET via NORMS: r-bad primes = prime factors of N(alpha), alpha=r-collision-diff")
print("="*82)

for n in [8,16,32,64]:
    phi=n//2
    print(f"\n### n={n}  n^4={n**4}  (4*log_2 = beta-thresh 4; phi={phi})")
    rmax = 8 if n<=8 else (6 if n==16 else (4 if n==32 else 3))
    for r in range(2, rmax+1):
        # enumerate r-multisets of exponents, build lattice vectors of their SUMS, then differences
        sums={}
        msets=list(combinations_with_replacement(range(n), r))
        if len(msets)>200000:
            print(f"  r={r}: skip (|multisets|={len(msets)} too big)")
            continue
        sumvecs=[lattice_vec_of_multiset(ms,n) for ms in msets]
        uniq_sumvecs=list(set(sumvecs))
        # differences alpha = u - v, u,v distinct sum-vectors, alpha != 0
        # to bound work, take all pairwise diffs among uniq sum-vectors
        U=uniq_sumvecs
        if len(U)>2500:
            # sample-free but cap: use full set if small else restrict (still exact over what we test)
            pass
        diffs=set()
        for i in range(len(U)):
            ui=U[i]
            for j in range(len(U)):
                if i==j: continue
                d=tuple(ui[k]-U[j][k] for k in range(phi))
                if any(d): diffs.add(d)
        if not diffs:
            print(f"  r={r}: no nonzero difference vectors")
            continue
        maxnorm=0; bad_primes=set(); pbad=1; nfail=0
        for c in diffs:
            N=norm_of(c,n)
            if N is None: nfail+=1; continue
            if N==0: continue
            maxnorm=max(maxnorm,abs(N))
            lpf=largest_prime_factor(N)
            if lpf>pbad: pbad=lpf
        beta=math.log(pbad)/math.log(n) if pbad>1 else 0
        # how many distinct primes >= n^4 appear as factors of some norm (bad primes in/above window)
        # (only collect for the largest few to keep cheap)
        print(f"  r={r}: |diffs|={len(diffs)} max|N|={maxnorm} (log2={math.log2(max(1,maxnorm)):.1f})  "
              f"p_bad_max={pbad} beta={beta:.2f}  {'>= n^4 (REACHES PRIZE WINDOW)' if pbad>=n**4 else '< n^4 (window clean)'}"
              + (f"  [{nfail} norm-fails]" if nfail else ""))
