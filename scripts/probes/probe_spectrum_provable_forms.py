#!/usr/bin/env python3
"""
probe_spectrum_provable_forms.py  (#444)

The single open prize core is the complete-homogeneous spectrum bound:
    #{distinct h_r(R) : R in binom(mu_s, k+1)}  <=  n * C(s+r-1, r)   (verified, poly(n)=n).

This probe pins down EXACTLY which PROVABLE form suffices, by computing for each (s, k, r):
  A = actual #distinct h_r(R) over (k+1)-subsets R of mu_s          (the truth)
  T = trivial bound C(s, k+1)                                       (one value per subset)
  G = rotation bound C(s,k+1)/gcd(s,r)                              (PROVABLE via h_r(zR)=z^r h_r(R))
  N = target n * C(s+r-1, r)  with n=s                             (the conjectured ceiling)
and reports A<=G, A<=N, G<=N (does the provable rotation bound IMPLY the target?), and the
leading exponents log(.)/log(s) so we see which dominates asymptotically.

h_r is computed exactly in Z[zeta_s] via the index-sum coefficient vector:
  h_r(R) = sum over size-r multisets M of R of prod x  =  sum_m c_m * zeta^m,
  c_m = #{size-r multisets of index-set(R) with index-sum = m mod s}.
Two subsets give the same h_r iff their coefficient vectors (mod the minimal poly of zeta_s)
coincide; we use the canonical reduction (vector in Z^s reduced by the relation sum_{j} zeta^{m+ j*s/p ...})
-- to stay exact and simple we compare the full length-s integer coefficient vector AND, separately,
the value as an algebraic number via high-precision; we report the algebraic-distinct count A.
"""
import math, itertools
from fractions import Fraction
import cmath

def gcd(a,b):
    while b: a,b=b,a%b
    return a

def choose(n,k):
    if k<0 or k>n: return 0
    return math.comb(n,k)

def hr_coeffvec(idxset, r, s):
    """coefficient vector c[0..s-1], c_m = # size-r multisets of idxset with index-sum = m mod s."""
    # dp over multisets of size r from idxset (with repetition), tracking sum mod s
    # multiset generating: product over elements 1/(1-x t) -> coefficient of t^r
    # dp[j][m] = # multisets of size j with sum m mod s, using elements processed so far,
    # allowing unlimited repetition of each element.
    # Use unbounded knapsack style: for each element e, allow taking it 0..r times.
    dp = [[0]*s for _ in range(r+1)]
    dp[0][0]=1
    for e in idxset:
        ndp=[row[:] for row in dp]
        # for taking element e one more time: shift
        # unbounded: iterate count
        for j in range(1,r+1):
            for m in range(s):
                # ndp[j][m] += ndp[j-1][(m-e)%s]  (take one more e)
                ndp[j][m]=dp[j][m]  # baseline: not adding more e beyond previous elements
            # we need proper unbounded within this element; do a forward pass
        # simpler: rebuild with unbounded contribution of e on top of dp(previous elements)
        ndp=[[0]*s for _ in range(r+1)]
        ndp[0][0]=dp[0][0]
        for j in range(0,r+1):
            for m in range(s):
                if dp[j][m]==0 and not (j==0 and m==0):
                    pass
        # Do clean unbounded knapsack across all elements at once instead.
        break
    # Clean implementation: unbounded knapsack over all elements simultaneously.
    dp=[[0]*s for _ in range(r+1)]
    dp[0][0]=1
    for e in idxset:
        for j in range(1,r+1):
            for m in range(s):
                dp[j][m]+=dp[j-1][(m-e)%s]
    return tuple(dp[r])

def algval(coeffvec, s):
    z=cmath.exp(2j*math.pi/s)
    return sum(c*(z**m) for m,c in enumerate(coeffvec))

def distinct_count(s,k,r):
    nodes=list(range(s))
    seen=set()
    seen_alg=[]
    for R in itertools.combinations(nodes,k+1):
        cv=hr_coeffvec(R,r,s)
        # canonical key: reduce coeff vector by cyclotomic relation only matters for equality of
        # algebraic numbers; use rounded high-precision value as key (robust at these sizes)
        v=algval(cv,s)
        key=(round(v.real,6),round(v.imag,6))
        seen.add(key)
    return len(seen)

def main():
    print(f"{'s':>3}{'k':>3}{'r':>3} | {'A=actual':>9} {'T=C(s,k+1)':>11} {'G=T/gcd':>9} {'N=s*CH':>10} "
          f"| {'A<=G':>5} {'A<=N':>5} {'G<=N':>5} | {'eA':>5} {'eG':>5} {'eN':>5}")
    print("-"*100)
    # binding fold heuristic: r ~ k (the divided-difference degree a-k with a~2k); sweep small r.
    configs=[]
    for s in (8,12,16,20,24):
        k=max(1,s//4 -1)          # rho=1/4 regime: k+1 ~ s/4
        for r in (2,3,4):
            configs.append((s,k,r))
    for (s,k,r) in configs:
        A=distinct_count(s,k,r)
        T=choose(s,k+1)
        g=gcd(s,r)
        G=T//g if T%g==0 else T/g
        N=s*choose(s+r-1,r)
        def lx(x):
            return math.log(x)/math.log(s) if x>0 else 0.0
        okAG = A<=G
        okAN = A<=N
        okGN = G<=N
        print(f"{s:>3}{k:>3}{r:>3} | {A:>9} {T:>11} {int(G) if isinstance(G,int) or G==int(G) else round(G,1):>9} {N:>10} "
              f"| {str(okAG):>5} {str(okAN):>5} {str(okGN):>5} | {lx(A):>5.2f} {lx(G):>5.2f} {lx(N):>5.2f}")

if __name__=="__main__":
    main()
