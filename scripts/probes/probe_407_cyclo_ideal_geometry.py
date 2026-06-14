#!/usr/bin/env python3
"""
#407 OPEN CORE -- CYCLOTOMIC IDEAL GEOMETRY attack on the char-p excess.

GOAL.  Prize bound  B(n,p)=max_{b!=0}|sum_{x in mu_n} e_p(bx)| <= n^{1/2+o(1)}  for n=2^mu.
Equivalent (proven): char-p excess  Excess(r) = E_r - n^{2r}/p <= (2r-1)!! n^r  at r ~ ln p.

THE OBJECT.  A collision  sum_{i<=r} x_i == sum_{j<=r} y_j  (mod p), x_i,y_j in mu_n,
is exactly a cyclotomic integer
    alpha = sum_i zeta^{a_i} - sum_j zeta^{b_j}  in Z[zeta_n],   (zeta = primitive n-th root)
with <= 2r terms each +-1, lying in the degree-1 prime ideal  P | p  (residue degree 1,
since n | p-1 forces COMPLETE SPLITTING).  i.e. alpha == 0 mod P, P of norm p, Z[zeta_n]/P = F_p.

So  Excess(r) = #{ short alpha in P } counted with the convolution multiplicity. We attack the
COUNT of such short alpha by the GEOMETRY of the ideal lattice P inside Z[zeta_n].

GEOMETRY-OF-NUMBERS HEURISTIC.
  Z[zeta_n] has rank d = phi(n) = n/2; in the power basis {1,zeta,...,zeta^{d-1}} a "short"
  alpha is an integer vector c in Z^d with L1 norm |c|_1 <= 2r.  The number of such vectors is
      Box(d, 2r) = #{c in Z^d : sum|c_j| <= 2r}  ~  (2*2r)^d / d!   (for 2r << d).
  The ideal P has index [Z[zeta_n]:P] = N(P) = p.  If P were a "random" index-p sublattice,
  a short vector lands in P with probability ~ 1/p, giving the RANDOM RATE  Box(d,2r)/p, which
  is exactly the n^{2r}/p term already subtracted.  The EXCESS is the DEVIATION from random:
  short vectors are NOT uniform mod P -- the count near 0 is governed by the SHORTEST VECTORS of
  P (lambda_1(P)) and the local point density.

  KEY DICHOTOMY (the thing to measure):
    * If lambda_1(P) is LARGE (P has no short vectors), then 0 is the ONLY short alpha in P up to
      the trivial antipodal relations, and Excess is SMALL.
    * If P has a short vector v (|v|_1 = O(1)), it generates an arithmetic progression
      {0, +-v, +-2v, ...} of short ideal points, and Excess INFLATES.
  The char-0 (Wick) value (2r-1)!! n^r is precisely the count of FORMAL antipodal relations
  (alpha = 0 in Z[zeta_n], i.e. c = 0 in the power basis): these are the lattice point 0 counted
  with convolution multiplicity. The question: does the 2-power ideal geometry keep the NONZERO
  short ideal points (the genuine excess) below the Wick budget at r ~ ln p?

WHAT THIS PROBE MEASURES (exactly, no hand-waving):
  For the prize 2-power n and primes p == 1 mod n:
  (A) lambda_1(P): the shortest nonzero cyclotomic integer (in L1-power-basis AND in the
      canonical/Minkowski L2 embedding) lying in P. This is the geometric gate.
  (B) The EXACT count  G(r) := #{ c in Z^d : |c|_1 <= 2r, sum c_j zeta^j == 0 mod P, c != 0 }
      of NONZERO short ideal vectors (the genuine relations) for r = 2,3,... and compare to Wick.
  (C) Whether the genuine short ideal points form a 1-D progression (rank-1 structure from a
      single short v) -- which would let us COUNT them as ~ (2r/|v|_1) and bound the excess.

This is a measurement to decide whether geometry-of-numbers gives Excess below Wick. Honest:
no closure is claimed; we report the exact gap.
"""
import numpy as np
import cmath, math, itertools
from math import gcd


def is_prime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = x - 1; s = 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        if a % x == 0: continue
        v = pow(a, d, x)
        if v in (1, x-1): continue
        for _ in range(s-1):
            v = v*v % x
            if v == x-1: break
        else: return False
    return True


def prime_factors(m):
    f = set(); d = 2
    while d*d <= m:
        while m % d == 0: f.add(d); m //= d
        d += 1
    if m > 1: f.add(m)
    return f


def order_n_root(p, n):
    """primitive n-th root zeta in F_p (p == 1 mod n)."""
    pf = prime_factors(n)
    for g in range(2, p):
        z = pow(g, (p-1)//n, p)
        if all(pow(z, n//q, p) != 1 for q in pf):
            return z
    raise RuntimeError("no root")


def short_ideal_count(p, n, r):
    """
    EXACT count of NONZERO cyclotomic integers  alpha = sum_{j<d} c_j zeta^j,  d = phi(n)=n/2,
    with sum|c_j| <= 2r and alpha == 0 mod P (the degree-1 prime above p), c != 0, modulo the
    trivial sign/rotation. We reduce alpha mod P by evaluating zeta -> the F_p root g and testing
    == 0 mod p in the power basis (deg < d, using zeta^{d}=...=−1 relations implicitly because
    g is a genuine n-th root in F_p so g^j for j<d are the literal residues).

    Returns (count_nonzero, lambda1_L1, lambda1_L2, sample_vectors).
    We also return the L2 (canonical-embedding) length of the shortest nonzero ideal point found.
    """
    d = n // 2
    g = order_n_root(p, n)
    gpow = [pow(g, j, p) for j in range(d)]          # zeta^j -> g^j in F_p, j < d (independent)
    # canonical embedding lengths: sigma_a(zeta)=exp(2pi i a/n), a coprime to n
    units = [a for a in range(1, n) if gcd(a, n) == 1]
    zc = [cmath.exp(2j*math.pi*a/n) for a in units]   # embeddings of zeta

    count = 0
    lam1_L1 = None
    lam1_L2 = None
    best_vecs = []
    # enumerate c in Z^d with sum|c_j| <= 2r.  This is the L1 ball; size ~ (4r)^d/d! -- feasible
    # only for small d (n<=16 -> d<=8). For larger we enumerate by support to keep it tractable.
    # We iterate over the number of nonzero coords s and their signs/positions.
    K = 2*r
    # To keep enumeration honest+complete for small n: iterate compositions of |c|_1.
    # Use recursion over coordinates with running budget.
    def rec(idx, budget, vec, val_modp, l1):
        nonlocal count, lam1_L1, lam1_L2
        if idx == d:
            if l1 == 0:
                return
            if val_modp % p == 0:
                count += 1
                # canonical L2 length
                emb = [sum(vec[j]*(zc[k]**j) for j in range(d)) for k in range(len(units))]
                l2 = math.sqrt(sum(abs(e)**2 for e in emb))
                if lam1_L1 is None or l1 < lam1_L1:
                    lam1_L1 = l1
                if lam1_L2 is None or l2 < lam1_L2:
                    lam1_L2 = l2
                if len(best_vecs) < 20:
                    best_vecs.append((tuple(vec), l1, round(l2, 3)))
            return
        # remaining coords idx..d-1 can use up to `budget`
        for c in range(-budget, budget+1):
            rec(idx+1, budget-abs(c), vec+[c], (val_modp + c*gpow[idx]) % p, l1+abs(c))
    # this naive recursion is exponential; cap d
    if d <= 8 and (2*K+1)**d < 5e8:
        rec(0, K, [], 0, 0)
        return count, lam1_L1, lam1_L2, best_vecs
    return None, None, None, None   # too big for exact enumeration here


def wick(r, n):
    x = 1; m = 2*r-1
    while m > 0: x *= m; m -= 2
    return x * n**r


def box_count(d, K):
    """#{c in Z^d : sum|c_j| <= K} = sum_{j=0}^{min(d,K)} C(d,j) C(K,j) 2^j (Delannoy-like)."""
    from math import comb
    tot = 0
    for j in range(0, min(d, K)+1):
        tot += comb(d, j) * comb(K, j) * (2**j)
    return tot


if __name__ == "__main__":
    print("#407 CYCLOTOMIC IDEAL GEOMETRY: short nonzero ideal points vs Wick budget\n")
    print("d=phi(n)=n/2.  Random-rate predicts #short alpha in P ~ Box(d,2r)/p.")
    print("Excess = #NONZERO short alpha in P (genuine).  Compare to Wick (2r-1)!! n^r.\n")
    for n in [8, 16]:
        d = n//2
        print(f"=== n={n} (d=phi={d}) ===")
        # primes p == 1 mod n, ladder from small (split, char-p) up
        ps = []
        p = n+1
        while len(ps) < 6:
            if is_prime(p): ps.append(p)
            p += n
        for p in ps:
            print(f"  p={p:6d}:", end=" ")
            for r in ([2,3] if n==8 else [2,3]):
                cnt, l1, l2, vecs = short_ideal_count(p, n, r)
                if cnt is None:
                    print(f"r={r}:(skip)", end="  ")
                    continue
                box = box_count(d, 2*r)
                rr = box / p   # random-rate predicted count of ALL (incl 0) short ideal pts
                print(f"r={r}: #nz_short={cnt} (lam1_L1={l1} lam1_L2={l2}) box/p~{rr:.1f} Wick={wick(r,n)}",
                      end="  ")
            print()
        print()
