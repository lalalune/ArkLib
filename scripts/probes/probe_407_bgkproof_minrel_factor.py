#!/usr/bin/env python3
"""
#407 STRATEGY 4 — does Anom_r FACTOR through a minimal char-p relation, with a quantitative
factorization bound that gives Anom_r <= n^{2r}/p ?

SETUP.  A collision is a walk: 2r steps, each +zeta^{a_i} (r of them) and -zeta^{b_j} (r of
them), summing to 0 mod p.  Coordinate form: the multiset of steps gives w in Z^n with
sum_j w_j zeta^j = 0 mod p, and the walk realizes it.  Char-0 (R_r): w=0 in Z[zeta_n].
Char-p-genuine (Anom): w != 0 in ring but = 0 mod p.

CLAIM TO TEST (the "factorization" / connected-cluster bound):
  Every char-p-genuine collision walk decomposes as (a char-0 part) glued to AT LEAST ONE
  minimal char-p-genuine relation of some weight L_min(p) <= 2r.  The number of char-p
  collisions is then  <=  (#ways to embed a min relation) * (char-0 completions).

The cleanest quantitative test of the SUFFICIENT inequality Anom_r <= n^{2r}/p:
  n^{2r}/p = (#all walks)/p = the count if sums were equidistributed mod p.
  Anom_r/(n^{2r}/p) = (Anom_r * p)/n^{2r} = the "excess equidistribution factor".

MEASURE, EXACTLY:
  (A) the FULL distribution of sum over F_p:  c_s = #{r-tuples from mu_n : sum = s},
      sum_s c_s = n^r.  E_r = sum_s c_s^2.  Then Anom_r = E_r - R_r.
  (B) the EXCESS over equidistribution: E_r - n^{2r}/p = sum_s (c_s - n^r/p)^2 - (n^r/p)...
      Actually sum_s c_s^2 - (sum c_s)^2/p = sum_s (c_s - n^r/p)^2 = VARIANCE of the count.
      So  E_r - n^{2r}/p = Var_s(c_s) = "spectral energy off DC".  And the target
        A_r = E_r - n^{2r}/p = Var_s(c_s) <= Wick.
      This re-derives A_r as the VARIANCE of the sum-distribution -- a cleaner object!
  (C) The KEY decomposition:  A_r = Var(c) = (1/p) sum_{b!=0} |chat(b)|^2, chat(b)=eta_b^r-ish.
      Actually c_s = (1/p) sum_b eta_b^r e_p(-b s)? no: c is the r-fold convolution of 1_{mu_n}.
      chat(b) = eta_b^r.  So Var = (1/p) sum_{b!=0} |eta_b|^{2r} = A_r.  CONSISTENT.

  (D) THE DYADIC LEVERAGE TEST.  Split the count by the 2-adic structure.  Does the
      variance Var(c_s) admit a per-level (tower) bound that the generic subgroup lacks?
      Concretely: c = 1_{mu_n}^{*r}, mu_n = mu_{n/2} cup zeta mu_{n/2}.  The negation
      symmetry -1 in mu_{n/2} forces c_s = c_{-s} (c even).  Quantify the structure.

Output: A_r as VARIANCE, the min char-p relation weight, and the anomaly-onset.
"""
import math
import numpy as np
from sympy import primerange
from collections import defaultdict

def setup_mu(n, p):
    for a in range(2, p):
        z = pow(a, (p-1)//n, p)
        if pow(z, n, p) == 1 and pow(z, n//2, p) == p-1:
            return [pow(z, j, p) for j in range(n)], z
    raise RuntimeError

def count_dist(n, r, p):
    """c_s = #{r-tuples from mu_n summing to s mod p}, as int64 array length p."""
    mu, _ = setup_mu(n, p)
    cnt = np.zeros(p, dtype=np.int64)
    cnt[0] = 1
    for _ in range(r):
        nc = np.zeros(p, dtype=np.int64)
        for x in mu:
            nc += np.roll(cnt, x)
        cnt = nc
    return cnt

def min_charp_relation_weight(n, p, maxw=10):
    """
    Smallest L such that some signed +/-1 combination of L distinct n-th roots
    (a MINIMAL antipodal-free vanishing sum, the m=2 spurious object) vanishes mod p.
    We search subsets of {zeta^j} with coefficients +/-1, no antipodal cancellation,
    smallest total weight.  Returns L or None.  (This is the L_min governing the anomaly.)
    """
    mu, z = setup_mu(n, p)
    # signed elements: for each j, +zeta^j.  We want a subset S of {0..n-1} and signs s.t.
    # sum_{j in S} eps_j zeta^j = 0 mod p, minimal |S|, with no antipodal pair (j, j+n/2 both in S with opposite "value").
    # brute by increasing weight; only need existence + weight.
    from itertools import combinations, product
    h = n//2
    for L in range(2, maxw+1):
        for combo in combinations(range(n), L):
            # skip if contains an antipodal pair giving trivial cancellation possibility -- allow all, just check vanish
            vals = [mu[j] for j in combo]
            # try all sign patterns (fix first sign +)
            for signs in product([1, -1], repeat=L-1):
                ss = (1,) + signs
                tot = 0
                for v, sgn in zip(vals, ss):
                    tot = (tot + sgn*v) % p
                if tot == 0:
                    # is it genuine (nonzero in ring)? a +/-1 combo of distinct roots is 0 in ring
                    # only if it's a union of antipodal pairs zeta^j - zeta^j... but distinct j so
                    # ring-zero requires the signed coordinate vector to be 0; check coords.
                    coord = [0]*h
                    for j, sgn in zip(combo, ss):
                        if j < h: coord[j] += sgn
                        else: coord[j-h] -= sgn
                    if any(coord):  # nonzero in ring => genuine char-p relation
                        return L
        # also try with repeated roots? minimal vanishing usually distinct.
    return None

def main():
    print("="*100)
    print("A_r as the VARIANCE of the r-fold sum-distribution c_s; anomaly onset; min char-p rel weight")
    print("="*100)
    for n in [8, 16, 32]:
        p = next(q for q in primerange(int(n**4), int(n**4*3)) if q % n == 1)
        rmax = 6 if n <= 16 else 5
        print(f"\nn={n} PRIZE p={p}:")
        Lmin = min_charp_relation_weight(n, p, maxw=8)
        print(f"   min char-p genuine relation weight L_min = {Lmin}   (anomaly needs >= 2 r-legs to host it)")
        print(f"   {'r':>2} {'Var=A_r':>16} {'Wick':>18} {'A_r/Wick':>9} {'mean=n^r/p':>12} "
              f"{'maxc_s':>8} {'support%':>9}")
        for r in range(1, rmax+1):
            c = count_dist(n, r, p)
            tot = int(c.sum())
            mean = tot / p
            var = float((c.astype(np.float64)**2).sum()) - tot*tot/p   # = A_r exactly
            W = 1.0
            for j in range(1, 2*r, 2): W *= j
            W *= n**r
            supp = float((c > 0).sum())/p*100
            print(f"   {r:>2} {var:>16.1f} {W:>18.1f} {var/W:>9.4f} {mean:>12.3f} {int(c.max()):>8d} {supp:>8.2f}%")
    print("\n" + "="*100)
    print("KEY: A_r = Var(c_s) = sum_s (c_s - n^r/p)^2.  The bound A_r <= Wick is a VARIANCE")
    print("(=spectral L2 off-DC) bound on the r-fold sumset count.  This is the cleanest statement.")
    print("="*100)

if __name__ == "__main__":
    main()
