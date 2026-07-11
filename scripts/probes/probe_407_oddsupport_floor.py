#!/usr/bin/env python3
"""
Does the sparse-zero floor interpolate at ODD / non-power-of-2 supports t?
The power-of-2 law: t=2^s -> n-n/2^s roots, via products of cyclotomic Phi_{2^j}.
But a t-sparse poly need NOT be a pure cyclotomic product. General question:
  F(t) := max #mu_n-roots of a NON-DEGENERATE t-sparse poly (any coeffs, char-0),
          excluding multiples of X^n-1 (the full-group trap).
For n=2^mu, the mu_n-roots of any poly p = the set of 2^mu-th roots of unity that are
roots of p = union of some cyclotomic-coset classes ONLY IF p is a product of Phi's...
BUT a general sparse p can vanish on an ARBITRARY subset S of mu_n (not a union of
cyclotomic classes) -- it just needs prod_{x in S}(X-x) | p. The min support of a poly
vanishing on a given S of size s is what governs F(t): F(t) = max{ |S| : minsupp(S) <= t }.
minsupp(S) = min # nonzero coeffs of a poly in <X^n-1> ideal-coset vanishing on S... 
Actually over mu_n, a function S->{0} extends to many polys; the MIN support of the
unique degree<n interpolation is the "uncertainty" min-support. We brute-force EXACTLY:
for small n, enumerate subsets S of mu_n by size, compute min support of the degree<n
interpolating poly that is 0 on S (and not identically 0 on mu_n), find max |S| with
min-support <= t.
"""
import numpy as np
from itertools import combinations


def min_support_vanishing_on(n, S):
    """Min # nonzero coeffs (deg<n) of a nonzero poly on mu_n vanishing exactly-at-least on S.
    The polys of deg<n vanishing on S form a linear space; on mu_n a deg<n poly is determined
    by its values, and 'vanishing on S' = values 0 on S, free on mu_n\\S. We want the min
    L0 (support) over the X-coeff vector. Coeff vector c (len n) <-> values v = DFT(c) on mu_n.
    v_j = sum_k c_k omega^{jk}, omega=e^{2pi i/n}. Constraint v_j=0 for j in S. We minimize
    ||c||_0 over c with (F c)_S = 0, c != 0. This is an L0-min over a subspace -> brute force
    via: the support of c is some set T; feasible iff exists nonzero c supported on T with
    F[S,T] c_T = 0 i.e. F[S,T] rank-deficient (nullspace nonzero). min |T| = min size with
    rank(F[S,T]) < |T|. We scan T by increasing size."""
    F = np.array([[np.exp(2j*np.pi*j*k/n) for k in range(n)] for j in range(n)])
    Srows = F[list(S), :]
    for tt in range(1, n+1):
        for T in combinations(range(n), tt):
            M = Srows[:, list(T)]
            # nullspace nonzero iff rank < |T|
            if np.linalg.matrix_rank(M, tol=1e-9) < len(T):
                return tt
    return n


def F_of_t(n, tmax):
    """For each support t, max |S| (S subset mu_n, exclude S=all=degenerate) with minsupp(S)<=t."""
    best = {t: 0 for t in range(1, tmax+1)}
    # iterate subsets S by size descending is expensive; do all S up to n-1
    idx = list(range(n))
    for s in range(1, n):  # |S| from 1..n-1 (exclude full group)
        # to bound cost only test a sample? For small n do all
        for S in combinations(idx, s):
            ms = min_support_vanishing_on(n, S)
            for t in range(ms, tmax+1):
                if s > best[t]:
                    best[t] = s
    return best


for mu in [3]:
    n = 2**mu
    print("=== n=%d ===" % n)
    best = F_of_t(n, n)
    for t in range(2, n+1):
        pred2 = (n - n // (2**int(np.log2(t)))) if (t & (t-1) == 0) else None
        tag = ""
        if t & (t-1) == 0:  # power of 2
            s = int(np.log2(t))
            tag = "  [2^%d law: n-n/2^%d=%d]" % (s, s, n - n//(2**s))
        print("  t=%2d: F(t)=max roots=%2d%s" % (t, best[t], tag))
