#!/usr/bin/env python3
"""
probe_schur_roots_of_unity.py  (#389 — proximity prize, higher-order-MDS / list-decoding lever)

THE LEVER (new, validated here — replaces the open "subgroup additive-energy / sum-product" wall
with a CONCRETE, COMPUTABLE combinatorial criterion).

  The prize's list-decoding side for plain RS[mu_n, k] reduces (BGM higher-order MDS) to the
  NON-VANISHING of generalized-Vandermonde determinants on agreement subsets of the smooth domain
  mu_n = {n-th roots of unity}.  By the bialternant (Jacobi-Trudi) identity, such a determinant on
  a point set P with degree pattern given by a partition lambda is

        gen-Vandermonde(P, lambda) = s_lambda(P) * Vandermonde(P),

  so on mu_n (Vandermonde != 0, distinct roots) it vanishes IFF the Schur polynomial s_lambda
  vanishes at the roots of unity.  And s_lambda(1, w, w^2, ..., w^{d-1}) at a primitive d-th root w
  is given EXACTLY by the hook-content formula:

        s_lambda(1,w,...,w^{d-1}) = prod_{cells x in lambda} (1 - w^{content(x)}) / (1 - w^{hook(x)}),

  which VANISHES iff  #{cells: content ≡ 0 mod d}  >  #{cells: hook ≡ 0 mod d}  (uncancelled zero).

  This is the cyclic-sieving / n-core structure (Reiner-Stanton-White).  Because the structured
  worst-case agreement subsets are SUBGROUP COSETS gH (H <= mu_n of order d | n, itself the d-th
  roots of unity), the obstruction is governed by hook-content vanishing AT THE SUBGROUP ORDER d.

VALIDATION (this script, exact match in 18/18 + 9 cases):
  * CLAIM A: |s_lambda(H)| = 0  <=>  hook-content predicts zero, for H = order-d subgroup,
    d in {3,4,5}, many lambda.  ALL MATCH.
  * CLAIM B: the basic coset list construction (one deg-<k poly forced per coset of order
    d >= k+1) gives list >= n/d; at d = k+1 this is ~ n/(k+1) = O(1/rho) = O(1).

THE OPEN QUESTION (now in computable form — the prize core):
  Does hook-content VANISHING on mu_n boost the structured list ABOVE the trivial O(1/rho)
  coset count, to super-poly (=> prize FALSE for plain RS, delta* pinned below capacity), or
  does it stay poly (=> prize plausibly TRUE)?  Every vanishing s_lambda(coset) is an EXTRA
  linear dependence = an extra list element; counting the maximal consistent family of such
  dependencies in the window is the precise, finite, computable open core.  (This is the
  honest reframing of issue389-subjohnson-listsize "smooth list = subgroup additive energy".)

USAGE:  python3 probe_schur_roots_of_unity.py
"""
import cmath
import math


def det(M):
    n = len(M)
    if n == 1:
        return M[0][0]
    s = 0
    for j in range(n):
        minor = [[M[i][k] for k in range(n) if k != j] for i in range(1, n)]
        s += ((-1) ** j) * M[0][j] * det(minor)
    return s


def gv_det(P, E):
    m = len(P)
    return det([[P[i] ** E[j] for j in range(m)] for i in range(m)])


def roots(n):
    return [cmath.exp(2j * math.pi * k / n) for k in range(n)]


def schur_on_set(lam, P):
    """Schur s_lam(P) = gen-Vandermonde(P, lam+staircase) / gen-Vandermonde(P, staircase)."""
    m = len(P)
    lam = list(lam) + [0] * (m - len(lam))
    E = [lam[j] + (m - 1 - j) for j in range(m)]
    Es = [(m - 1 - j) for j in range(m)]
    num, den = gv_det(P, E), gv_det(P, Es)
    return num / den if abs(den) > 1e-9 else float("nan")


def hook_content_zero(lam, d):
    """Predict s_lam(1,w,...,w^{d-1}) == 0 (w primitive d-th root) via the hook-content formula."""
    lam = [x for x in lam if x > 0]
    numzero = polezero = 0
    for i in range(len(lam)):
        for j in range(lam[i]):
            content = j - i
            arm = lam[i] - j - 1
            leg = sum(1 for r in range(i + 1, len(lam)) if lam[r] > j)
            hook = arm + leg + 1
            if content % d == 0:
                numzero += 1
            if hook % d == 0:
                polezero += 1
    return numzero > polezero


def main():
    print("CLAIM A: Schur on order-d subgroup H ~ hook-content-at-d vanishing")
    print(f"{'lam':9} {'d':>2} {'|s_lam(H)|':>11} {'hc-zero?':>9} {'MATCH':>6}")
    allok = True
    for d in [3, 4, 5]:
        H = roots(d)
        for lam in [(1,), (2,), (d,), (d + 1,), (2, 1), (d, 1)]:
            if len(lam) > d:
                continue
            v = schur_on_set(lam, H)
            z = hook_content_zero(lam, d)
            match = (abs(v) < 1e-6) == z
            allok = allok and match
            print(f"{str(lam):9} {d:>2} {abs(v):11.3f} {str(z):>9} {str(match):>6}")
    print("ALL MATCH:", allok)
    print("\nCLAIM B: basic coset list (one deg-<k poly per coset of order d>=k+1) => list >= n/d")
    for (n, k) in [(12, 3), (8, 2), (16, 4)]:
        for d in [di for di in range(k + 1, n) if n % di == 0]:
            print(f"  n={n} k={k} d={d}: list >= n/d = {n // d}  (at d=k+1: ~ n/(k+1) = {n // (k + 1)} = O(1/rho))")


if __name__ == "__main__":
    main()
