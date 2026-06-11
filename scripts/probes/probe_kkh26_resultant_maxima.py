#!/usr/bin/env python3
"""A3 feasibility probe: how big are the KKH26 collision resultants REALLY? (issue #334)

[KKH26] Lemma 1 needs p to divide no collision resultant Res(P-Q, Phi_s); the
in-tree threshold uses the worst-case bound |Res| <= (2r)^{s/2} <= s^{s/2},
which makes the epsilon* = 2^-128 reach-table rows EMPTY for s >= 64
(probe_kkh_ceiling_numeric_reach.py).  Hypothesis A3 asks whether the TRUE
maximum over the needed pairs is far smaller, so that a certified maximum
could open s = 64 unconditionally (no Thorner-Zaman external).

This probe measures the exact norm landscape at small s and extrapolates:

  N(R) = |prod_{zeta primitive s-th root} R(zeta)| = |Res(R, Phi_s)|
       = |N_{Q(zeta_s)/Q}(R(zeta_s))|,

computed EXACTLY in the ring Z[x]/Phi_s(x) (power basis, deg = s/2 for s a
power of two; Phi_s = x^{s/2} + 1) via the resultant = product of conjugates,
i.e. det of multiplication... we use the simplest exact route: resultant via
integer polynomial arithmetic (Sylvester determinant is overkill; for
Phi_s = x^m + 1 with m = s/2, N(R) = |Res(R, x^m+1)| = |prod R(zeta)| can be
computed exactly as the constant coefficient (up to sign) of the
characteristic polynomial of multiplication-by-R on Z[x]/(x^m+1) -- but the
cheapest exact method is: N(R) = |det of the (negacyclic) matrix of R|.
For R = sum c_i x^i, multiplication by R on Z[x]/(x^m+1) is the negacyclic
matrix M with M[j][i+j mod m] = +/- c_i (sign flips on wraparound).  N(R) =
|det M|, exact over Z via fraction-free Bareiss.

Families measured:
1. s = 16 (m = 8): EXACT max over the FULL difference superset
   D8 = {R != 0 : coeffs in {-2..2}^8}  (5^8 - 1 = 390624 polynomials)
   -- every collision difference P-Q lies in D8, so max over D8 upper-bounds
   the true pair maximum for EVERY r.  Compare against s^{s/2} = 16^8 ~ 4.3e9.
2. s = 32 (m = 16): the diagonal +/-1 family (R = P-Q with disjoint supports,
   coeffs in {-1,0,1}, exactly 2r nonzero) sampled (200k) + structured
   extremal candidates (all-ones, alternating, clustered) + a hill-climb from
   the best sample; reported as an HONEST LOWER BOUND on the s = 32 max,
   plus the {-2..2} random-sample max for the superset.
3. Growth fit: log2(max) vs s across s = 8, 16, (32 lower bound); compare
   against the worst-case slope log2(s^{s/2}) = (s/2) log2 s and against the
   Mahler-measure heuristic (max ~ M^{s/2} for a constant M < 4: if the
   observed per-conjugate geometric mean is mu, then certifying s = 64 needs
   mu^{32} < 2^{128+epsilon_budget} i.e. mu < ~2^4.7 -- printed verdict).

Verdict semantics for A3:
  - if the s = 16 exact max is ALREADY ~ s^{s/2}: A3 is DEAD (worst case tight).
  - if max << s^{s/2} but mu (per-conjugate mean) > the 2^4.7 budget: A3 dies
    at s = 64 anyway -- certified-but-too-big.
  - if mu < budget: A3 stays alive; next rung is a certified branch-and-bound
    at s = 64 over the +/-1 difference family.
Exit 0 iff internal cross-checks pass (the verdict itself is informational).
"""

import random
from fractions import Fraction

random.seed(334)


def negacyclic_det(coeffs, m):
    """|det| of multiplication-by-R on Z[x]/(x^m + 1), R = sum coeffs[i] x^i.
    Exact integer Bareiss elimination."""
    M = [[0] * m for _ in range(m)]
    for j in range(m):
        for i, c in enumerate(coeffs):
            if c == 0:
                continue
            k = i + j
            if k < m:
                M[j][k] += c
            else:
                M[j][k - m] -= c
    # Bareiss fraction-free determinant
    n = m
    prev = 1
    mat = [row[:] for row in M]
    sign = 1
    for k in range(n - 1):
        if mat[k][k] == 0:
            piv = next((r for r in range(k + 1, n) if mat[r][k] != 0), None)
            if piv is None:
                return 0
            mat[k], mat[piv] = mat[piv], mat[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                mat[i][j] = (mat[i][j] * mat[k][k] - mat[i][k] * mat[k][j]) // prev
            mat[i][k] = 0
        prev = mat[k][k]
    return abs(sign * mat[n - 1][n - 1])


def norm_check_via_complex(coeffs, m):
    """Float cross-check: prod |R(zeta)| over primitive 2m-th roots."""
    import cmath
    prod = 1.0
    for t in range(2 * m):
        if t % 2 == 1:  # primitive (2m)-th roots of unity: odd powers of zeta_{2m}
            z = cmath.exp(1j * cmath.pi * t / m)
            prod *= abs(sum(c * z ** i for i, c in enumerate(coeffs)))
    return prod


def itertools_product_max_m8():
    """Exact max over D8 = coeffs in {-2..2}^8, R != 0 (390k dets of 8x8)."""
    from itertools import product
    best, best_R = 0, None
    cnt = 0
    for coeffs in product(range(-2, 3), repeat=8):
        if all(c == 0 for c in coeffs):
            continue
        d = negacyclic_det(list(coeffs), 8)
        cnt += 1
        if d > best:
            best, best_R = d, coeffs
    return best, best_R, cnt


def sample_pm1_disjoint(m, r, trials):
    """Sample differences P-Q: +/-1 coefficients, 2r nonzero (disjoint supports)."""
    best, best_R = 0, None
    idxs = list(range(m))
    for _ in range(trials):
        support = random.sample(idxs, 2 * r)
        coeffs = [0] * m
        for t, i in enumerate(support):
            coeffs[i] = 1 if t < r else -1
        random.shuffle(support)
        d = negacyclic_det(coeffs, m)
        if d > best:
            best, best_R = d, tuple(coeffs)
    return best, best_R


def hill_climb(m, start, iters=4000):
    cur = list(start)
    best = negacyclic_det(cur, m)
    best_R = tuple(cur)
    for _ in range(iters):
        cand = best_R and list(best_R)
        i = random.randrange(m)
        cand[i] = random.choice([-2, -1, 0, 1, 2])
        d = negacyclic_det(cand, m)
        if d >= best:
            best, best_R = d, tuple(cand)
    return best, best_R


if __name__ == "__main__":
    import math

    # cross-check the exact determinant against the float norm on 50 random R
    for m in (4, 8):
        for _ in range(25):
            coeffs = [random.randint(-2, 2) for _ in range(m)]
            if all(c == 0 for c in coeffs):
                coeffs[0] = 1
            exact = negacyclic_det(coeffs, m)
            approx = norm_check_via_complex(coeffs, m)
            assert abs(exact - approx) <= max(1.0, 1e-6 * approx), \
                f"det/norm mismatch at m={m}: {exact} vs {approx}"
    print("cross-check: negacyclic det == complex norm product (50 random R) [OK]")

    # s = 8 exact (tiny): full {-2..2}^4
    from itertools import product as iproduct
    best8 = max((negacyclic_det(list(c), 4), c) for c in iproduct(range(-2, 3), repeat=4)
                if any(c))
    wc8 = 8 ** 4
    print(f"\ns=8  (m=4):  exact max over {{-2..2}}^4 = {best8[0]}  at R={best8[1]}")
    print(f"             worst-case bound s^(s/2) = {wc8}   ratio = {best8[0]/wc8:.4f}")

    # s = 16 exact superset max
    best16, R16, cnt = itertools_product_max_m8()
    wc16 = 16 ** 8
    mu16 = best16 ** (1 / 8)
    print(f"\ns=16 (m=8):  exact max over {{-2..2}}^8 ({cnt} polys) = {best16}")
    print(f"             at R = {R16}")
    print(f"             worst-case s^(s/2) = {wc16}  ratio = {best16/wc16:.6f}")
    print(f"             per-conjugate geometric mean mu = {mu16:.4f} (= 2^{math.log2(mu16):.3f})")

    # s = 32 sampled lower bounds
    m = 16
    best32 = 0
    for r in (4, 6, 8):
        b, R = sample_pm1_disjoint(m, r, 60000)
        print(f"\ns=32 (m=16): +/-1 disjoint-support 2r={2*r} sample max = {b} "
              f"(2^{math.log2(b):.1f})" if b else f"s=32 r={r}: all zero?!")
        best32 = max(best32, b)
    # structured candidates + hill climb from random start
    structured = [
        [1] * 16,
        [(-1) ** i for i in range(16)],
        [1] * 8 + [-1] * 8,
        [2] * 8 + [0] * 8,
        [2, -2] * 8,
    ]
    for c in structured:
        best32 = max(best32, negacyclic_det(c, 16))
    hb, hR = hill_climb(16, [random.choice([-2, -1, 0, 1, 2]) for _ in range(16)])
    best32 = max(best32, hb)
    wc32 = 32 ** 16
    mu32 = best32 ** (1 / 16)
    print(f"\ns=32 (m=16): best found (sample+structured+hillclimb, HONEST LOWER BOUND) "
          f"= {best32} (2^{math.log2(best32):.1f})")
    print(f"             worst-case s^(s/2) = 32^16 = 2^80;  found/worst = 2^"
          f"{math.log2(best32) - 80:.1f}")
    print(f"             per-conjugate mu >= {mu32:.4f} (= 2^{math.log2(mu32):.3f})")

    # the s = 64 verdict arithmetic
    print("\n--- A3 verdict arithmetic for s = 64 (m = 32) ---")
    print("budget: the reach-table row s=64, rate 1/4 wants the prime window")
    print("  log2(p) in (log2(max-resultant), 128 + log2(count) ) nonempty;")
    print("  with count ~ 2^r C(16,r) ~ 2^20, budget is log2(max) < ~148, i.e.")
    print("  mu = max^(1/32) < 2^4.625.")
    for name, mu in (("s=16 exact mu", mu16), ("s=32 lower-bound mu", mu32)):
        verdict = "WITHIN budget" if math.log2(mu) < 4.625 else "EXCEEDS budget"
        print(f"  {name} = 2^{math.log2(mu):.3f}  -> {verdict}")
    if math.log2(mu16) < 4.625 and math.log2(mu32) < 4.625:
        print("VERDICT: A3 ALIVE at the mu-extrapolation level -- a certified")
        print("  branch-and-bound max at s=64 over the +/-1 difference family is the")
        print("  next rung (the {-2..2} superset is 5^32 ~ 2^74: needs the orbit/")
        print("  submultiplicativity pruning, not enumeration).")
    else:
        print("VERDICT: A3 DEAD -- the per-conjugate mean already exceeds the")
        print("  s=64 budget; the TZ external (K4 route) is necessary for s >= 64.")
    print("\nall assertions passed")
