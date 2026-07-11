#!/usr/bin/env python3
"""Probe for the small-good-set discharge of StrictCoeffPolysResidual (#304).

Claim under test (the Lean brick `exists_coeff_interpolant_of_card_le`):
  over a field F, for ANY finset S with |S| <= k+1 and ANY function c : S -> F,
  there is a polynomial B with natDegree < k+1 (i.e. deg <= k) and
  B(z) = c(z) for all z in S.

Control (minimal falsification of the boundary): at |S| = k+2 the same claim
should FAIL for generic c — confirming k+1 is the exact cutoff, i.e. the
residual's whole content lives in the large-set sector |S| >= k+2.

Field: GF(p), p prime. Interpolation: solve the Vandermonde system / Lagrange.
"""

import itertools
import random

P = 13  # field size


def inv(a: int) -> int:
    return pow(a, P - 2, P)


def lagrange_coeffs(pts):
    """Return coefficient list (low->high) of the Lagrange interpolant through pts."""
    n = len(pts)
    coeffs = [0] * max(n, 1)
    for i, (xi, yi) in enumerate(pts):
        # numerator polynomial prod_{j != i} (X - xj)
        num = [1]
        denom = 1
        for j, (xj, _) in enumerate(pts):
            if j == i:
                continue
            # multiply num by (X - xj)
            new = [0] * (len(num) + 1)
            for t, ct in enumerate(num):
                new[t] = (new[t] - ct * xj) % P
                new[t + 1] = (new[t + 1] + ct) % P
            num = new
            denom = (denom * (xi - xj)) % P
        scale = (yi * inv(denom)) % P if denom % P else None
        assert scale is not None, "nodes must be distinct"
        for t, ct in enumerate(num):
            coeffs[t] = (coeffs[t] + scale * ct) % P
    return coeffs


def poly_deg(coeffs):
    d = -1
    for t, ct in enumerate(coeffs):
        if ct % P:
            d = t
    return d


def main():
    rng = random.Random(304)
    trials = 4000
    small_ok = 0
    for _ in range(trials):
        k = rng.randint(1, 4)
        m = rng.randint(1, k + 1)  # |S| <= k+1
        S = rng.sample(range(P), m)
        c = {z: rng.randrange(P) for z in S}
        pts = [(z, c[z]) for z in S]
        coeffs = lagrange_coeffs(pts)
        d = poly_deg(coeffs)
        assert d < k + 1, f"FAIL small: k={k} |S|={m} deg={d}"
        for z in S:
            v = sum(ct * pow(z, t, P) for t, ct in enumerate(coeffs)) % P
            assert v == c[z], f"FAIL small eval: k={k} z={z}"
        small_ok += 1

    # Control: |S| = k+2, generic c should NOT be degree-<=k interpolable.
    control_fail = 0
    control_trials = 2000
    for _ in range(control_trials):
        k = rng.randint(1, 4)
        m = k + 2
        S = rng.sample(range(P), m)
        c = {z: rng.randrange(P) for z in S}
        # fit on first k+1 points, test on the last
        pts = [(z, c[z]) for z in S[: k + 1]]
        coeffs = lagrange_coeffs(pts)
        zlast = S[-1]
        v = sum(ct * pow(zlast, t, P) for t, ct in enumerate(coeffs)) % P
        if v != c[zlast]:
            control_fail += 1

    print(f"small-set claim: {small_ok}/{trials} PASS (deg<k+1 and exact eval, GF({P}))")
    print(
        f"control |S|=k+2: {control_fail}/{control_trials} generic c NOT interpolable "
        f"(expected ~{control_trials * (P - 1) // P})"
    )
    assert small_ok == trials
    assert control_fail > control_trials * 0.8, "boundary control too weak"
    print("PROBE PASS: cutoff is exactly |S| = k+1; small sector unconditional, large sector carries the content")


if __name__ == "__main__":
    main()
