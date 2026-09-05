#!/usr/bin/env python3
"""Finite controls for the scalar tail split; no Lean/MCA/prize closure."""
from fractions import Fraction
from math import comb, factorial
import json

from astra_scalar_differential_carrier_check import scalar_counts
from astra_tail_regularity_cube_check import add, scale, mul, diff, evaluate


X = {(1, 0, 0, 0): 1}
Y = {(0, 1, 0, 0): 1}
R = {(0, 0, 1, 0): 1}


def tail(p, F, w):
    H = diff(p, F, 2)
    G = scale(p, add(p, diff(p, F, 0), mul(p, R, diff(p, F, 1))), -1)
    VH = add(p, mul(p, H, diff(p, H, 0)),
             mul(p, H, R, diff(p, H, 1)), mul(p, G, diff(p, H, 2)))
    N = G
    numerators = {2: N}
    for j in range(2, w+1):
        N = add(p, mul(p, H, H, diff(p, N, 0)),
                mul(p, H, H, R, diff(p, N, 1)),
                mul(p, H, G, diff(p, N, 2)),
                scale(p, mul(p, N, VH), -(2*j-3)))
        numerators[j+1] = N
    return H, numerators


def modulo_power_curve(p, poly, degree):
    """Exact remainder by the monic relation R^d=d^d*Y^(d-1)."""
    out = {}
    for (x, y, r, z), c in poly.items():
        quotient, remainder = divmod(r, degree)
        key = x, y+(degree-1)*quotient, remainder, z
        out[key] = (out.get(key, 0)+c*pow(degree, degree*quotient, p)) % p
    return {key: c for key, c in out.items() if c}


def power_curve_controls():
    rows = []
    for p in (17, 257, 2130706433):
        for degree in (2, 3, 4):
            F = {(0, 0, degree, 0): 1,
                 (0, degree-1, 0, 0): -pow(degree, degree, p) % p}
            weight = degree*(degree-1)
            assert weight+1 < p
            H, numerators = tail(p, F, degree)
            assert not modulo_power_curve(p, numerators[degree+1], degree)
            identities = 0
            for t in (1, 2, 3, 5, 7):
                initial = (0, pow(t, degree, p),
                           degree*pow(t, degree-1, p) % p, 0)
                h = evaluate(p, H, initial)
                assert h and evaluate(p, F, initial) == 0
                # q(U)=(U+t)^degree. Check every reconstructed derivative.
                for j in range(2, degree+1):
                    expected = factorial(degree)//factorial(degree-j)*pow(t, degree-j, p)
                    assert evaluate(p, numerators[j], initial) == expected*pow(h, 2*j-3, p) % p
                    identities += 1
                # Independent direct substitution in the full equation.
                for u in (0, 1, 4, 9):
                    values = (u, pow(u+t, degree, p),
                              degree*pow(u+t, degree-1, p) % p, 0)
                    assert evaluate(p, F, values) == 0
                    identities += 1
                # Coefficient of U^(degree-1) recovers t; no inseparable map.
                assert comb(degree, degree-1)*t*pow(degree, -1, p) % p == t % p
            rows.append({"prime": p, "degree": degree, "weighted_degree": weight,
                         "tail_remainder_zero": True, "identities": identities,
                         "coefficient_curve_degree": degree})
    return rows


def boundary_controls():
    rows = []
    for p in (17, 257, 2130706433):
        # R-Y=0 has next tail R, a proper cut; only f=0 has degree < p.
        F = add(p, R, scale(p, Y, -1))
        H, numerators = tail(p, F, 2)
        assert H == {(0, 0, 0, 0): 1} and numerators[3] == R
        # X*R-2Y=0 has the family f=cX^2 and an identically zero next tail.
        F = add(p, mul(p, X, R), scale(p, Y, -2))
        H, numerators = tail(p, F, 2)
        assert H == X and not numerators[3]
        for c in (0, 1, 3, 8):
            for u in (0, 1, 2, 6):
                assert evaluate(p, F, (u, c*u*u % p, 2*c*u % p, 0)) == 0
        rows.append({"prime": p, "proper_linear_cut": True,
                     "flat_line_checked": True})
    # The old w<p condition alone does NOT justify the new flat-family step.
    # In F7, F=R-X^7 has delta^3(Y)=0, but at x0=1 its reconstructed
    # q(U)=y0+U-1 gives F(U,q,q')=1-U^7=-(U-1)^7, not zero.
    p = 7
    F = add(p, R, {(7, 0, 0, 0): -1})
    H, numerators = tail(p, F, 2)
    assert H == {(0, 0, 0, 0): 1} and not numerators[3]
    translated = [(int(j == 0)-comb(7, j)) % 7 for j in range(8)]
    assert translated == [0]*7+[6]
    assert evaluate(p, F, (2, 1, 1, 0)) != 0
    return {"factor_cases": rows, "characteristic_gate_counterexample": {
        "prime": 7, "w": 2, "weighted_degree": 7,
        "zero_tail": True, "reconstructed_polynomial_solves_equation": False,
        "residual_order_at_x0": 7}}


def exponential_controls():
    # Truncated exp(t*d/dx) is multiplicative mod t^p, even on inputs
    # of degree >=p. Exhaustive monomials expose the Frobenius boundary.
    rows = []
    for p in (2, 3, 5, 7, 17):
        identities = 0
        for a in range(2*p+1):
            for b in range(2*p+1):
                for j in range(p):
                    actual = sum(comb(a, k)*comb(b, j-k)
                                 for k in range(j+1) if k <= a and j-k <= b) % p
                    assert actual == (comb(a+b, j) if j <= a+b else 0) % p
                    identities += 1
        rows.append({"prime": p, "monomial_product_coefficients": identities})
    return rows


def production():
    n, w, A, m, cap, p = 262144, 131071, 181353, 99, 30, 2130706433
    D = m*A
    C, L, d = scalar_counts(D, w, m, cap)
    assert (C, L, d, C-n*L) == (30638265433, 116870, 136, 1496153)
    assert p > D > w
    ratio = Fraction(n-w, A-w)
    E = (2*w-1)*(d-1)+1
    assert E >= ratio
    bound = d*E+d*(d-1)
    assert (E, bound) == (35389036, 4812927256)
    assert bound == d*(2*w*(d-1)+1)
    pairs = bound*(bound+1)//2
    assert pairs == 11582134388180308396 < p**6
    assert bound < p**6//2**128 == 274980728111395087
    # Every factor, including a linear flat factor, fits the aggregate cap.
    for factor_degree in range(1, d+1):
        factor_E = (2*w-1)*(factor_degree-1)+1
        assert max(factor_E, ratio) <= E
    return {"D": D, "characteristic": p, "YR_degree": d,
            "proper_cut_degree": E, "proper_point_allowance": d*E,
            "singular_allowance": d*(d-1), "flat_incidence_ratio": str(ratio),
            "written_uniform_list_bound": bound, "projection_pair_count": pairs,
            "previous_written_bound": 12546010856, "MCA_bound_proved": False}


def main():
    print(json.dumps({"status": "PASS_SCALAR_TAIL_SPLIT_CONTROLS",
                      "power_curves": power_curve_controls(),
                      "boundaries": boundary_controls(),
                      "truncated_exponential": exponential_controls(),
                      "production": production(),
                      "independent_mathematical_review": False,
                      "Lean_formalization": False, "prize_solved": False}, indent=2))


if __name__ == "__main__":
    main()
