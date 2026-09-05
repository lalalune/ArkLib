#!/usr/bin/env python3
"""Exact controls for a family-wide properness argument; requires NumPy.

This is not a proof of arbitrary production properness or a prize bound.
See docs/kb/astra_squarefree_denominator-2026-09-05.md.
"""
import json
import numpy as np

from astra_acceleration_extension_check import contact
from astra_full_kernel_properness_check import nullspace, safe_dot
from astra_hasse_containment_check import linear_matrix
from astra_positive_kernel_factor_check import (
    trim, add, scale, mul, deriv, evaluate, divide, gcd, locator,
)


def sub(a, b, p):
    return add(a, scale(b, -1, p), p)


def sum_polys(polys, p):
    out = []
    for poly in polys:
        out = add(out, poly, p)
    return out


def product_polys(polys, p):
    out = [1]
    for poly in polys:
        out = mul(out, poly, p)
    return out


def setup(p, A, e, ell):
    W, E, L = locator(range(A), p), locator(range(A, A+e), p), locator(range(-ell, 0), p)
    Wp, Lp, half = deriv(W, p), deriv(L, p), pow(2, -1, p)
    Wpp, Lpp = deriv(Wp, p), deriv(Lp, p)
    Jw = sub(mul(Wp, Wp, p), scale(mul(W, Wpp, p), half, p), p)
    Jl = sub(mul(Lp, Lp, p), scale(mul(L, Lpp, p), half, p), p)
    F = [sub(mul(Lp, W, p), mul(L, Wp, p), p), mul(L, W, p), [], Wp]
    dF = [deriv(F[0], p), add(F[0], deriv(F[1], p), p),
          scale(F[1], 2, p), deriv(F[3], p)]
    P = [sub(scale(mul(W, df, p), half, p), mul(Wp, f, p), p)
         for f, df in zip(F, dF)]
    assert P == [sum_polys([mul(L, Jw, p), scale(product_polys([Lp, W, Wp], p), -1, p),
                           scale(product_polys([Lpp, W, W], p), half, p)], p),
                 sub(product_polys([Lp, W, W], p), product_polys([L, W, Wp], p), p),
                 product_polys([L, W, W], p), scale(Jw, -1, p)]
    assert gcd(L, Lp, p) == [1] and gcd(W, L, p) == [1]
    assert gcd(gcd(F[0], F[1], p), F[3], p) == [1]
    # Cleared jets of W/L (Z=0) and 1/L (Z=1), with common denominator L^3.
    L2, L3 = mul(L, L, p), product_polys([L, L, L], p)
    hom = [mul(W, L2, p), mul(L, sub(mul(L, Wp, p), mul(Lp, W, p), p), p),
           sum_polys([scale(mul(L2, Wpp, p), half, p),
                      scale(product_polys([L, Lp, Wp], p), -1, p), mul(Jl, W, p)], p), []]
    particular = [L2, scale(mul(L, Lp, p), -1, p), Jl, L3]
    for jet in (hom, particular):
        assert not sum_polys([mul(a, b, p) for a, b in zip(P, jet)], p)
    return W, E, L, Wp, Lp, Jw, Jl, P, hom, particular


def control(p, e, ell, slack):
    w = 2
    A = w+3*e+ell-1+slack
    n, D = A+e, 2*A+3*e+ell+w-1
    W, E, L, Wp, Lp, Jw, Jl, P, hom, particular = setup(p, A, e, ell)
    assert D <= 3*A and n+ell < p
    margin = 5*D-3*w+3-12*n
    lower = w+4*ell-A-1
    assert margin > 0 and lower == margin+3*A-D >= 2
    u0 = [0]*A+list(range(1, e+1))
    u1 = [pow(evaluate(L, x, p), -1, p) for x in range(n)]
    basis, rows = linear_matrix(p, D, w, tuple(range(n)), u0, u1)
    matrix = np.asarray(rows, dtype=np.int64)
    vectors = nullspace(matrix, p)
    assert vectors.shape[1] >= lower
    assert nullspace(vectors, p).shape[1] == 0
    # Compare every direct-matrix column/node with the separate contact routine.
    channels = ((0, 0, 0, 0), (0, 0, 0, 1), (0, 1, 0, 0), (0, 0, 1, 0))
    axes = (None, 1, 2, 3, 4)
    for col, (var, x_degree) in enumerate(basis):
        mon = [x_degree, 0, 0, 0, 0]
        if axes[var] is not None:
            mon[axes[var]] = 1
        for node in range(n):
            expansion = contact(tuple(mon), node, u0[node], u1[node], 3, p)
            for channel, tail in enumerate(channels):
                for order in range(3):
                    assert rows[12*node+3*channel+order][col] == expansion.get((order,)+tail, 0)
    # The explicit contained vector is present in the full kernel.
    E3 = product_polys([E, E, E], p)
    explicit = [[]]+[mul(E3, a, p) for a in P]
    vector = np.array([explicit[var][j] if j < len(explicit[var]) else 0
                       for var, j in basis], dtype=np.int64)
    assert np.any(vector) and not np.any(safe_dot(matrix, vector, p))
    images, coefficient_forms = [], 0
    for column in vectors.T:
        polys = [[0]*D for _ in range(5)]
        for (var, j), value in zip(basis, column):
            polys[var][j] = int(value)
        polys = [trim(a, p) for a in polys]
        assert not polys[0]
        quotients = [divide(poly, E3, p) for poly in polys[1:]]
        assert all(not remainder for _, remainder in quotients)
        a, b, c, d = [q for q, _ in quotients]
        t, rem = divide(c, mul(W, W, p), p)
        assert not rem and len(t) <= ell+1
        B, rem = divide(add(b, product_polys([t, W, Wp], p), p), mul(W, W, p), p)
        assert not rem and len(B) <= ell
        C, rem = divide(sum_polys([a, scale(mul(t, Jw, p), -1, p),
                                  product_polys([B, W, Wp], p)], p), mul(W, W, p), p)
        assert not rem and len(C) <= ell-1
        homogeneous = sum_polys([mul(x, y, p) for x, y in zip((a, b, c, d), hom)], p)
        relation = sum_polys([mul(t, Jl, p), scale(product_polys([B, L, Lp], p), -1, p),
                              product_polys([C, L, L], p)], p)
        assert homogeneous == product_polys([W, W, W, relation], p)
        second = sum_polys([mul(x, y, p) for x, y in zip((a, b, c, d), particular)], p)
        images.append((homogeneous, second))
        coefficient_forms += 1
    lengths = [max(len(pair[j]) for pair in images) for j in range(2)]
    image_matrix = np.asarray([pair[0]+[0]*(lengths[0]-len(pair[0]))+
                               pair[1]+[0]*(lengths[1]-len(pair[1])) for pair in images],
                              dtype=np.int64).T
    contained = nullspace(image_matrix, p).shape[1]
    assert contained == 1
    return {"p": p, "n": n, "w": w, "A": A, "e": e, "ell": ell, "D": D,
            "columns": len(basis), "uniform_margin": margin,
            "redundant_agreement_rows": 3*A-D, "nullity_lower_bound": lower,
            "actual_nullity": vectors.shape[1], "contained_dimension": contained,
            "escape_quotient_dimension": vectors.shape[1]-contained,
            "column_node_comparisons": len(basis)*n,
            "coefficient_form_checks": coefficient_forms}


def inequality_controls():
    count = 0
    for w in (2, 3, 7, 31):
        for e in range(1, 31):
            for ell in range(1, 31):
                for A in range(w, w+5*(e+ell)+1):
                    D = 2*A+3*e+ell+w-1
                    margin = -2*A+3*e+5*ell+2*w-2
                    if D <= 3*A and margin > 0:
                        assert ell >= e+1 and A <= w+4*ell-3
                        assert w+4*ell-A-1 >= 2
                        count += 1
    return count


def main():
    controls = [control(p, e, e+1, slack)
                for p in (257, 65537, 2130706433) for e in (1, 2, 3) for slack in (0, 1)]
    print(json.dumps({"status": "PASS_SQUAREFREE_DENOMINATOR_PROPERNESS_CONTROLS",
                      "controls": controls, "inequality_controls": inequality_controls(),
                      "general_production_properness_proved": False,
                      "prize_bound_improved": False,
                      "independent_review_and_Lean_complete": False}, sort_keys=True))


if __name__ == "__main__":
    main()
