#!/usr/bin/env python3
"""Positive source margin with a universal factor and simple selected tails.

Exact finite controls only; no production properness or prize theorem.
See docs/kb/astra_positive_kernel_factor-2026-09-05.md.
Uses the Python standard library, including at the companion characteristic.
"""
from itertools import combinations
import json
from math import comb, isqrt

N, W, A = 10, 2, 8
U0 = (0,)*A+(1, 1)
U1 = (3, 1, 4, 1, 5, 9, 2, 6, 5, 3)


def trim(f, p):
    f = [c % p for c in f]
    while f and not f[-1]:
        f.pop()
    return f


def add(f, g, p):
    return trim([(f[i] if i < len(f) else 0)+(g[i] if i < len(g) else 0)
                 for i in range(max(len(f), len(g)))], p)


def scale(f, c, p):
    return trim([c*x for x in f], p)


def mul(f, g, p):
    if not f or not g:
        return []
    out = [0]*(len(f)+len(g)-1)
    for i, a in enumerate(f):
        for j, b in enumerate(g):
            out[i+j] = (out[i+j]+a*b) % p
    return trim(out, p)


def deriv(f, p):
    return trim([i*f[i] for i in range(1, len(f))], p)


def evaluate(f, x, p):
    out = 0
    for c in reversed(f):
        out = (out*x+c) % p
    return out


def divide(f, g, p):
    f, g = trim(f, p), trim(g, p)
    assert g
    quotient = [0]*max(0, len(f)-len(g)+1)
    while f and len(f) >= len(g):
        shift = len(f)-len(g)
        coefficient = f[-1]*pow(g[-1], -1, p) % p
        quotient[shift] = coefficient
        f = add(f, [0]*shift+scale(g, -coefficient, p), p)
    return trim(quotient, p), f


def gcd(f, g, p):
    while g:
        f, g = g, divide(f, g, p)[1]
    return scale(f, pow(f[-1], -1, p), p) if f else []


def locator(nodes, p):
    out = [1]
    for x in nodes:
        out = mul(out, [-x, 1], p)
    return out


def source_basis(D, T, s2):
    # Exponents (X,Y,R,S,Z); R cap is one in both controls.
    return [(x, i, j, k, z)
            for h in range(T+1) for i in range(h+1)
            for j in range(min(1, h-i)+1)
            for k in range(min(s2, h-i-j)+1) for z in [h-i-j-k]
            for x in range(max(0, D-W*i-(W-1)*j-(W-2)*k))]


def contact_column(mon, node, m, order, p):
    """Direct expansion: X=node+t, Y=u0+Z*u1+t*R-t^2*S+v.

    Here m=order+1, so v has weight m and contributes no retained row.
    Rows retain all coefficients of contact weight strictly below m.
    """
    assert m == order+1
    x, i, j, k, z = mon
    terms = {(0, 0, 0, 0): U0[node], (0, 0, 0, 1): U1[node],
             (1, 1, 0, 0): 1}
    if order == 2:
        terms[2, 0, 1, 0] = -1
    power = {(0, 0, 0, 0): 1}
    for _ in range(i):
        result = {}
        for a, ca in power.items():
            for b, cb in terms.items():
                key = tuple(u+v for u, v in zip(a, b))
                if key[0] < m:
                    result[key] = (result.get(key, 0)+ca*cb) % p
        power = {key: value for key, value in result.items() if value}
    out = {}
    for tx in range(min(x, m-1)+1):
        coefficient = comb(x, tx)*pow(node, x-tx, p) % p
        for (t, r, s, zz), value in power.items():
            if t+tx < m:
                key = t+tx, r+j, s+k, zz+z
                out[key] = (out.get(key, 0)+coefficient*value) % p
    return {key: value for key, value in out.items() if value}


def contact_matrix(basis, nodes, m, order, p):
    columns = []
    for mon in basis:
        column = {}
        for node in nodes:
            column.update({(node,)+key: value for key, value in
                           contact_column(mon, node, m, order, p).items()})
        columns.append(column)
    keys = sorted({key for column in columns for key in column})
    return [[column.get(key, 0) for column in columns] for key in keys]


def kernel(matrix, p):
    """Complete exact row reduction, with direct checks of every null vector."""
    rows = [row.copy() for row in matrix]
    width = len(rows[0])
    pivots = []
    for c in range(width):
        r = len(pivots)
        pivot = next((q for q in range(r, len(rows)) if rows[q][c]), None)
        if pivot is None:
            continue
        rows[r], rows[pivot] = rows[pivot], rows[r]
        inverse = pow(rows[r][c], -1, p)
        rows[r] = [a*inverse % p for a in rows[r]]
        for q in range(r+1, len(rows)):
            scalar = rows[q][c]
            if scalar:
                rows[q] = [(a-scalar*b) % p for a, b in zip(rows[q], rows[r])]
        pivots.append(c)
        if len(pivots) == len(rows):
            break
    free = [c for c in range(width) if c not in set(pivots)]
    result = []
    for c in free:
        vector = [0]*width
        vector[c] = 1
        for r in reversed(range(len(pivots))):
            pivot = pivots[r]
            vector[pivot] = -sum(a*b for a, b in
                                 zip(rows[r][pivot+1:], vector[pivot+1:])) % p
        assert all(sum(a*b for a, b in zip(row, vector)) % p == 0 for row in matrix)
        result.append(vector)
    return len(pivots), result


def maximum_quadratic_agreement_on_zero_set(p):
    # Every degree <=2 polynomial agreeing on >=3 nodes occurs in this list.
    interpolants = set()
    for nodes in combinations(range(A), W+1):
        f = []
        for node in nodes:
            numerator = locator([x for x in nodes if x != node], p)
            coefficient = U1[node]*pow(evaluate(numerator, node, p), -1, p)
            f = add(f, scale(numerator, coefficient, p), p)
        interpolants.add(tuple(f))
    maximum = max(sum(evaluate(f, x, p) == U1[x] for x in range(A))
                  for f in interpolants)
    assert maximum+(N-A) < A
    return maximum


def hermite_reduced_check(coefficients, p):
    """Independent 4-by-5 description after dividing the forced error factor.

    b=W*v, a=-W'*v+W*u, deg(v)<=2, deg(u)<=1. The degree <=15
    Hermite interpolant for c must have its coefficients 12,...,15 zero.
    """
    Wpoly = locator(range(A), p)
    Wprime = deriv(Wpoly, p)
    channels = []
    for is_v, bound in ((True, 3), (False, 2)):
        for degree in range(bound):
            monomial = [0]*degree+[1]
            a = scale(mul(Wprime, monomial, p), -1, p) if is_v else mul(Wpoly, monomial, p)
            b = mul(Wpoly, monomial, p) if is_v else []
            c = []
            for node in range(A):
                ell = locator([x for x in range(A) if x != node], p)
                ell = scale(ell, pow(evaluate(ell, node, p), -1, p), p)
                ell2 = mul(ell, ell, p)
                d = evaluate(deriv(ell, p), node, p)
                H = mul([1+2*d*node, -2*d], ell2, p)
                K = mul([-node, 1], ell2, p)
                c = add(c, scale(H, -evaluate(a, node, p)*U1[node], p), p)
                c = add(c, scale(K, -evaluate(deriv(a, p), node, p)*U1[node], p), p)
            assert all((evaluate(c, x, p)+evaluate(a, x, p)*U1[x]) % p == 0 and
                       (evaluate(deriv(c, p), x, p)+evaluate(deriv(a, p), x, p)*U1[x]) % p == 0
                       for x in range(A))
            channels.append((a, b, c))
    matrix = [[f[2][degree] if degree < len(f[2]) else 0 for f in channels]
              for degree in range(12, 16)]
    rank, nulls = kernel(matrix, p)
    assert rank == 4 and len(nulls) == 1
    E = locator((8, 9), p)
    recovered = []
    for index in range(3):
        f = []
        for scalar, channel in zip(nulls[0], channels):
            f = add(f, scale(channel[index], scalar, p), p)
        recovered.append(mul(mul(E, E, p), f, p))
    first = next((j, k) for j, f in enumerate(recovered) for k, c in enumerate(f) if c)
    j, k = first
    ratio = coefficients[j][k]*pow(recovered[j][k], -1, p) % p
    assert ratio and all(scale(f, ratio, p) == g for f, g in zip(recovered, coefficients))
    return rank


def old_control(p):
    basis = source_basis(16, 1, 0)
    matrix = contact_matrix(basis, range(N), 2, 1, p)
    rank, nulls = kernel(matrix, p)
    local_ranks = [kernel(contact_matrix(basis, [x], 2, 1, p), p)[0]
                   for x in range(N)]
    assert (len(basis), rank, len(nulls), local_ranks) == (61, 60, 1, [6]*N)
    Q = nulls[0]
    coefficients = []
    for coordinate in (1, 2, 4):
        coefficient = [0]*16
        for mon, value in zip(basis, Q):
            if mon[coordinate]:
                coefficient[mon[0]] = value
            elif sum(mon[1:]) == 0:
                assert value == 0
        coefficients.append(trim(coefficient, p))
    reduced_rank = hermite_reduced_check(coefficients, p)
    common = gcd(gcd(coefficients[0], coefficients[1], p), coefficients[2], p)
    E = locator((8, 9), p)
    expected_common = mul(E, E, p)
    if p == 17:
        expected_common = mul(expected_common, [-1, 1], p)
    assert common == expected_common
    primitive = []
    for coefficient in coefficients:
        quotient, remainder = divide(coefficient, common, p)
        assert not remainder
        primitive.append(quotient)
    a, b, c = primitive  # F=a(X)Y+b(X)R+c(X)Z.
    assert b and gcd(gcd(a, b, p), c, p) == [1]
    factor_orders = []
    for x in range(N):
        aa, bb, cc = [evaluate(f, x, p) for f in primitive]
        da, db, dc = [evaluate(deriv(f, p), x, p) for f in primitive]
        order_zero = (U0[x]*aa % p, bb, (U1[x]*aa+cc) % p)
        order_one = (U0[x]*da % p, (aa+db) % p, (U1[x]*da+dc) % p)
        if any(order_zero):
            factor_orders.append(0)
        elif any(order_one):
            factor_orders.append(1)
        else:
            assert aa != 0  # The coefficient of v gives exact contact two.
            factor_orders.append(2)
    expected_orders = [2]*A+[0, 0]
    if p == 17:
        expected_orders[1] = 1
    assert factor_orders == expected_orders
    # On F=0, delta(Y) = -(aY+cZ)/b. Its j-th tail is (AjY+CjZ)/b^j.
    Aj, Cj = [1], []
    tails = [(Aj, Cj)]
    bp = deriv(b, p)
    for j in range(4):
        next_a = add(add(mul(b, deriv(Aj, p), p),
                          scale(mul(bp, Aj, p), -j, p), p),
                     scale(mul(a, Aj, p), -1, p), p)
        next_c = add(add(mul(b, deriv(Cj, p), p),
                          scale(mul(bp, Cj, p), -j, p), p),
                     scale(mul(c, Aj, p), -1, p), p)
        Aj, Cj = next_a, next_c
        tails.append((Aj, Cj))
    determinant = add(mul(tails[3][0], tails[4][1], p),
                      scale(mul(tails[3][1], tails[4][0], p), -1, p), p)
    assert determinant  # Exact polynomial nonvanishing, not a sampled identity.
    return primitive, {"prime": p, "columns": 61, "full_rank": rank,
                       "uniform_local_rank": 6, "uniform_margin": 1,
                       "kernel_dimension": 1, "primitive_coefficients_Y_R_Z": primitive,
                       "independent_4_by_5_Hermite_rank": reduced_rank,
                       "primitive_coefficient_degrees": [len(f)-1 for f in primitive],
                       "coefficient_gcd": common,
                       "primitive_factor_nodewise_contact_orders": factor_orders,
                       "maximum_u1_quadratic_agreement_on_first_eight":
                           maximum_quadratic_agreement_on_zero_set(p),
                       "complete_nearby_family": [{"gamma": 0, "f": [0]}],
                       "tail_3_4_determinant_degree": len(determinant)-1,
                       "tail_3_4_determinant_leading_coefficient": determinant[-1]}


def second_control(primitive, p):
    basis = source_basis(24, 2, 1)
    matrix = contact_matrix(basis, range(N), 3, 2, p)
    rank, nulls = kernel(matrix, p)
    local_ranks = [kernel(contact_matrix(basis, [x], 3, 2, p), p)[0]
                   for x in range(N)]
    assert len(basis) == 296 and local_ranks == [27]*N
    assert len(nulls) == len(basis)-rank >= 26
    a, b, c = primitive
    ap, bp, cp = [deriv(f, p) for f in primitive]
    for X in range(N, min(p, N+32)):
        aa, bb, cc = [evaluate(f, X, p) for f in primitive]
        if not bb:
            continue
        Y, Z = 2, 3
        R = -(aa*Y+cc*Z)*pow(bb, -1, p) % p
        S = -(evaluate(ap, X, p)*Y+(aa+evaluate(bp, X, p))*R+
              evaluate(cp, X, p)*Z)*pow(2*bb % p, -1, p) % p
        assert (aa*Y+bb*R+cc*Z) % p == 0
        assert (evaluate(ap, X, p)*Y+(aa+evaluate(bp, X, p))*R+
                2*bb*S+evaluate(cp, X, p)*Z) % p == 0
        values = [pow(X, x, p)*pow(Y, i, p)*pow(R, j, p)*pow(S, k, p)*pow(Z, z, p) % p
                  for x, i, j, k, z in basis]
        for index, Q in enumerate(nulls):
            value = sum(a*b for a, b in zip(values, Q)) % p
            if value:
                return {"columns": len(basis), "full_rank": rank,
                        "uniform_local_rank": 27, "uniform_margin": 26,
                        "kernel_dimension": len(nulls), "proper_basis_vector": index,
                        "point_X_Y_R_S_Z": [X, Y, R, S, Z],
                        "F_R_at_point": bb, "Q_at_point": value,
                        "entire_new_kernel_contained": False}
    raise AssertionError("No nonzero pullback witness found")


def main():
    result = []
    for p in (17, 257, 65537, 2130706433):
        assert p > N and all(p % d for d in range(2, isqrt(p)+1))
        primitive, row = old_control(p)
        row["positive_second_order_control"] = second_control(primitive, p)
        result.append(row)
    print(json.dumps({"status": "PASS_POSITIVE_MARGIN_UNIVERSAL_FACTOR_CONTROLS",
                      "n": N, "w": W, "agreements": A, "u0": U0, "u1": U1,
                      "controls": result, "production_geometry": False,
                      "production_second_order_properness_proved": False,
                      "prize_bound_improved": False, "lean_run_performed": False}, indent=2))


if __name__ == "__main__":
    main()
