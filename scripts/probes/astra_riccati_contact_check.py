#!/usr/bin/env python3
"""Boundary controls for the all-multiplicity Riccati contact obstruction."""
from math import comb
import json

from astra_mca_moment_rigidity_check import P, evaluate, locator, mul, root, subtract


def trim(f):
    f = list(f)
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return tuple(f) or (0,)


def add(f, g, p):
    return trim(((f[i] if i < len(f) else 0)+(g[i] if i < len(g) else 0)) % p
                for i in range(max(len(f), len(g))))


def derivative(f, p):
    return trim(i*f[i] % p for i in range(1, len(f)))


def kernel(nodes, values, p, w, A, m, pairs=((0, 0), (1, 0), (2, 0), (0, 1))):
    cap = m*A
    basis = [(a, i, j) for i, j in pairs
             for a in range(max(0, cap-w*i-(w-1)*j))]
    pivots, nulls = {}, []

    def subtract_scaled(target, source, c):
        for key, value in source.items():
            updated = (target.get(key, 0)-c*value) % p
            if updated:
                target[key] = updated
            else:
                target.pop(key, None)

    for index, (a, i, j) in enumerate(basis):
        column = {}
        for ni, (x, v) in enumerate(zip(nodes, values)):
            for z in range(i+1):
                for r in range(i-z+1):
                    for t in range(min(a, m-1-r-2*z)+1):
                        key = ni, t+r, z, j+r
                        value = (comb(i, z)*comb(i-z, r)*pow(v, i-z-r, p)*
                                 comb(a, t)*pow(x, a-t, p)) % p
                        column[key] = (column.get(key, 0)+value) % p
        column = {key: value for key, value in column.items() if value}
        combination = {index: 1}
        while column:
            key = min(column)
            if key not in pivots:
                inverse = pow(column[key], -1, p)
                pivots[key] = ({key: value*inverse % p for key, value in column.items()},
                               {key: value*inverse % p for key, value in combination.items()})
                break
            old, old_combination = pivots[key]
            scalar = column[key]
            subtract_scaled(column, old, scalar)
            subtract_scaled(combination, old_combination, scalar)
        else:
            assert combination
            coefficients = {(i, j): [0]*max(1, cap-w*i-(w-1)*j)
                            for i, j in pairs}
            for index, coefficient in combination.items():
                a, i, j = basis[index]
                coefficients[i, j][a] = coefficient
            nulls.append(tuple(trim(coefficients[key]) for key in pairs))
    return len(basis), len(pivots), nulls


def check_contact_order_two(coefficients, nodes, values, p):
    A, B, C, D = coefficients
    Ap, Bp, Cp, Dp = [derivative(f, p) for f in coefficients]
    for x, v in zip(nodes, values):
        assert evaluate(D, x, p) == 0
        assert (evaluate(A, x, p)+v*evaluate(B, x, p)+v*v*evaluate(C, x, p)) % p == 0
        assert (evaluate(Ap, x, p)+v*evaluate(Bp, x, p)+v*v*evaluate(Cp, x, p)) % p == 0
        assert (evaluate(B, x, p)+2*v*evaluate(C, x, p)+evaluate(Dp, x, p)) % p == 0


def boundary_three_candidate_kernel():
    p, n, w, A, m = P, 16, 7, 11, 2
    z, ell = root(n, p), n//4
    R = locator((4, 8, 12), z, p)
    fourth = pow(z, ell, p)
    U = [(-pow(fourth, j, p) % p,)+(0,)*(ell-1)+(1,) for j in (1, 2, 3)]
    errors = [mul(R, mul(U[i], U[j], p), p) for i, j in ((0, 1), (0, 2), (1, 2))]
    V = errors[0]
    candidates = [subtract(V, error, p) for error in errors]
    nodes = [pow(z, i, p) for i in range(1, n)]
    values = [evaluate(V, x, p) for x in nodes]
    columns, rank, nulls = kernel(nodes, values, p, w, A, m)
    assert (columns, rank, len(nulls)) == (61, 60, 1)
    a, b, c, d = nulls[0]
    assert d != (0,)
    inverse = pow(d[-1], -1, p)
    normalized = tuple(trim(coefficient*inverse % p for coefficient in f) for f in (a, b, c, d))
    a, b, c, d = normalized
    assert d == locator(range(1, n), z, p) and len(d)-1 == len(nodes)
    check_contact_order_two(normalized, nodes, values, p)
    for f in candidates:
        assert len(f)-1 <= w
        assert sum(evaluate(f, x, p) == value for x, value in zip(nodes, values)) == A
        specialized = add(add(a, mul(b, f, p), p), mul(c, mul(f, f, p), p), p)
        specialized = add(specialized, mul(d, derivative(f, p), p), p)
        assert specialized == (0,)
    assert len(set(evaluate(f, 1, p) for f in candidates)) == 3
    return {"b": 3, "n": n, "prime": p, "contact_order": m,
            "columns": columns, "rank": rank, "kernel_dimension": len(nulls),
            "derivative_coefficient_is_domain_locator": True, "derivative_coefficient_degree": 15,
            "contact_equations_checked_independently": 60, "polynomial_solutions_checked": 3,
            "weighted_derivative_degree": 15+w-1, "weighted_cap": m*A}


def first_excluded_profile_control():
    b, p, m = 4, 97, 2
    N, w, A = 6*b-3, 3*b-2, 4*b-1
    nodes = list(range(N))
    values = [x*x % p for x in nodes]
    columns, rank, nulls = kernel(nodes, values, p, w, A, m)
    assert (columns, rank, len(nulls)) == (81, 71, 10)
    for coefficients in nulls:
        assert coefficients[3] == (0,)
        check_contact_order_two(coefficients, nodes, values, p)
    return {"b": b, "nodes": N, "prime": p, "contact_order": m,
            "columns": columns, "rank": rank, "kernel_dimension": len(nulls),
            "every_kernel_vector_has_zero_derivative_coefficient": True,
            "nonzero_algebraic_kernels_still_exist": True}


def arithmetic_controls():
    rows = []
    for b in range(4, 25):
        N, w, A = 6*b-3, 3*b-2, 4*b-1
        for m in range(1, 25):
            q = max(1, m-1)
            gap = N*q-(m*A-w)
            formula = 5*b-4 if m == 1 else 2*m*(b-1)-3*b+1
            assert gap == formula and gap > 0
            rows.append(gap)
    b = 178956971
    n, N, w, A = 6*b-2, 6*b-3, 3*b-2, 4*b-1
    assert n == 2**30 and N == n-1 and w == n//2-1
    assert w+3 == 536870914 < n and P > 2*w
    return {"generic_integer_controls": len(rows), "n": n, "N": N, "w": w, "A": A,
            "m_one_degree_gap": 5*b-4, "m_two_degree_gap": b-3,
            "gap_increment_for_larger_m": 2*(b-1),
            "all_m_production_degree_gap_has_separate_Lean_proof": True,
            "written_Riccati_whole_list_allowance_if_relation_exists": w+3}


def main():
    print(json.dumps({"status": "PASS_RICCATI_CONTACT_CONTROLS",
                      "boundary_kernel": boundary_three_candidate_kernel(),
                      "first_excluded_profile": first_excluded_profile_control(),
                      "arithmetic": arithmetic_controls(),
                      "Riccati_relation_for_all_production_lists_constructed": False,
                      "general_Riccati_list_count_Lean_formalized": False,
                      "prize_solved": False}, indent=2))


if __name__ == '__main__':
    main()
