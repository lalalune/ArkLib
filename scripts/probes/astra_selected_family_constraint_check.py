#!/usr/bin/env python3
"""Fixed checks for selected-graph Jacobi divisibility and rigidity.

See docs/kb/astra_selected_family_constraint-2026-09-05.md.
No selected-factor count or protocol certificate is produced.
"""
import json
from astra_colon_audit import matrix_rank


def add(a, b, p):
    result = dict(a)
    for exponent, coefficient in b.items():
        result[exponent] = (result.get(exponent, 0)+coefficient) % p
    return {exponent: coefficient for exponent, coefficient in result.items()
            if coefficient % p}


def scale(a, scalar, p):
    return {exponent: coefficient*scalar % p for exponent, coefficient in a.items()
            if coefficient*scalar % p}


def mul(a, b, p):
    result = {}
    for first, c in a.items():
        for second, d in b.items():
            exponent = tuple(x+y for x, y in zip(first, second))
            result[exponent] = (result.get(exponent, 0)+c*d) % p
    return {exponent: coefficient for exponent, coefficient in result.items()
            if coefficient}


def power(a, exponent, p):
    result = {(0, 0, 0, 0): 1}
    for _ in range(exponent):
        result = mul(result, a, p)
    return result


def monomial(t=0, v=0, r=0, z=0):
    return {(t, v, r, z): 1}


def contact_check(n, point, p, kind):
    one = monomial()
    X = add(scale(one, point, p), monomial(t=1), p)
    V = add(power(X, n, p), scale(one, -1, p), p)
    Vprime = scale(power(X, n-1, p), n, p)
    R, Z = monomial(r=1), monomial(z=1)
    if kind == "pencil":
        A = add(monomial(t=1, r=1), monomial(v=1), p)
        local = add(add(mul(Vprime, A, p), scale(mul(V, R, p), -1, p), p),
                    power(A, 2, p), p)
    else:
        Y = add(scale(add(one, scale(Z, -1, p), p), pow(point, -1, p), p),
                add(monomial(t=1, r=1), monomial(v=1), p), p)
        Phi = add(add(mul(X, Y, p), scale(one, -1, p), p), Z, p)
        A = add(V, scale(mul(X, Vprime, p), -1, p), p)
        local = add(mul(A, Y, p), mul(mul(X, V, p), R, p), p)
        local = add(local, mul(add(one, scale(Z, -1, p), p), Vprime, p), p)
        local = add(local, power(Phi, 2, p), p)
    assert min(t+2*v for t, v, r, z in local) == 2


def univariate_add(a, b, p):
    length = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0)+(b[i] if i < len(b) else 0)) % p
            for i in range(length)]


def univariate_scale(a, scalar, p):
    return [coefficient*scalar % p for coefficient in a]


def univariate_shift(a, degree):
    return [0]*degree+a


def jacobi_matrix(h, a, b, w, p):
    columns = []
    for k in range(w+1):
        first = univariate_scale(univariate_shift(h, k-1), k, p) if k else []
        columns.append(univariate_add(first, univariate_shift(a, k), p))
    columns.append(b)
    length = max(map(len, columns))
    columns = [column+[0]*(length-len(column)) for column in columns]
    rows = [list(row) for row in zip(*columns)]
    fixed = [row[:-1] for row in rows]
    return w+1-matrix_rank(fixed, p), w+2-matrix_rank(rows, p)


def main():
    rows = []
    contacts = 0
    for p, n, generator, w in ((17, 8, 2, 3), (5, 4, 2, 1), (17, 4, 4, 1)):
        nodes = tuple(pow(generator, i, p) for i in range(n))
        assert len(set(nodes)) == n and all(pow(x, n, p) == 1 for x in nodes)
        V = [p-1]+[0]*(n-1)+[1]
        Vprime = [0]*(n-1)+[n % p]
        for kind in ("pencil", "far_singleton"):
            for point in nodes:
                contact_check(n, point, p, kind)
                contacts += 1
            if kind == "pencil":
                h = univariate_scale(V, -1, p)
                a = Vprime
                b = univariate_scale(Vprime, -1, p)
                c = max(n+w-1, 2*w)
                expected = 1
            else:
                h = univariate_shift(V, 1)
                a = univariate_add(V, univariate_scale(univariate_shift(Vprime, 1), -1, p), p)
                b = univariate_scale(Vprime, -1, p)
                c = max(n+w, 2*(w+1))
                expected = 0
            fixed, total = jacobi_matrix(h, a, b, w, p)
            assert 2*n > c+1
            assert fixed == 0 and total == expected
            rows.append({"prime": p, "n": n, "w": w, "control": kind,
                         "contact_sum": 2*n, "actual_weight": c,
                         "fixed_seed_nullity": fixed, "full_jacobi_nullity": total})

    production = []
    w, agreement_count, nu = 131071, 181353, 34
    contact_sum = agreement_count*nu
    assert contact_sum == 6166002
    for c, expected_minimal in ((6160327, 136745), (6160337, 136735)):
        h_degree_upper = c-w+1
        minimal_lower = contact_sum-h_degree_upper
        assert minimal_lower == expected_minimal > w
        production.append({"specified_actual_c": c, "contact_sum": contact_sum,
                           "h_degree_upper": h_degree_upper,
                           "minimal_nodes_lower": minimal_lower,
                           "lower_minus_w": minimal_lower-w})
    c = 6160327
    low_contact_sum = 33*agreement_count
    threshold = (c+1-low_contact_sum)//24+1
    assert threshold == 7320
    boundary = []
    for high_nodes, expected_minimal in ((7319, 131048), (7320, 131072)):
        selected_sum = low_contact_sum+24*high_nodes
        minimal_lower = selected_sum-(c-w+1)
        assert minimal_lower == expected_minimal
        assert (selected_sum > c+1) == (high_nodes >= threshold)
        boundary.append({"high_contact_agreement_nodes": high_nodes,
                         "contact_sum": selected_sum, "minimal_nodes_lower": minimal_lower,
                         "rigidity_gate": selected_sum > c+1})
    print(json.dumps({"status": "PASS_SELECTED_JACOBI_CONSTRAINT_NO_COUNT_BOUND",
                      "contact_expansions": contacts, "jacobi_matrix_checks": len(rows),
                      "controls": rows, "conditional_profile_rows": production,
                      "profile_33_57_threshold": threshold,
                      "profile_33_57_boundary": boundary}, indent=2))


if __name__ == "__main__":
    main()
