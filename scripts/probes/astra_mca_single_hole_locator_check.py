#!/usr/bin/env python3
"""Exact subgroup control for the single-hole locator formulation and relaxation."""

from itertools import combinations, product
import json


P = 17
OMEGA = (1, 2, 4, 8, 16, 15, 13, 9)
A_NODE, K, AGREEMENT = 1, 4, 5


def trim(f):
    f = [c % P for c in f]
    while len(f) > 1 and f[-1] == 0:
        f.pop()
    return tuple(f) if f else (0,)


def degree(f):
    f = trim(f)
    return -1 if f == (0,) else len(f) - 1


def add(f, g):
    return trim([(f[i] if i < len(f) else 0) + (g[i] if i < len(g) else 0)
                 for i in range(max(len(f), len(g)))])


def scale(c, f):
    return trim([c * v for v in f])


def multiply(f, g):
    result = [0] * (len(f) + len(g) - 1)
    for i, x in enumerate(f):
        for j, y in enumerate(g):
            result[i + j] += x * y
    return trim(result)


def divide(f, g):
    f, g = trim(f), trim(g)
    assert g != (0,)
    quotient = [0] * max(1, degree(f) - degree(g) + 1)
    while f != (0,) and degree(f) >= degree(g):
        shift = degree(f) - degree(g)
        coefficient = f[-1] * pow(g[-1], -1, P) % P
        quotient[shift] = coefficient
        f = add(f, (0,) * shift + scale(-coefficient, g))
    return trim(quotient), f


def evaluate(f, x):
    result = 0
    for c in reversed(f):
        result = (result * x + c) % P
    return result


def locator(nodes):
    result = (1,)
    for x in nodes:
        result = multiply(result, (-x, 1))
    return result


def interpolate(nodes, values):
    result = (0,)
    for x in nodes:
        basis = locator(y for y in nodes if y != x)
        result = add(result, scale(values[x] * pow(evaluate(basis, x), -1, P), basis))
    return result


def rank(rows):
    rows = [[x % P for x in row] for row in rows]
    pivot_row = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(pivot_row, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[pivot_row], rows[pivot] = rows[pivot], rows[pivot_row]
        inverse = pow(rows[pivot_row][col], -1, P)
        rows[pivot_row] = [x * inverse % P for x in rows[pivot_row]]
        for i in range(pivot_row + 1, len(rows)):
            coefficient = rows[i][col]
            rows[i] = [(x - coefficient * y) % P
                       for x, y in zip(rows[i], rows[pivot_row])]
        pivot_row += 1
        if pivot_row == len(rows):
            break
    return pivot_row


def main():
    nodes = tuple(x for x in OMEGA if x != A_NODE)
    n, error_budget = len(nodes), len(nodes) - AGREEMENT
    assert all(pow(x, len(OMEGA), P) == 1 for x in OMEGA)
    assert len(set(OMEGA)) == len(OMEGA)
    values = {x: {2: 1, 15: 11}.get(x, 0) for x in nodes}
    domain_locator = locator(nodes)
    received_polynomial = interpolate(nodes, values)
    assert degree(received_polynomial) < n
    assert all(evaluate(received_polynomial, x) == values[x] for x in nodes)

    def remainder(lam):
        return divide(multiply(lam, received_polynomial), domain_locator)[1]

    listing = []
    for coefficients in product(range(P), repeat=K):
        if sum(evaluate(coefficients, x) == values[x] for x in nodes) >= AGREEMENT:
            listing.append(trim(coefficients))
    assert set(listing) == {(0,), (3, 3, 5, 5), (8, 8, 8, 8)}
    actual_values = {evaluate(f, A_NODE) for f in listing}
    assert actual_values == {0, 15, 16}

    exact_values, exact_locators, exact_decodings = set(), set(), set()
    divisor_checks = 0
    for errors in combinations(nodes, error_budget):
        lam = locator(errors)
        assert divide(domain_locator, lam)[1] == (0,)
        rem = remainder(lam)
        if degree(rem) < K + error_budget:
            f, residual = divide(rem, lam)
            assert residual == (0,) and degree(f) < K
            assert all(evaluate(f, x) == values[x] for x in nodes if x not in errors)
            gamma = evaluate(rem, A_NODE) * pow(evaluate(lam, A_NODE), -1, P) % P
            assert gamma == evaluate(f, A_NODE)
            exact_values.add(gamma)
            exact_locators.add(lam)
            exact_decodings.add(f)
        divisor_checks += 1
    assert exact_values == actual_values
    assert exact_decodings == set(listing)
    assert exact_locators == {trim((-c, 0, 1)) for c in (4, 16, 13)}

    constraint_columns = []
    for i in range(error_budget + 1):
        rem = remainder((0,) * i + (1,))
        constraint_columns.append([rem[j] if j < len(rem) else 0
                                   for j in range(K + error_budget, n)])
    constraint_matrix = [list(row) for row in zip(*constraint_columns)]
    constraint_rank = rank(constraint_matrix)
    assert constraint_rank == 1
    assert degree(remainder((1,))) < K + error_budget
    assert degree(remainder((0, 0, 1))) < K + error_budget

    relaxed_values, monic_kernel = set(), []
    for coefficients in product(range(P), repeat=error_budget):
        lam = coefficients + (1,)
        rem = remainder(lam)
        if degree(rem) >= K + error_budget:
            continue
        monic_kernel.append(lam)
        denominator = evaluate(lam, A_NODE)
        if denominator:
            relaxed_values.add(evaluate(rem, A_NODE) * pow(denominator, -1, P) % P)
    assert set(monic_kernel) == {trim((-c, 0, 1)) for c in range(P)}
    assert len(relaxed_values) == P - 1 > len(OMEGA)
    assert actual_values <= relaxed_values

    u0 = {**values, A_NODE: 0}
    u1 = {x: int(x == A_NODE) for x in OMEGA}
    original_bad, support_checks = set(), 0
    for size in range(AGREEMENT + 1, len(OMEGA) + 1):
        for support in combinations(OMEGA, size):
            matrix = [[pow(x, j, P) for j in range(K)] for x in support]
            assert rank(matrix) == K
            no_joint = rank([row + [u0[x], u1[x]]
                             for row, x in zip(matrix, support)]) > K
            for gamma in range(P):
                decodes = rank([row + [(u0[x] + gamma * u1[x]) % P]
                                for row, x in zip(matrix, support)]) == K
                if no_joint and decodes:
                    original_bad.add(gamma)
                support_checks += 1
    assert original_bad == actual_values
    assert support_checks == 629 and divisor_checks == 21

    b = 178956971
    assert 6 * b - 2 == 2**30
    assert (6*b-3) - (3*b-1) - (2*b-2) == b
    assert (2*b-2) + 1 - b == b - 1
    assert (3*b-2) + 2*(b+1) + (b-3) == 6*b-3
    assert (3*b-2) + (b+1) == 4*b-1
    assert (b+1) + (b-3) == 2*b-2

    print(json.dumps({
        "status": "PASS_EXACT_LOCATOR_AND_LINEAR_RELAXATION_CONTROL",
        "field": P, "domain": OMEGA, "omitted_node": A_NODE,
        "code_dimension": K, "punctured_agreement": AGREEMENT,
        "polynomials_enumerated": P**K, "divisor_locators_checked": divisor_checks,
        "monic_polynomials_checked": P**error_budget,
        "linear_constraint_rank": constraint_rank, "monic_kernel_size": len(monic_kernel),
        "actual_bad_values": sorted(actual_values),
        "relaxed_value_count": len(relaxed_values),
        "same_support_scalar_rank_checks": support_checks,
        "production_counterexample_claim": False, "universal_scalar_bound_claim": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
