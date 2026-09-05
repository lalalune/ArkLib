#!/usr/bin/env python3
"""Exact F17 single-hole control; no production or universal count claim."""

from itertools import combinations, product
import json
from math import prod


P = 17
OMEGA = (1, 2, 4, 8, 16, 15, 13, 9)
K, T, A = 4, 6, 1


def evaluate(coefficients, x):
    value = 0
    for c in reversed(coefficients):
        value = (value * x + c) % P
    return value


def rank(rows):
    rows = [[v % P for v in row] for row in rows]
    pivot_row = 0
    for col in range(len(rows[0])):
        pivot = next((i for i in range(pivot_row, len(rows)) if rows[i][col]), None)
        if pivot is None:
            continue
        rows[pivot_row], rows[pivot] = rows[pivot], rows[pivot_row]
        inverse = pow(rows[pivot_row][col], -1, P)
        rows[pivot_row] = [v * inverse % P for v in rows[pivot_row]]
        for i in range(pivot_row + 1, len(rows)):
            multiplier = rows[i][col]
            rows[i] = [(x - multiplier * y) % P
                       for x, y in zip(rows[i], rows[pivot_row])]
        pivot_row += 1
        if pivot_row == len(rows):
            break
    return pivot_row


def nonsubgroup_rank_three_control():
    omega = (0, 1, 16, 2, 15, 3, 14, 4)
    a = 4
    u0 = {x: {1: 7, 16: 10}.get(x, 0) for x in omega}
    expected = [(0, 0, 0, 0), (0, 10, 0, 14), (0, 15, 0, 9)]
    candidates = [f for f in product(range(P), repeat=K)
                  if sum(evaluate(f, x) == u0[x] for x in omega if x != a) >= T - 1]
    assert candidates == expected
    values = [evaluate(f, a) for f in candidates]
    assert values == [0, 1, 7]
    weights = {x: pow(prod(x - y for y in omega if y != x) % P, -1, P)
               for x in omega}
    assert [weights[x] for x in omega] == [15, 2, 8, 9, 3, 14, 2, 15]
    for d in range(2 * K - 1):
        assert sum(weights[x] * pow(x, d, P) for x in omega) % P == 0
    errors = []
    for f, gamma in zip(candidates, values):
        error = {x: (u0[x] + gamma * int(x == a) - evaluate(f, x)) % P
                 for x in omega}
        support = [x for x in omega if not error[x]]
        assert len(support) == T
        rows = [[pow(x, j, P) for j in range(K)] + [u0[x], int(x == a)]
                for x in support]
        assert rank(rows) > K  # Original same-support no-joint clause.
        errors.append(error)
    gram = [[sum(weights[x] * f[x] * g[x] for x in omega) % P
             for g in errors] for f in errors]
    assert gram == [[14, 0, 0], [0, 5, 0], [0, 0, 16]]
    assert rank(gram) == 3
    return {"omega": omega, "omitted_point": a, "list_polynomials": candidates,
            "actual_bad_scalars": sorted(values), "lagrange_weights": [weights[x] for x in omega],
            "error_gram": gram, "gram_rank": 3, "polynomials_enumerated": P ** K}


def main():
    f1 = (4, 5, 3, 1)
    zeros = {2, 4, 8, 16, 15}
    u0 = {x: 0 if x == A or x in zeros else evaluate(f1, x) for x in OMEGA}
    u1 = {x: int(x == A) for x in OMEGA}
    punctured_list = []
    for f in product(range(P), repeat=K):
        support = [x for x in OMEGA if x != A and evaluate(f, x) == u0[x]]
        if len(support) >= T - 1:
            punctured_list.append((f, evaluate(f, A), support))
    assert [r[0] for r in punctured_list] == [(0, 0, 0, 0), f1]
    values = {r[1] for r in punctured_list}
    assert values == {0, 13}

    # Independently use the original same-support rank conditions, including
    # every support size >= T rather than assuming reduction to size T.
    bad = set()
    rank_checks = 0
    for size in range(T, len(OMEGA) + 1):
        for support in combinations(OMEGA, size):
            vandermonde = [[pow(x, j, P) for j in range(K)] for x in support]
            assert rank(vandermonde) == K
            joint = [row + [u0[x], u1[x]] for row, x in zip(vandermonde, support)]
            no_joint = rank(joint) > K
            for gamma in range(P):
                scalar = [row + [(u0[x] + gamma * u1[x]) % P]
                          for row, x in zip(vandermonde, support)]
                if no_joint and rank(scalar) == K:
                    bad.add(gamma)
                rank_checks += 1
    assert bad == values
    full = [[pow(x, j, P) for j in range(K)] + [u0[x], u1[x]] for x in OMEGA]
    assert rank(full) == K + 2

    # Verify the weighted Gram identity independently on the resulting errors.
    def pairing(v, w):
        return sum(x * v[x] * w[x] for x in OMEGA) % P

    words = [{x: evaluate(f, x) for x in OMEGA} for f, _, _ in punctured_list]
    errors = [{x: (u0[x] + gamma * u1[x] - word[x]) % P for x in OMEGA}
              for word, (_, gamma, _) in zip(words, punctured_list)]
    for i, (_, gamma, _) in enumerate(punctured_list):
        assert errors[i][A] == 0
        for j, (_, eta, _) in enumerate(punctured_list):
            expected = (pairing(u0, u0) - pairing(u0, words[i])
                        - pairing(u0, words[j]) - A * gamma * eta) % P
            assert pairing(errors[i], errors[j]) == expected

    print(json.dumps({
        "status": "PASS_EXACT_SINGLE_HOLE_CONTROL",
        "field": P, "n": len(OMEGA), "k": K, "agreement": T,
        "polynomials_enumerated": P ** K,
        "same_support_scalar_rank_checks": rank_checks,
        "punctured_list": punctured_list, "actual_bad_scalars": sorted(bad),
        "quotient_rank": 2, "gram_identity_checked": True,
        "nonsubgroup_rank_three_control": nonsubgroup_rank_three_control(),
        "production_claim": False, "universal_count_claim": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
