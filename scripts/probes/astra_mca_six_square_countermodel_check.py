#!/usr/bin/env python3
"""Exact six-square b=3 countermodel; no MCA or production witness claim.

Standard library only. Polynomial arrays are constant coefficient first.
Sylvester determinants are computed in F_11[S,T], with fixed X-degree 3;
no search, interpolation, external CAS, or input data file is used.
"""

import itertools
import json
import math


P = 11
B = [[3, 8, 10, 1], [9, 1], [6, 9, 8, 1]]
C = [[8, 3, 5, 6], [0, 0, 1, 5], [7, 5, 5, 2]]
POINTS = [[1, 0, 0], [1, 5, 5], [1, 7, 10],
          [1, 9, 4], [0, 1, 0], [0, 0, 1]]
EXPECTED_W = [[8, 8, 0, 6, 4, 3, 6],
              [5, 8, 7, 10, 4, 6, 4],
              [5, 9, 10, 8, 0, 7, 5]]
EXPECTED_LOCATORS = [EXPECTED_W[0], [3, 5, 8, 8, 2, 2, 7],
                     [5, 0, 6, 2, 10, 5, 7], [7, 6, 4, 7, 7, 8, 7],
                     EXPECTED_W[1], EXPECTED_W[2]]
SCALARS = [9, 10, 2, 6, 1, 10]
SQUARE_ROOTS = [[3, 9, 9, 1], [3, 5, 10, 1], [9, 0, 6, 1],
                [6, 2, 1, 1], [3, 8, 0, 1], [9, 2, 7, 1]]
LOCATOR_FACTOR_DEGREES = [[1, 1, 4], [6], [6], [2, 4],
                          [1, 1, 2, 2], [1, 1, 4]]
ROOT_FACTOR_DEGREES = [[1, 2], [3], [3], [1, 2], [1, 2], [1, 2]]


def trim(a):
    a = [x % P for x in a]
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def add(a, b, scale=1):
    return trim([(a[i] if i < len(a) else 0) + scale *
                 (b[i] if i < len(b) else 0)
                 for i in range(max(len(a), len(b)))])


def mul(a, b):
    result = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            result[i + j] = (result[i + j] + x * y) % P
    return trim(result)


def divmod_poly(a, b):
    a, b = trim(a), trim(b)
    if b == [0]:
        raise ZeroDivisionError("zero polynomial")
    quotient = [0] * max(1, len(a) - len(b) + 1)
    inverse = pow(b[-1], -1, P)
    while a != [0] and len(a) >= len(b):
        shift, factor = len(a) - len(b), a[-1] * inverse % P
        quotient[shift] = factor
        for j, x in enumerate(b):
            a[shift + j] = (a[shift + j] - factor * x) % P
        a = trim(a)
    return trim(quotient), a


def monic(a):
    a = trim(a)
    return trim([x * pow(a[-1], -1, P) for x in a]) if a != [0] else a


def gcd(a, b):
    a, b = trim(a), trim(b)
    while b != [0]:
        a, b = b, divmod_poly(a, b)[1]
    return monic(a)


def derivative(a):
    return trim([i * a[i] for i in range(1, len(a))] or [0])


def powmod(a, exponent, modulus):
    result = [1]
    while exponent:
        if exponent & 1:
            result = divmod_poly(mul(result, a), modulus)[1]
        a = divmod_poly(mul(a, a), modulus)[1]
        exponent >>= 1
    return result


def factor_degrees(f):
    """Recover irreducible degrees from exact Frobenius-gcd degrees.

    For squarefree f, deg gcd(f, X^(P^d)-X) is the sum of the degrees
    of its irreducible factors whose degrees divide d.
    """
    assert gcd(f, derivative(f)) == [1]
    x, frobenius, counts, degrees = [0, 1], [0, 1], {}, []
    for d in range(1, len(f)):
        frobenius = powmod(frobenius, P, f)
        total = len(gcd(f, add(frobenius, x, -1))) - 1
        new = total - sum(e * n for e, n in counts.items() if d % e == 0)
        assert new >= 0 and new % d == 0
        counts[d] = new // d
        degrees.extend([d] * counts[d])
    assert sum(degrees) == len(f) - 1
    return degrees


def combination(row, polys):
    result = [0]
    for coefficient, polynomial in zip(row, polys):
        result = add(result, polynomial, coefficient)
    return result


def determinant(matrix):
    matrix = [row[:] for row in matrix]
    result = 1
    for j in range(len(matrix)):
        pivot = next((i for i in range(j, len(matrix)) if matrix[i][j] % P), None)
        if pivot is None:
            return 0
        if pivot != j:
            matrix[pivot], matrix[j] = matrix[j], matrix[pivot]
            result = -result % P
        value = matrix[j][j] % P
        result = result * value % P
        for i in range(j + 1, len(matrix)):
            factor = matrix[i][j] * pow(value, -1, P) % P
            matrix[i] = [(x - factor * y) % P
                         for x, y in zip(matrix[i], matrix[j])]
    return result


def homogeneous_mul(a, b):
    """Bivariate polynomials keyed by (S exponent, T exponent)."""
    result = {}
    for (s, t), x in a.items():
        for (u, v), y in b.items():
            key = (s + u, t + v)
            result[key] = (result.get(key, 0) + x * y) % P
    return {key: value for key, value in result.items() if value}


def homogeneous_determinant(matrix):
    """Direct Leibniz formula in F_11[S,T], without specialization."""
    result = {}
    for perm in itertools.permutations(range(len(matrix))):
        inversions = sum(perm[i] > perm[j] for i in range(len(perm))
                         for j in range(i + 1, len(perm)))
        product = {(0, 0): (-1) ** inversions % P}
        for i, j in enumerate(perm):
            product = homogeneous_mul(product, matrix[i][j])
        for key, value in product.items():
            result[key] = (result.get(key, 0) + value) % P
    return {key: value for key, value in result.items() if value}


def resultant(ci):
    pivot = next(i for i, c in enumerate(ci) if c)
    projected = []
    for j in range(3):
        if j == pivot:
            continue
        factor = -ci[j] * pow(ci[pivot], -1, P) % P
        projected.append((add(B[j], B[pivot], factor),
                          add(C[j], C[pivot], factor)))
    rows = []
    for b, c in projected:
        coefficients = []
        # Fixed homogeneous X-degree 3, even if a leading coefficient vanishes.
        for degree in range(3, -1, -1):
            entry = {(1, 0): -(b[degree] if degree < len(b) else 0) % P,
                     (0, 1): (c[degree] if degree < len(c) else 0) % P}
            coefficients.append({key: value for key, value in entry.items() if value})
        for shift in range(3):
            rows.append([{}] * shift + coefficients + [{}] * (2 - shift))
    result = homogeneous_determinant(rows)
    assert result and all(s + t == 6 for s, t in result)
    return [result.get((s, 6 - s), 0) for s in range(7)]


def main():
    w = [add(mul(B[j], C[k]), mul(B[k], C[j]), -1)
         for j, k in ((1, 2), (2, 0), (0, 1))]
    assert w == EXPECTED_W
    assert gcd(gcd(w[0], w[1]), w[2]) == [1]
    infinity = [f[6] for f in w]
    assert infinity == [6, 4, 5]  # Homogeneous B,C independent at infinity.
    assert len({tuple(ci) for ci in POINTS}) == 6
    assert determinant([POINTS[i] for i in (0, 4, 5)]) == 1

    cases, locators, all_degrees = [], [], []
    for i, (ci, scalar, root) in enumerate(zip(POINTS, SCALARS, SQUARE_ROOTS)):
        locator = combination(ci, w)
        assert locator == EXPECTED_LOCATORS[i] and len(locator) == 7
        assert gcd(locator, derivative(locator)) == [1]
        assert len(root) == 4 and root[-1] == 1
        assert gcd(root, derivative(root)) == [1]
        actual = resultant(ci)
        assert actual == [scalar * a % P for a in mul(root, root)]
        assert actual[6] == scalar != 0  # No parameter root at infinity.
        ld, rd = factor_degrees(locator), factor_degrees(root)
        assert ld == LOCATOR_FACTOR_DEGREES[i]
        assert rd == ROOT_FACTOR_DEGREES[i]
        for f in (locator, root):
            assert powmod([0, 1], P ** 12, f) == [0, 1]
        all_degrees.extend(ld + rd)
        locators.append(locator)
        cases.append({"index": i, "ci": ci, "locator": locator,
                      "resultant_S_ascending": actual, "square_scalar": scalar,
                      "square_root_S_ascending": root,
                      "locator_irreducible_degrees": ld,
                      "square_root_irreducible_degrees": rd})

    for a, b in itertools.combinations(SQUARE_ROOTS, 2):
        assert gcd(a, b) == [1]
    assert math.lcm(*all_degrees) == 12

    products = [mul(w[i], w[j]) for i in range(3) for j in range(i, 3)]
    minor = [[f[d] for f in products] for d in range(6)]
    assert determinant(minor) == 7

    expected_pair_gcds = {(0, 4): [8, 1], (0, 5): [9, 1], (4, 5): [10, 1]}
    pair_gcds = []
    for i, j in itertools.combinations(range(6), 2):
        common = gcd(locators[i], locators[j])
        assert common == expected_pair_gcds.get((i, j), [1])
        if common != [1]:
            pair_gcds.append({"indices": [i, j], "gcd": common})
    lcm = [1]
    for locator in locators:
        quotient, remainder = divmod_poly(locator, gcd(lcm, locator))
        assert remainder == [0]
        lcm = monic(mul(lcm, quotient))
    assert len(lcm) - 1 == 33
    assert gcd(lcm, derivative(lcm)) == [1]
    assert determinant([POINTS[i] for i in (1, 2, 3)]) == 0
    assert [(POINTS[1][j] - 2 * POINTS[2][j] + POINTS[3][j]) % P
            for j in range(3)] == [0, 0, 0]
    assert gcd(gcd(locators[1], locators[2]), locators[3]) == [1]

    print(json.dumps({
        "status": "PASS_SIX_SQUARE_B3_COUNTERMODEL", "field": P, "b": 3,
        "B": B, "C": C, "w": w, "cases": cases,
        "symbolic_homogeneous_sylvester_determinants": 6,
        "finite_coordinate_gcd": [1], "w_at_infinity": infinity,
        "quadratic_product_minor": {"rows": list(range(6)), "matrix": minor,
                                    "determinant": 7},
        "minimal_common_splitting_extension_degree": 12,
        "square_roots_pairwise_coprime": True, "distinct_scalar_parameters": 18,
        "nontrivial_locator_pair_gcds": pair_gcds,
        "locator_union_degree": 33, "required_domain_size_6b_minus_2": 16,
        "collinear_triple": [1, 2, 3], "collinear_triple_locator_gcd": [1],
        "geometric_argument": "balanced kernel implies cover degree divides 3; "
                              "nonconic minor excludes degree 3, hence birational",
        "actual_mca_counterexample": False, "production_claim": False,
    }, sort_keys=True))


if __name__ == "__main__":
    main()
