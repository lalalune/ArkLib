#!/usr/bin/env python3
"""Exact production-parameter obstructions to two simple OrbitPencil refinements.

At F=256,r=136 and the literal KoalaBear prime, even the maximal product
class s=4 has no forced affine identity among its six top coefficients (or
six power sums). An extra evaluation key V_U(1) is not confined to any
proper multiplicative coset. These are support obstructions, NOT bounds on
nonlinear concentration or on the largest joint key fibre.
"""

from itertools import permutations
from math import isqrt, prod


P = 2130706433
F = 256
Z = 392596362
COMMON = {3, 4, *range(6, 137), 165}
BASE = COMMON | {1, 2}
TRADES = (
    ((1, 2), (5, 254)),
    ((1, 3), (5, 255)),
    ((1, 18), (137, 138)),
    ((1, 19), (137, 139)),
    ((1, 20), (137, 140)),
    ((1, 21), (137, 141)),
)


def elementary_key(subset, roots):
    e = [1, 0, 0, 0, 0, 0, 0]
    for index in sorted(subset):
        for degree in range(6, 0, -1):
            e[degree] = (e[degree] + roots[index] * e[degree - 1]) % P
    return e[1:]


def power_key(subset, roots):
    return [sum(pow(roots[index], degree, P) for index in subset) % P for degree in range(1, 7)]


def determinant_elimination(matrix):
    a = [row[:] for row in matrix]
    answer = 1
    for column in range(6):
        pivot = next((row for row in range(column, 6) if a[row][column]), None)
        if pivot is None:
            return 0
        if pivot != column:
            a[pivot], a[column] = a[column], a[pivot]
            answer = -answer
        value = a[column][column]
        answer = answer * value % P
        inverse = pow(value, -1, P)
        for row in range(column + 1, 6):
            multiple = a[row][column] * inverse % P
            for j in range(column, 6):
                a[row][j] = (a[row][j] - multiple * a[column][j]) % P
    return answer % P


def determinant_permutations(matrix):
    answer = 0
    for permutation in permutations(range(6)):
        inversions = sum(permutation[i] > permutation[j] for i in range(6) for j in range(i + 1, 6))
        answer += (-1) ** inversions * prod(matrix[i][permutation[i]] for i in range(6))
    return answer % P


def main():
    assert all(P % divisor for divisor in range(2, isqrt(P) + 1))
    assert P - 1 == 127 * 2**24
    assert Z == pow(3, (P - 1) // F, P)
    assert pow(Z, F, P) == 1 and pow(Z, F // 2, P) == P - 1
    roots = [pow(Z, index, P) for index in range(F)]
    assert len(COMMON) == 134 and sum(COMMON) % F == 1
    subsets = [BASE]
    for removed, inserted in TRADES:
        assert set(removed) <= BASE and not set(inserted) & BASE
        assert sum(removed) % F == sum(inserted) % F
        subsets.append((BASE - set(removed)) | set(inserted))
    assert all(len(s) == 136 and 0 not in s and sum(s) % F == 4 for s in subsets)
    for key, expected in ((elementary_key, 626613800), (power_key, 1105802634)):
        vectors = [key(subset, roots) for subset in subsets]
        matrix = [[(x - y) % P for x, y in zip(row, vectors[0])] for row in vectors[1:]]
        first, second = determinant_elimination(matrix), determinant_permutations(matrix)
        assert first == second == expected != 0
        print(f"{key.__name__}: affine rank6; determinant={first}; two algorithms agree")
    values = [prod((1 - roots[index]) % P for index in subset) % P for subset in subsets[:2]]
    assert all(values)
    ratio = values[0] * pow(values[1], -1, P) % P
    cancelled_ratio = ((1 - roots[1]) * (1 - roots[2])
                       * pow((1 - roots[5]) * (1 - roots[254]) % P, -1, P)) % P
    assert ratio == cancelled_ratio == 343834042
    assert pow(ratio, P - 1, P) == 1
    assert pow(ratio, (P - 1) // 2, P) == P - 1
    assert pow(ratio, (P - 1) // 127, P) == 359646889 != 1
    print(f"Same product-class evaluation ratio={ratio}, exact multiplicative order={P-1}")
    print(f"Explicit common set: {{3,4,6,...,136,165}}; trades={TRADES}")
    print("PASS: no forced affine top/power-sum identity; no proper-coset restriction on V_U(1)")
    print("Scope: these do not rule out nonlinear key constraints, concentration, or another construction.")


if __name__ == "__main__":
    main()
