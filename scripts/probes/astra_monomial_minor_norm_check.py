#!/usr/bin/env python3
"""Exact n=16 monomial-minor norms; no claim at production length."""
import json
from collections import Counter
from functools import lru_cache
from itertools import combinations
from math import comb

P = 365375409332725729550921208179070755120141565953
N, K = 16, 8


def shift(coefficients, exponent):
    """Multiply in Z[zeta_16], represented modulo Z^8+1."""
    out = [0]*K
    for i, value in enumerate(coefficients):
        degree = (i+exponent) % N
        out[degree % K] += value if degree < K else -value
    return out


def locator(exponents):
    out = [[1]+[0]*(K-1)]
    for exponent in exponents:
        new = [[0]*K for _ in range(len(out)+1)]
        for i, coefficient in enumerate(out):
            shifted = shift(coefficient, exponent)
            for j in range(K):
                new[i][j] -= shifted[j]
                new[i+1][j] += coefficient[j]
        out = new
    return out


@lru_cache(None)
def tower_norm(a):
    """Successive relative norms under zeta -> -zeta."""
    d = len(a)
    if d == 1:
        return a[0]
    product = [0]*d
    for i, x in enumerate(a):
        for j, y in enumerate(a):
            value = x*y*(-1 if j % 2 else 1)
            degree = i+j
            product[degree % d] += value if degree < d else -value
    assert all(product[j] == 0 for j in range(1, d, 2))
    return tower_norm(tuple(product[::2]))


def determinant(matrix):
    """Independent fraction-free determinant of the multiplication matrix."""
    a = [row[:] for row in matrix]
    sign, previous = 1, 1
    for k in range(len(a)-1):
        pivot = next((i for i in range(k, len(a)) if a[i][k]), None)
        if pivot is None:
            return 0
        if pivot != k:
            a[k], a[pivot] = a[pivot], a[k]
            sign = -sign
        value = a[k][k]
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                numerator = value*a[i][j]-a[i][k]*a[k][j]
                assert numerator % previous == 0
                a[i][j] = numerator//previous
            a[i][k] = 0
        previous = value
    return sign*a[-1][-1]


def prime_factors(number):
    out, divisor = [], 2
    while divisor*divisor <= number:
        if number % divisor == 0:
            out.append(divisor)
            while number % divisor == 0:
                number //= divisor
        divisor += 1
    if number > 1:
        out.append(number)
    return out


def primitive_root(p):
    assert (p-1) % N == 0
    root = next(value for base in range(2, 100)
                if (value := pow(base, (p-1)//N, p)) and pow(value, K, p) != 1)
    assert pow(root, N, p) == 1
    return root


def evaluate(poly, x, p):
    value = 0
    for coefficient in reversed(poly):
        value = (value*x+coefficient) % p
    return value


def finite_locator(nodes, p):
    out = [1]
    for x in nodes:
        new = [0]*(len(out)+1)
        for i, value in enumerate(out):
            new[i] = (new[i]-x*value) % p
            new[i+1] = (new[i+1]+value) % p
        out = new
    return out


def remainder(poly, monic, p):
    out = poly[:]
    for degree in range(len(out)-1, len(monic)-2, -1):
        scale, offset = out[degree], degree-len(monic)+1
        for j, coefficient in enumerate(monic):
            out[offset+j] = (out[offset+j]-scale*coefficient) % p
    return out[:len(monic)-1]


def witness(p, exponents, j):
    omega = primitive_root(p)
    agreement = [e for e in range(N) if e not in exponents]
    h = finite_locator([pow(omega, e, p) for e in agreement], p)
    d = K+j
    f = remainder([0]*d+[1], h, p)
    assert f[K] == 0
    f = f[:K]
    actual = [e for e in range(N)
              if evaluate(f, pow(omega, e, p), p) == pow(omega, d*e, p)]
    assert len(actual) >= K+1
    return {"p": p, "omega": omega, "monomial_degree": d,
            "complement_exponents": list(exponents), "polynomial": f,
            "actual_agreement_exponents": actual}


def main():
    histogram, representatives, exceptional = Counter(), {}, set()
    primes = (17, 97, P)
    roots = {p: primitive_root(p) for p in primes}
    zeros = {p: Counter() for p in primes}
    witnesses = {}
    count = 0
    for exponents in combinations(range(N), K-1):
        count += 1
        coefficients = locator(exponents)
        for j in range(K):
            coefficient = coefficients[K-1-j]
            # Reduction zeta -> 1 modulo 2 gives an odd binomial coefficient.
            assert sum(coefficient) % 2 == comb(K-1, j) % 2 == 1
            norm = tower_norm(tuple(coefficient))
            assert norm > 0 and norm % 2 == 1
            histogram[norm] += 1
            representatives.setdefault(norm, coefficient)
            for p in primes:
                value = evaluate(coefficient, roots[p], p)
                if not value:
                    assert norm % p == 0
                    zeros[p][K+j] += 1
                    witnesses.setdefault(p, (exponents, j))
            # Independent division checks at a bounded sample of subsets.
            if count <= 16:
                h = finite_locator([pow(roots[P], e, P) for e in range(N)
                                    if e not in exponents], P)
                rem = remainder([0]*(K+j)+[1], h, P)
                assert rem[K] == evaluate(coefficient, roots[P], P)
    for norm, coefficient in representatives.items():
        columns = [shift(coefficient, j) for j in range(K)]
        matrix = [[columns[j][i] for j in range(K)] for i in range(K)]
        assert determinant(matrix) == norm
        exceptional.update(prime_factors(norm))
    assert count == comb(N, K-1) == 11440
    assert sum(histogram.values()) == 91520
    assert len(histogram) == 50 and max(histogram) == 66049
    assert max(exceptional) == 9601
    assert not zeros[P] and zeros[17] and zeros[97]
    assert P > 35**8 and P < comb(15, 7)**16
    # The general norm-bound gate fails at production without forming a
    # binomial coefficient containing hundreds of millions of digits.
    assert (2**29-1) >= 7 and 2**29 >= 64 and 7**64 > P
    print(json.dumps({"status": "PASS_N16_MONOMIAL_MINOR_CERTIFICATE",
                      "n": N, "coefficient_norm_checks": sum(histogram.values()),
                      "independent_multiplication_determinants": len(histogram),
                      "independent_remainder_checks": 16*K,
                      "norm_histogram": sorted(histogram.items()),
                      "exceptional_characteristics": sorted(exceptional),
                      "exceptional_prime_fields_1_mod_16": sorted(p for p in exceptional if p % 16 == 1),
                      "finite_field_zero_coefficient_counts": {p: dict(c) for p, c in zeros.items()},
                      "small_characteristic_witnesses": [witness(p, *witnesses[p]) for p in (17, 97)],
                      "production_prime_length16_monomial_agreement_cap": K,
                      "general_norm_bound_passes_at_length32": False,
                      "production_length_monomial_bound_proved": False,
                      "grand_prize_solved": False, "Lean_formalized": False}, sort_keys=True))


if __name__ == "__main__":
    main()
