#!/usr/bin/env python3
"""Explicit nonmonomial counterexample to extending the monomial maximum nine.

On the order-eight domain this constructs ten distinct threshold-four MCA
scalars uniformly for primes p = 1 mod 8 outside {17,97,337,641}. The proof
uses explicit witnesses and exact integer collision certificates. This is
not a claim that ten is the arbitrary-pencil maximum, or a prize solution.
"""

from fractions import Fraction
from itertools import combinations

from g328_k2_field_stability_boundary import order_eight_generator, primes_one_mod_eight


RATIONAL_SCALARS = (Fraction(-3, 2), Fraction(-2), Fraction(-5, 2), Fraction(-4, 3))
COLLISION_FACTORS = ((13, 97), (5, 17), (29, 641), (5, 5, 337))
EXCEPTIONAL_PRIMES = {17, 97, 337, 641}


def rational_mod(value, p):
    return value.numerator * pow(value.denominator, -1, p) % p


def construction(p):
    g = order_eight_generator(p)
    domain = [pow(g, i, p) for i in range(8)]
    first = [3, 0, 0, 0, 5, 1, 1, 1]
    second = [2, 0, 0, 0, 2, domain[5], domain[6], domain[7]]
    return domain, first, second


def is_affine(domain, word, support, p):
    i, j = support[:2]
    slope = (word[j] - word[i]) * pow(domain[j] - domain[i], -1, p) % p
    return all((word[t] - word[i] - slope * (domain[t] - domain[i])) % p == 0
               for t in support)


def explicit_witnesses(p):
    domain, first, second = construction(p)
    a, b = (1, 2, 3), (5, 6, 7)
    witnesses = []
    for index in b:
        gamma = -pow(domain[index], -1, p) % p
        witnesses.append((gamma, 0, 0, a + (index,)))
    for index in a:
        gamma = -pow(domain[index], -1, p) % p
        witnesses.append((gamma, 1, gamma, b + (index,)))
    for gamma, intercept, support in (
        (RATIONAL_SCALARS[0], 0, a + (0,)),
        (RATIONAL_SCALARS[1], 1, b + (0,)),
        (RATIONAL_SCALARS[2], 0, a + (4,)),
        (RATIONAL_SCALARS[3], 1, b + (4,)),
    ):
        scalar = rational_mod(gamma, p)
        witnesses.append((scalar, intercept, scalar if intercept else 0, support))
    for gamma, intercept, slope, support in witnesses:
        assert len(set(support)) == 4
        assert all((first[i] + gamma * second[i] - intercept - slope * domain[i]) % p == 0
                   for i in support)
        assert not is_affine(domain, first, support, p)
    scalars = {w[0] for w in witnesses}
    assert len(scalars) == (9 if p in EXCEPTIONAL_PRIMES else 10)
    return scalars, witnesses


def exhaustive_affine_check(p):
    """Original event, exhaustively over all p scalars and p^2 affine codewords."""
    domain, first, second = construction(p)
    bad = set()
    for gamma in range(p):
        for intercept in range(p):
            for slope in range(p):
                support = tuple(i for i in range(8)
                                if (first[i] + gamma * second[i] - intercept
                                    - slope * domain[i]) % p == 0)
                if len(support) >= 4 and not (
                    is_affine(domain, first, support, p)
                    and is_affine(domain, second, support, p)
                ):
                    bad.add(gamma)
    return bad


def integer_collision_certificate():
    """Check explicit rational scalars avoid the six non-real eighth roots."""
    root_collision_primes = set()
    values = []
    for value, factors in zip(RATIONAL_SCALARS, COLLISION_FACTORS):
        a, b = value.numerator, value.denominator
        numerator = a**6 + a**4 * b**2 + a**2 * b**4 + b**6
        product = 1
        for prime in factors:
            assert prime > 1 and all(prime % d for d in range(2, prime))
            product *= prime
            root_collision_primes.add(prime)
        assert numerator == product
        values.append(numerator)
    assert values == [1261, 85, 18589, 8425]
    differences = [(a - b).numerator for a, b in combinations(RATIONAL_SCALARS, 2)]
    assert differences == [1, 1, -1, 1, -2, -7]
    assert {p for p in root_collision_primes | {2, 3, 7} if p % 8 == 1} == EXCEPTIONAL_PRIMES
    return values


def main():
    values = integer_collision_certificate()
    primes = primes_one_mod_eight(2000)
    for prime in primes:
        explicit_witnesses(prime)
    # Independent exhaustive search; these runs are checks, not the uniform proof.
    for prime in (17, 41, 73):
        expected, _ = explicit_witnesses(prime)
        actual = exhaustive_affine_check(prime)
        assert actual == expected, (prime, expected, actual)
    large_prime = 111 * 2**128 + 1
    assert 111 < 2**128 and pow(5, (large_prime - 1) // 2, large_prime) == large_prime - 1
    explicit_witnesses(large_prime)
    print(f"Rational/root collision numerators: {values}")
    print(f"Excluded primes congruent to 1 modulo 8: {sorted(EXCEPTIONAL_PRIMES)}")
    print(f"Explicit witness checks: all {len(primes)} primes =1 mod8 up to2000 PASS")
    print("Independent exhaustive gamma/affine-codeword checks: p=17,41,73 PASS")
    print("Ten witnesses at Proth-certified prime 111*2^128+1 PASS")
    scalars, witnesses = explicit_witnesses(41)
    print(f"F41 bad scalars: {sorted(scalars)}")
    for gamma, intercept, slope, support in sorted(witnesses):
        print(f" gamma={gamma:2d}, affine={intercept}+{slope}*X, support_indices={support}")
    print("PASS: a field-uniform nonmonomial lower bound of10 beats the monomial maximum9.")
    print("Scope: explicit n=8 family, not a worst-case upper bound or a production threshold.")


if __name__ == "__main__":
    main()
