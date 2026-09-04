#!/usr/bin/env python3
"""A field-uniform certificate for the order-eight, threshold-four monomial census.

This is an exact finite certificate over Z[z]/(z^4+1), not a bounded prime
sweep. Every nonzero determinant, chosen denominator, or candidate-separation
element has a power-of-two norm. Consequently the entire 8x8 census survives
specialization to EVERY field of characteristic different from two containing
an element g with g^4=-1. The maximum is nine, at exactly four pencils.

The mathematical completeness/specialization argument is in
docs/kb/proximity-astra-monomial-census-2026-09-04.md. This Python certificate is
not a Lean theorem and does not prove the production Proximity Prize target.

Stdlib only. Run from any working directory with Python 3.10 or later.
"""

from functools import lru_cache
from itertools import combinations, permutations


ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)
GENERATOR = (0, 1, 0, 0)
EXPECTED_PROFILE = (
    (0, 0, 1, 1, 1, 1, 1, 1),
    (0, 0, 1, 1, 1, 1, 1, 1),
    (0, 0, 1, 0, 4, 8, 4, 0),
    (0, 0, 0, 1, 8, 4, 0, 4),
    (0, 0, 5, 9, 1, 8, 5, 9),
    (0, 0, 9, 5, 8, 1, 9, 5),
    (0, 0, 4, 0, 4, 8, 1, 0),
    (0, 0, 0, 4, 8, 4, 0, 1),
)
EXPECTED_MAXIMIZERS = ((4, 3), (4, 7), (5, 2), (5, 6))


def add(a, b):
    return tuple(x + y for x, y in zip(a, b))


def negate(a):
    return tuple(-x for x in a)


def subtract(a, b):
    return add(a, negate(b))


def multiply(a, b):
    """Multiply integer coordinates, reducing only by the monic relation z^4=-1."""
    out = [0] * 4
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[(i + j) % 4] += x * y * (-1 if i + j >= 4 else 1)
    return tuple(out)


def norm_ladder(c):
    """G330's two antipodal-squaring identities, evaluated entirely in integers."""
    c0, c1, c2, c3 = c
    a0 = c0 * c0
    a1 = 2 * c0 * c2 - c1 * c1
    a2 = c2 * c2 - 2 * c1 * c3
    a3 = -c3 * c3
    return a0 * a0 - (2 * a0 * a2 - a1 * a1) + (a2 * a2 - 2 * a1 * a3) + a3 * a3


def norm_matrix(c):
    """Independent norm: permutation determinant of multiplication by c."""
    basis = [tuple(int(i == j) for i in range(4)) for j in range(4)]
    columns = [multiply(c, e) for e in basis]
    total = 0
    for permutation in permutations(range(4)):
        inversions = sum(permutation[i] > permutation[j] for i in range(4) for j in range(i + 1, 4))
        term = (-1) ** inversions
        for row in range(4):
            term *= columns[permutation[row]][row]
        total += term
    return total


@lru_cache(maxsize=None)
def certified_norm(c):
    first, second = norm_ladder(c), norm_matrix(c)
    assert first == second, (c, first, second)
    assert (first == 0) == (c == ZERO), (c, first)
    return abs(first)


def require_two_power(c, bucket):
    assert c != ZERO
    norm = certified_norm(c)
    assert norm > 0 and norm & (norm - 1) == 0, (c, norm)
    bucket.add(norm)


def polynomial_value(coefficients, x):
    value = ZERO
    for coefficient in reversed(coefficients):
        value = add(multiply(value, x), coefficient)
    return value


def four_point_remainders(roots, indices):
    """Return all X^a mod product_(j in indices)(X-z^j), for a=0,...,7."""
    polynomial = [ONE]
    for index in indices:
        out = [ZERO] * (len(polynomial) + 1)
        for degree, coefficient in enumerate(polynomial):
            out[degree] = subtract(out[degree], multiply(coefficient, roots[index]))
            out[degree + 1] = add(out[degree + 1], coefficient)
        polynomial = out
    assert polynomial[4] == ONE
    remainders = []
    for exponent in range(8):
        coefficients = [ZERO] * max(5, exponent + 1)
        coefficients[exponent] = ONE
        for degree in range(exponent, 3, -1):
            leading = coefficients[degree]
            for offset, coefficient in enumerate(polynomial):
                target = degree - 4 + offset
                coefficients[target] = subtract(coefficients[target], multiply(leading, coefficient))
        assert all(c == ZERO for c in coefficients[4:])
        remainder = tuple(coefficients[:4])
        # Independent evaluation checks guard polynomial-division bookkeeping.
        for index in indices:
            assert polynomial_value(remainder, roots[index]) == roots[(index * exponent) % 8]
        remainders.append((remainder[2], remainder[3]))
    return remainders


def cross_product(a, b):
    return subtract(multiply(a[0], b[1]), multiply(a[1], b[0]))


def build_certificate():
    roots = [ONE]
    for _ in range(7):
        roots.append(multiply(roots[-1], GENERATOR))
    assert len(set(roots)) == 8
    assert multiply(roots[-1], GENERATOR) == ONE and roots[4] == negate(ONE)
    root_norms, determinant_norms, denominator_norms, separation_norms = set(), set(), set(), set()
    for x, y in combinations(roots, 2):
        require_two_power(subtract(x, y), root_norms)
    all_remainders = [four_point_remainders(roots, indices) for indices in combinations(range(8), 4)]
    assert len(all_remainders) == 70
    labels = {}
    for a in range(8):
        for b in range(8):
            candidates = []
            for remainders in all_remainders:
                ra, rb = remainders[a], remainders[b]
                determinant = cross_product(ra, rb)
                if determinant != ZERO:
                    require_two_power(determinant, determinant_norms)
                    continue
                if rb == (ZERO, ZERO):
                    # Either there is no agreement or both words are affine:
                    # neither gives the MCA joint-exclusion clause.
                    continue
                coordinate = 0 if rb[0] != ZERO else 1
                denominator = rb[coordinate]
                require_two_power(denominator, denominator_norms)
                candidate = (negate(ra[coordinate]), denominator)
                assert all(add(multiply(ra[i], denominator), multiply(candidate[0], rb[i])) == ZERO
                           for i in range(2))
                for previous in candidates:
                    difference = cross_product(candidate, previous)
                    if difference == ZERO:
                        break
                    require_two_power(difference, separation_norms)
                else:
                    candidates.append(candidate)
            labels[a, b] = tuple(candidates)
    profile = tuple(tuple(len(labels[a, b]) for b in range(8)) for a in range(8))
    assert profile == EXPECTED_PROFILE, profile
    assert determinant_norms == {1, 2, 4, 8, 16}
    # Denominators and separations are also checked individually above, rather
    # than relying only on the printed aggregate sets.
    maximizers = tuple((a, b) for a in range(8) for b in range(8) if profile[a][b] == 9)
    assert max(map(max, profile)) == 9 and maximizers == EXPECTED_MAXIMIZERS
    return profile, labels, (root_norms, determinant_norms, denominator_norms, separation_norms)


def direct_prime_profile(p):
    """Independent check: enumerate EVERY scalar and every affine line from two points.

    This routine does not use cyclotomic remainders, determinants, or candidate
    enumeration. It evaluates the original existential MCA event directly.
    """
    assert p > 2 and all(p % divisor for divisor in range(2, p)) and p % 8 == 1
    g = next(x for x in range(2, p) if pow(x, 4, p) == p - 1)
    domain = [pow(g, i, p) for i in range(8)]
    words = [[pow(x, a, p) for x in domain] for a in range(8)]
    pairs = [(i, j, pow((domain[j] - domain[i]) % p, -1, p)) for i, j in combinations(range(8), 2)]
    profile = []
    for first_word in words:
        row = []
        for second_word in words:
            bad = 0
            for gamma in range(p):
                values = [(x + gamma * y) % p for x, y in zip(first_word, second_word)]
                for i, j, inverse in pairs:
                    slope = (values[j] - values[i]) * inverse % p
                    support = [k for k in range(8) if (values[k] - values[i] - slope * (domain[k] - domain[i])) % p == 0]
                    if len(support) < 4:
                        continue
                    individually_affine = []
                    for word in (first_word, second_word):
                        word_slope = (word[j] - word[i]) * inverse % p
                        individually_affine.append(all((word[k] - word[i] - word_slope * (domain[k] - domain[i])) % p == 0
                                                       for k in support))
                    if not all(individually_affine):
                        bad += 1
                        break
            row.append(bad)
        profile.append(tuple(row))
    return tuple(profile)


def main():
    profile, labels, norms = build_certificate()
    # Full scalar sweeps include the spectrum's exceptional characteristic 17.
    # These are independent error-detection checks, not the universal proof.
    for prime in (17, 41, 73):
        assert direct_prime_profile(prime) == profile, prime
    # Cross-check the already landed scanner at larger representative fields.
    from g328_k2_field_stability_boundary import scan_prime
    for prime in (17, 41, 257, 1009):
        expected_ceiling = 16 if prime == 17 else 40
        assert scan_prime(prime) == (expected_ceiling, 9, EXPECTED_MAXIMIZERS), prime
    print("Exact cyclotomic certificate: 70 supports x 64 monomial pencils")
    for name, values in zip(("root differences", "proportionality determinants", "candidate denominators", "candidate separations"), norms):
        print(f"{name} norms: {sorted(values)}")
    print("Complete field-uniform profile (rows a, columns b):")
    for row in profile:
        print(" ".join(str(value) for value in row))
    print(f"max=9; maximizers={EXPECTED_MAXIMIZERS}; total scalar labels={sum(map(len, labels.values()))}")
    print("Independent full-scalar finite-field checks: p=17,41,73 PASS")
    print("Existing G328 scan cross-checks: p=17,41,257,1009 PASS")
    print("PASS: every nonzero obstruction has a power-of-two norm; no exceptional odd characteristic")
    print("Scope: order eight, dimension two, monomial pencils, threshold four. Production prize OPEN.")


if __name__ == "__main__":
    main()
