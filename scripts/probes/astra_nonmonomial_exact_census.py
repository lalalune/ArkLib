#!/usr/bin/env python3
"""Exact, all-prime census of the explicit nonmonomial order-eight construction.

For g of order eight, u=0,v=0 on {g,g^2,g^3}; u=1,v=x on
{g^5,g^6,g^7}; (u(1),v(1))=(3,2), (u(-1),v(-1))=(5,2).

The threshold-four MCA bad-scalar count is exactly ten at every prime p=1 mod8
outside {17,41,97,137,337,641}. At17,97,337,641 it is nine. At41 and137 it is
ten or eleven depending on g; this generator dependence is explicitly checked.

Universal coverage comes from finite cyclotomic norms, not a prime sweep.
Two exceptional eleven-scalar cells are independently checked by enumerating
every scalar and EVERY affine polynomial. Stdlib only; no Lean proof claimed.
"""

from itertools import combinations

from astra_order_eight_monomial_certificate import (
    GENERATOR, ONE, ZERO, certified_norm, cross_product, multiply, negate, subtract,
)


EXCEPTIONAL_PRIMES = {17, 41, 97, 137, 337, 641}
EXPECTED_EXCEPTION_PROFILE = {
    17: {2: 9, 8: 9, 9: 9, 15: 9},
    41: {3: 11, 14: 11, 27: 10, 38: 10},
    97: {33: 9, 47: 9, 50: 9, 64: 9},
    137: {10: 10, 41: 11, 96: 10, 127: 11},
    337: {85: 9, 111: 9, 226: 9, 252: 9},
    641: {256: 9, 318: 9, 323: 9, 385: 9},
}
EXPECTED_EXTRA = {(41, 3): {23}, (41, 14): {5}, (137, 41): {85}, (137, 127): {46}}


def constant(n):
    return (n, 0, 0, 0)


def prime_divisors(n):
    assert n > 0
    divisors = set()
    d = 2
    while d * d <= n:
        while n % d == 0:
            divisors.add(d)
            n //= d
        d += 1
    if n > 1:
        divisors.add(n)
    return divisors


def cyclotomic_certificate():
    roots = [ONE]
    for _ in range(7):
        roots.append(multiply(roots[-1], GENERATOR))
    u = [constant(3), ZERO, ZERO, ZERO, constant(5), ONE, ONE, ONE]
    v = [constant(2), ZERO, ZERO, ZERO, constant(2), *roots[5:]]

    def divided_difference(word, i, j, k):
        return subtract(multiply(subtract(roots[j], roots[i]), subtract(word[k], word[i])),
                        multiply(subtract(roots[k], roots[i]), subtract(word[j], word[i])))

    determinant_norms, denominator_norms, separation_norms = set(), set(), set()
    residual_supports, labels = [], []
    for support in combinations(range(8), 4):
        i, j, k, ell = support
        aa = (divided_difference(u, i, j, k), divided_difference(u, i, j, ell))
        bb = (divided_difference(v, i, j, k), divided_difference(v, i, j, ell))
        determinant = cross_product(aa, bb)
        if determinant != ZERO:
            norm = certified_norm(determinant)
            determinant_norms.add(norm)
            if 0 in support and 4 in support and len(set(support) & {1, 2, 3}) == 1 and len(set(support) & {5, 6, 7}) == 1:
                residual_supports.append((support, determinant, norm))
            continue
        if bb == (ZERO, ZERO):
            continue
        coordinate = 0 if bb[0] != ZERO else 1
        candidate = (negate(aa[coordinate]), bb[coordinate])
        denominator_norms.add(certified_norm(candidate[1]))
        for previous in labels:
            difference = cross_product(candidate, previous)
            if difference == ZERO:
                break
            separation_norms.add(certified_norm(difference))
        else:
            labels.append(candidate)
    assert len(labels) == 10
    explicit_labels = [(negate(ONE), roots[i]) for i in (1, 2, 3, 5, 6, 7)]
    explicit_labels += [(constant(-3), constant(2)), (constant(-2), ONE),
                        (constant(-5), constant(2)), (constant(-4), constant(3))]
    assert all(any(cross_product(candidate, explicit) == ZERO for explicit in explicit_labels)
               for candidate in labels)
    assert all(any(cross_product(candidate, explicit) == ZERO for candidate in labels)
               for explicit in explicit_labels)
    assert denominator_norms == {2, 32, 162}
    assert len(residual_supports) == 9
    assert {entry[2] for entry in residual_supports} == {32, 800, 1312, 2624, 4384, 5184, 8768}
    all_norms = determinant_norms | denominator_norms | separation_norms
    divisors = set().union(*(prime_divisors(norm) for norm in all_norms))
    assert {p for p in divisors if p % 8 == 1} == EXCEPTIONAL_PRIMES
    return labels, (determinant_norms, denominator_norms, separation_norms), residual_supports


def field_words(p, g):
    assert pow(g, 4, p) == p - 1
    domain = [pow(g, i, p) for i in range(8)]
    assert len(set(domain)) == 8
    return domain, [3, 0, 0, 0, 5, 1, 1, 1], [2, 0, 0, 0, 2, *domain[5:]]


def direct_support_candidates(p, g):
    """Exact 70-support elimination in the specified field, including all degeneracies."""
    xs, u, v = field_words(p, g)
    bad = set()
    for i, j, k, ell in combinations(range(8), 4):
        def dd(word, h):
            return ((xs[j] - xs[i]) * (word[h] - word[i]) - (xs[h] - xs[i]) * (word[j] - word[i])) % p
        aa, bb = (dd(u, k), dd(u, ell)), (dd(v, k), dd(v, ell))
        if (aa[0] * bb[1] - aa[1] * bb[0]) % p or bb == (0, 0):
            continue
        coordinate = 0 if bb[0] else 1
        gamma = -aa[coordinate] * pow(bb[coordinate], -1, p) % p
        assert all((aa[h] + gamma * bb[h]) % p == 0 for h in range(2))
        bad.add(gamma)
    return bad


def explicit_ten_set(p, g):
    xs, _, _ = field_words(p, g)
    return ({-pow(xs[i], -1, p) % p for i in (1, 2, 3, 5, 6, 7)}
            | {-3 * pow(2, -1, p) % p, -2 % p, -5 * pow(2, -1, p) % p, -4 * pow(3, -1, p) % p})


def brute_all_affine(p, g):
    """Original MCA event: every gamma, intercept, and slope; no determinant method."""
    xs, u, v = field_words(p, g)
    bad, receipts = set(), {}
    for gamma in range(p):
        values = [(a + gamma * b) % p for a, b in zip(u, v)]
        for intercept in range(p):
            for slope in range(p):
                support = [i for i in range(8) if (intercept + slope * xs[i] - values[i]) % p == 0]
                if len(support) < 4:
                    continue
                i, j = support[:2]
                individual_affine = []
                for word in (u, v):
                    word_slope = (word[j] - word[i]) * pow(xs[j] - xs[i], -1, p) % p
                    individual_affine.append(all((word[k] - word[i] - word_slope * (xs[k] - xs[i])) % p == 0
                                                for k in support))
                if not all(individual_affine):
                    bad.add(gamma)
                    receipts[gamma] = (intercept, slope, tuple(support))
                    break
            if gamma in bad:
                break
    return bad, receipts


def main():
    labels, norm_sets, residuals = cyclotomic_certificate()
    actual_profile = {}
    for p, expected_generators in EXPECTED_EXCEPTION_PROFILE.items():
        assert all(p % d for d in range(2, p)) and p % 8 == 1
        generators = [g for g in range(2, p) if pow(g, 4, p) == p - 1]
        assert set(generators) == set(expected_generators)
        actual_profile[p] = {}
        for g in generators:
            actual = direct_support_candidates(p, g)
            explicit = explicit_ten_set(p, g)
            assert explicit <= actual
            assert actual - explicit == EXPECTED_EXTRA.get((p, g), set())
            actual_profile[p][g] = len(actual)
        assert actual_profile[p] == expected_generators
    receipts = {}
    for p, g in ((41, 3), (137, 41)):
        exhaustive, witness_data = brute_all_affine(p, g)
        assert exhaustive == direct_support_candidates(p, g)
        assert len(exhaustive) == 11
        extra = EXPECTED_EXTRA[p, g]
        receipts[p, g] = {gamma: witness_data[gamma] for gamma in extra}
    print(f"Generic symbolic candidate count={len(labels)}")
    for name, norms in zip(("proportionality determinants", "candidate denominators", "candidate separations"), norm_sets):
        print(f"{name} norms={sorted(norms)}")
    print(f"Exact possible exceptional primes p=1 mod8: {sorted(EXCEPTIONAL_PRIMES)}")
    print("Complete exceptional table (g: count):")
    for p, profile in actual_profile.items():
        print(f"p={p}: {profile}")
    print("Nine remaining 1A+1B+2C supports (indices, determinant coordinates, norm):")
    for residual in residuals:
        print(residual)
    print(f"Independent all-scalar/all-affine verification extra receipts: {receipts}")
    print("PASS: all other primes p=1 mod8 and all generators have exactly ten bad scalars")
    print("Scope: one explicit nonmonomial pencil at order eight, threshold four; no maximum claim; production prize OPEN.")


if __name__ == "__main__":
    main()
