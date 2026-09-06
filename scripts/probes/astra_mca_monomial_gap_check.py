#!/usr/bin/env python3
"""Exact controls for the monomial locator gap, not a universal MCA bound.

Standard library only. Production-length assertions concern integer indices
and the written coset proof; no production domain enumeration is performed.
"""

import itertools
import json
import math

P = 365375409332725729550921208179070755120141565953


def trim(a):
    while len(a) > 1 and a[-1] == 0:
        a.pop()
    return a


def multiply(a, b, p):
    c = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            c[i + j] = (c[i + j] + x * y) % p
    return trim(c)


def divide(a, b, p):
    a = trim([x % p for x in a])
    q = [0] * max(1, len(a) - len(b) + 1)
    inv = pow(b[-1], -1, p)
    while a != [0] and len(a) >= len(b):
        j = len(a) - len(b)
        c = a[-1] * inv % p
        q[j] = c
        for i, x in enumerate(b):
            a[i + j] = (a[i + j] - c * x) % p
        trim(a)
    return trim(q), a


def evaluate(a, x, p):
    value = 0
    for c in reversed(a):
        value = (value * x + c) % p
    return value


def roots(p, n):
    assert (p - 1) % n == 0
    for a in range(2, 100):
        g = pow(a, (p - 1) // n, p)
        if pow(g, n // 2, p) != 1:
            break
    xs = [pow(g, i, p) for i in range(n)]
    assert len(set(xs)) == n and pow(g, n, p) == 1
    return xs


def from_roots(xs, p):
    result = [1]
    for x in xs:
        result = multiply(result, [-x % p, 1], p)
    return result


def length16_census(p):
    n, k, b, e = 16, 8, 3, 4
    xs = roots(p, n)
    vanishing = [1] * n  # (X^n-1)/(X-1).
    monomial_matches = {11: 0, 12: 0}
    checks = 0
    for error_ids in itertools.combinations(range(1, n), e):
        locator = from_roots([xs[i] for i in error_ids], p)
        h = multiply([-1 % p, 1], locator, p)
        assert divide([-1 % p] + [0] * (n - 1) + [1], h, p)[1] == [0]
        for degree in monomial_matches:
            # Long division is independent of the consecutive-coefficient test.
            _, remainder = divide([0] * degree + locator, vanishing, p)
            remainder_condition = len(remainder) <= k + e
            start = 5 * b - 2 - degree
            gap_condition = all(h[j] == 0 for j in range(start, start + b))
            assert remainder_condition == gap_condition
            if remainder_condition:
                decoder, rest = divide(remainder, locator, p)
                assert rest == [0] and len(decoder) <= k
                assert sum(evaluate(decoder, x, p) == pow(x, degree, p)
                           for x in xs[1:]) >= 11
                monomial_matches[degree] += 1
            checks += 1
    assert all(count == 0 for count in monomial_matches.values())

    # Positive control for the general locator-to-decoder recovery: the word
    # is f plus a polynomial vanishing on exactly the complement of a locator.
    locator = from_roots(xs[1:5], p)
    agreement_factor = from_roots(xs[5:], p)
    decoder = [3, 1, 4, 1, 5, 9, 2, 6]
    word = agreement_factor[:]
    for j, c in enumerate(decoder):
        word[j] = (word[j] + c) % p
    _, remainder = divide(multiply(locator, word, p), vanishing, p)
    recovered, rest = divide(remainder, locator, p)
    assert rest == [0] and recovered == decoder
    assert sum(evaluate(word, x, p) == evaluate(decoder, x, p)
               for x in xs[1:]) == 11
    return {"p": p, "locators": math.comb(15, 4),
            "independent_remainder_gap_comparisons": checks,
            "monomial_candidates": monomial_matches,
            "positive_locator_recovery": True}


def sharp_gap_control(p, n):
    xs = roots(p, n)
    ell = n // 4
    q = (ell - 1) // 3
    b = 2 * q + 1
    # X^ell-1 has roots of exponent divisible by four. Q uses other roots.
    extra = [xs[j] for j in range(n) if j % 4 != 0][:q]
    small = from_roots(extra, p)
    h = multiply([-1 % p] + [0] * (ell - 1) + [1], small, p)
    assert len(h) - 1 == (n - 1) // 3
    assert sum(evaluate(h, x, p) == 0 for x in xs) == len(h) - 1
    assert evaluate(h, 1, p) == 0 and h[0] != 0
    assert divide([-1 % p] + [0] * (n - 1) + [1], h, p)[1] == [0]
    assert all(h[j] == 0 for j in range(q + 1, ell))
    assert ell - q - 1 == b - 1 and h[q] != 0 and h[ell] != 0
    assert not any(all(h[j] == 0 for j in range(start, start + b))
                   for start in range(1, len(h) - b))
    return {"p": p, "n": n, "divisor_degree": len(h) - 1,
            "attained_internal_zero_run": b - 1,
            "gap_boundary_coefficients_nonzero": True}


def integer_controls():
    result = []
    for a in range(1, 16):
        n = 4 ** a
        d, b = (n - 1) // 3, (n + 2) // 6
        support = sorted(sum(4 ** j for j in range(a) if mask >> j & 1)
                         for mask in range(2 ** a))
        assert all((j & ~d) == 0 for j in support)
        max_gap = max(y - x - 1 for x, y in zip(support, support[1:]))
        assert max_gap == b - 1
        if a <= 4:
            assert support == [j for j in range(d + 1) if math.comb(d, j) % 2]
        row = {"n": n, "d": d, "required_gap": b,
               "max_parity_zero_run": max_gap}
        if a >= 2:
            ell, q = n // 4, (n // 4 - 1) // 3
            assert ell == 3 * q + 1 and d == 4 * q + 1 and b == 2 * q + 1
            degree_low, degree_high = 3 * ell - 1, 3 * ell
            assert 5 * b - 2 - degree_low == q + 1
            assert 5 * b - 2 - degree_high == q
            assert degree_low >= 4 * b - 1 and degree_high <= 5 * b - 3
            assert 4 * q == d - 1
            row.update({"finite_field_excluded_degrees": [degree_low, degree_high],
                        "coset_root_cap": 4 * q})
        result.append(row)
    assert result[-1]["finite_field_excluded_degrees"] == [805306367, 805306368]
    return result


def main():
    census = [length16_census(p) for p in [17, 97, 113, 193, 257, 65537, P]]
    sharp = [sharp_gap_control(p, n)
             for p in [257, 65537, P] for n in [16, 64, 256]]
    print(json.dumps({
        "status": "PASS_MONOMIAL_GAP_CONTROLS",
        "length16_census": census,
        "sharp_divisor_controls": sharp,
        "integer_controls": integer_controls(),
        "scope": "Written general proofs plus finite controls; only two monomial "
                 "degrees excluded over the production field, no universal MCA bound."
    }, indent=2))


if __name__ == "__main__":
    main()
