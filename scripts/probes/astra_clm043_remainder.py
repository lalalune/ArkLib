#!/usr/bin/env python3
"""Exact diagnostics for the CLM-043 remainder improvement 87 -> 24.

The accompanying proof uses the classical Hasse bound for elliptic curves;
this script is independent diagnostic evidence, not a proof of that theorem
or a bound on the still-open main term U. No floating-point arithmetic.

It checks the six original subgroup cells by both elementary-symmetric rows
and direct ordered triple-overlap sums, retains every inverse-root zero,
checks individual quadratic identities and quartic Hasse inequalities, and
then scans admissible primes <=3000. Non-subgroup cells also exercise the
proved extension to arbitrary distinct nonzero evaluation points.
"""

from collections import Counter
from itertools import combinations
from math import comb, isqrt, prod


FROZEN = (
    (97, 3, 93, 0, -3348),
    (257, 4, 964, 0, -34704),
    (641, 5, 6380, 0, -229680),
    (1297, 6, 25464, 64800, -851904),
    (1459, 6, 27768, 0, -999648),
    (2521, 7, 118377, 211680, -4049892),
)


def prime(p):
    return p >= 2 and all(p % d for d in range(2, isqrt(p) + 1))


def legendre_table(p):
    table = [-1] * p
    table[0] = 0
    for x in range(1, p):
        table[x * x % p] = 1
    return table


def sector_counts(n):
    n3 = comb(n, 3)
    n2 = 3 * (n - 3) * n3
    n1 = 3 * (comb(n - 3, 2) if n >= 5 else 0) * n3
    return n1, n2, n3


def check_algebraic_budget(n, p):
    """Check the square-root comparison using integer squares only."""
    assert n >= 3 and p >= n**4
    n1, n2, n3 = sector_counts(n)
    rational = 36 * (n3 * (p - 4) + 4 * n2 + 3 * n1)
    radical = 72 * n1
    room = 24 * p * n**3 - rational
    assert room > 0 and room * room > radical * radical * p
    return rational, radical


def elementary_rows(p, domain):
    n = len(domain)
    assert prime(p) and p % 2 and n >= 3 and p >= n**4
    assert len(set(domain)) == n and all(0 < a < p for a in domain)
    chi = legendre_table(p)
    rows = []
    u = d6 = remainder_identity = 0
    for t in range(1, p):
        values = tuple(chi[(1 - a * t) % p] for a in domain)
        r = sum(x * x for x in values)
        assert r == n - int(pow(t, -1, p) in domain)
        e = [1, 0, 0, 0, 0, 0, 0]
        for x in values:
            for degree in range(6, 0, -1):
                e[degree] += x * e[degree - 1]
        assert e[3] * e[3] == (20 * e[6] + 6 * (r - 4) * e[4]
                                + (r - 2) * (r - 3) * e[2] + comb(r, 3))
        u += e[3] * e[3]
        d6 += 720 * e[6]
        remainder_identity -= (216 * (r - 4) * e[4]
                               + 36 * (r - 2) * (r - 3) * e[2]
                               + 6 * r * (r - 1) * (r - 2))
        rows.append(values)
    remainder = d6 - 36 * u
    assert remainder == remainder_identity
    rational, radical = check_algebraic_budget(n, p)
    excess = abs(remainder) - rational
    assert excess <= 0 or excess * excess <= radical * radical * p
    assert abs(remainder) < 24 * p * n**3
    return (u, d6, remainder), rows, chi


def independent_overlap_check(p, domain, rows, chi, result):
    n = len(domain)
    triples = list(combinations(range(n), 3))
    profiles = {a: [prod(row[i] for i in a) for row in rows] for a in triples}
    sectors, counts = Counter(), Counter()
    for a in triples:
        for b in triples:
            common = set(a) & set(b)
            j = len(common)
            counts[j] += 1
            total = sum(x * y for x, y in zip(profiles[a], profiles[b]))
            sectors[j] += total
            different = sorted(set(a) ^ set(b))
            if j == 3:
                assert total == p - 4
            elif j == 2:
                x, y = (domain[i] for i in different)
                correction = sum(chi[((1 - x * pow(domain[i], -1, p))
                                      * (1 - y * pow(domain[i], -1, p))) % p] for i in common)
                assert total == -chi[x * y % p] - 1 - correction
                assert abs(total) <= 4
            elif j == 1:
                intersection_point = domain[next(iter(common))]
                inverse = pow(intersection_point, -1, p)
                deleted_value = prod(chi[(1 - domain[i] * inverse) % p] for i in different)
                full_quartic_sum = total + 1 + deleted_value
                leading_character = chi[prod(domain[i] for i in different) % p]
                # Hasse with the exact infinity correction, not a rounded sqrt.
                assert (full_quartic_sum + leading_character) ** 2 <= 4 * p
                excess = abs(total) - 3
                assert excess <= 0 or excess * excess <= 4 * p
    n1, n2, n3 = sector_counts(n)
    assert (counts[1], counts[2], counts[3]) == (n1, n2, n3)
    u, d6, remainder = result
    assert sum(sectors.values()) == u
    assert 36 * sectors[0] == d6
    assert remainder == -36 * (sectors[1] + sectors[2] + sectors[3])
    return tuple(sectors[j] for j in (1, 2, 3))


def main():
    print("CLM-043 remainder: exact overlap diagnostics")
    for p, n, expected_u, expected_d6, expected_r in FROZEN:
        subgroup = tuple(a for a in range(1, p) if pow(a, n, p) == 1)
        assert len(subgroup) == n
        result, rows, chi = elementary_rows(p, subgroup)
        assert result == (expected_u, expected_d6, expected_r)
        sectors = independent_overlap_check(p, subgroup, rows, chi, result)
        print(f"(p,n)=({p},{n}) U,D6,R={result}; I1,I2,I3={sectors}; strict24bound PASS")
    non_subgroup = 0
    for p, n in ((97, 3), (641, 5), (1459, 6), (2521, 7)):
        domain = tuple(range(1, n + 1))
        result, rows, chi = elementary_rows(p, domain)
        independent_overlap_check(p, domain, rows, chi, result)
        non_subgroup += 1
    swept = 0
    for p in range(83, 3001, 2):
        if not prime(p):
            continue
        for n in range(3, 8):
            if p < n**4 or (p - 1) % n:
                continue
            subgroup = tuple(a for a in range(1, p) if pow(a, n, p) == 1)
            elementary_rows(p, subgroup)
            swept += 1
    # The universal n>=4 argument is symbolic in the note. These arithmetic
    # checks protect its expansion and include the literal production order.
    for n in list(range(4, 257)) + [2**30]:
        n1, n2, n3 = sector_counts(n)
        margin_polynomial = (198 * n**5 - 669 * n**4 + 1098 * n**3
                             - 921 * n**2 + 486 * n - 168)
        endpoint_bound = 36 * (n3 * (n**4 - 4) + 4 * n2 + n1 * (2 * n * n + 3))
        assert 24 * n**7 - endpoint_bound == n * margin_polynomial
        assert margin_polynomial == n**4 * (198 * n - 669) + n**2 * (1098 * n - 921) + 486 * n - 168
        assert min(198 * n - 669, 1098 * n - 921, 486 * n - 168) > 0
        check_algebraic_budget(n, n**4)
    print(f"Independent non-subgroup overlap checks: {non_subgroup} cells PASS")
    print(f"All admissible subgroup cells with p<=3000, n=3..7: {swept} PASS")
    print("Exact endpoint arithmetic through n=256 and n=2^30 PASS")
    print("Improved theorem: |D6-36U| < 24*q*n^3 for q>=n^4, n>=3.")
    print("Proof input: classical Hasse theorem; no new bound on U; production prize OPEN.")


if __name__ == "__main__":
    main()
