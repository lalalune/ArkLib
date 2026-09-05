#!/usr/bin/env python3
"""Positive control for the conditional pair-cover conversion on other domains.

These domains are unions of three power-map fibres with two points removed.
They are not the production dyadic subgroup. Every displayed bad scalar has
a support witness and an independent Vandermonde no-joint certificate.
"""

from __future__ import annotations

import json
from math import isqrt


PRIME = 2013265921


def parity_row(xs: list[int]) -> list[int]:
    result = []
    for i, x in enumerate(xs):
        denominator = 1
        for j, y in enumerate(xs):
            if i != j:
                denominator = denominator * (x - y) % PRIME
        result.append(pow(denominator, -1, PRIME))
    # Independently verify annihilation of every monomial of degree < k.
    for exponent in range(len(xs) - 1):
        assert sum(a * pow(x, exponent, PRIME) for a, x in zip(result, xs)) % PRIME == 0
    return result


def cell(h: int) -> dict[str, object]:
    n, k, s = 3 * h - 2, (3 * h - 2) // 2, 2 * h - 1
    assert h >= 6 and h % 2 == 0 and h <= k - 2 and s - 1 >= k
    assert PRIME > n**4 and (PRIME - 1) % h == 0
    # The h used below have only the prime divisors 2 and 3.
    assert h % 3 == 0 and (h // 3) & ((h // 3) - 1) == 0
    root = next(
        z for base in range(2, PRIME)
        if (z := pow(base, (PRIME - 1) // h, PRIME)) != 1
        and pow(z, h // 2, PRIME) != 1 and pow(z, h // 3, PRIME) != 1
    )
    assert pow(root, h, PRIME) == 1
    powers = [pow(root, j, PRIME) for j in range(h)]
    levels = [pow(base, h, PRIME) for base in (1, 2, 3)]
    assert len(set(levels)) == 3
    fibres = [[base * z % PRIME for z in powers] for base in (1, 2, 3)]
    blocks = [fibres[0][:-1], fibres[1][:-1], fibres[2]]
    domain = sum(blocks, [])
    assert len(domain) == len(set(domain)) == n and 0 not in domain
    # The test domain is not any multiplicative coset of mu_n.
    assert len({pow(x, n, PRIME) for x in domain}) > 1
    alpha = (levels[0] - levels[2]) * pow(levels[1] - levels[2], -1, PRIME) % PRIME

    def values(x: int) -> list[int]:
        z = pow(x, h, PRIME)
        return [0, (z - levels[0]) % PRIME, alpha * (z - levels[1]) % PRIME]

    codewords = [values(x) for x in domain]
    pair_labels = [(0, 1)] * (h - 1) + [(0, 2)] * (h - 1) + [(1, 2)] * h
    cores: list[set[int]] = [set(), set(), set()]
    u0, u1 = [], []
    for j, (x, fs, pair) in enumerate(zip(domain, codewords, pair_labels)):
        assert len(set(fs)) == 2 and fs[pair[0]] == fs[pair[1]]
        u0.append(fs[pair[0]])
        u1.append(x * u0[-1] % PRIME)
        for i in pair:
            cores[i].add(j)
    assert [len(core) for core in cores] == [s - 1, s, s]

    changed = n - 1
    xi, v = domain[changed], codewords[changed][1]
    assert v != 0 and v == codewords[changed][2]
    for core in cores:
        core.discard(changed)
    assert all(len(core) == s - 1 for core in cores)
    old = {(-pow(x, -1, PRIME)) % PRIME for x in domain}
    fresh = []
    for gamma in range(PRIME):
        if gamma not in old:
            fresh.append(gamma)
            if len(fresh) == 2:
                break
    lam, mu = fresh
    b = v * (1 + mu * xi) * pow(mu - lam, -1, PRIME) % PRIME
    u0[changed], u1[changed] = -lam * b % PRIME, b
    assert b != 0 and (b - xi * v) % PRIME != 0

    witnesses = []
    for j, (x, pair) in enumerate(zip(domain, pair_labels)):
        if j != changed:
            odd = next(i for i in range(3) if i not in pair)
            witnesses.append(((-pow(x, -1, PRIME)) % PRIME, odd, j))
    witnesses.extend([(lam, 0, changed), (mu, 1, changed)])
    assert len(witnesses) == len({gamma for gamma, _, _ in witnesses}) == n + 1
    for gamma, i, extra in witnesses:
        support = cores[i] | {extra}
        assert len(support) == s and extra not in cores[i]
        # The explanatory polynomial is (1+gamma*X)*f_i, degree <= h+1 < k.
        assert h + 1 < k
        for j in support:
            expected = (1 + gamma * domain[j]) * codewords[j][i] % PRIME
            assert (u0[j] + gamma * u1[j]) % PRIME == expected
        # A dual row on k core points plus the extra point rules out any
        # joint pair of degree < k on the full support, independently of
        # the displayed local codeword explanation.
        restricted = sorted(cores[i])[:k] + [extra]
        row = parity_row([domain[j] for j in restricted])
        a = sum(weight * u0[j] for weight, j in zip(row, restricted)) % PRIME
        b = sum(weight * u1[j] for weight, j in zip(row, restricted)) % PRIME
        assert (a, b) != (0, 0) and (a + gamma * b) % PRIME == 0
    return {
        "n": n, "k": k, "power_map_degree": h, "agreement": s,
        "pair_region_sizes": [h - 1, h - 1, h],
        "primitive_hth_root": root, "domain": domain,
        "alpha": alpha, "fresh_scalars": fresh,
        "distinct_bad_scalars_certified": len(witnesses),
        "independent_no_joint_parity_checks": len(witnesses),
        "is_production_domain": False,
    }


if __name__ == "__main__":
    assert all(PRIME % divisor for divisor in range(2, isqrt(PRIME) + 1))
    cells = [cell(h) for h in (6, 12, 24, 48)]
    print(json.dumps({
        "status": "PAIR_COVER_CONVERSION_POSITIVE_CONTROL_OTHER_DOMAINS",
        "prime": PRIME,
        "cells": cells,
        "total_no_joint_parity_checks": sum(c["independent_no_joint_parity_checks"] for c in cells),
        "production_consequence": "NONE: these are different evaluation domains",
    }, indent=2))
