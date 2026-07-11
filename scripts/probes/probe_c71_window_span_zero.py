#!/usr/bin/env python3
"""
Probe for the C71 reduced support-span zero consumer.

For proper thin dyadic subgroups mu_n < F_p^*, build sparse high-exponent
polynomials whose exponents all reduce to one residue mod n and whose reduced
coefficient at that residue is nonzero. Then the reduced support span is zero
(a single monomial), hence no nonzero mu_n point can be a root.
"""
from __future__ import annotations

import random


def is_prime(n: int) -> bool:
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return False
        d += 2
    return True


def next_prime_congruent(start: int, mod: int) -> int:
    p = max(start, 2)
    while True:
        if p % mod == 1 and is_prime(p):
            return p
        p += 1


def primitive_root(p: int) -> int:
    factors = []
    x = p - 1
    d = 2
    while d * d <= x:
        if x % d == 0:
            factors.append(d)
            while x % d == 0:
                x //= d
        d += 1
    if x > 1:
        factors.append(x)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")


def mu_n(p: int, n: int) -> list[int]:
    g = primitive_root(p)
    z = pow(g, (p - 1) // n, p)
    return [pow(z, i, p) for i in range(n)]


def eval_sparse(p: int, terms: list[tuple[int, int]], x: int) -> int:
    return sum(c * pow(x, e, p) for c, e in terms) % p


def main() -> None:
    random.seed(1781738472)
    cases = []
    total = zero_span = 0
    for n in [8, 16, 32, 64]:
        for beta in [4, 5]:
            p = next_prime_congruent(n ** beta + 1, n)
            if (p - 1) // n <= 1:
                continue
            roots = mu_n(p, n)
            assert len(set(roots)) == n and all(pow(x, n, p) == 1 for x in roots)
            for residue in range(n):
                for width in [1, 2, 3, 4, 5]:
                    # all exponents reduce to the same residue, but are high/wrapped
                    exps = [residue + n * j for j in range(width)]
                    coeffs = [random.randrange(1, p) for _ in exps]
                    red_coeff = sum(coeffs) % p
                    if red_coeff == 0:
                        coeffs[-1] = (coeffs[-1] + 1) % p or 1
                        red_coeff = sum(coeffs) % p
                    assert red_coeff != 0
                    terms = list(zip(coeffs, exps))
                    root_count = sum(1 for x in roots if x != 0 and eval_sparse(p, terms, x) == 0)
                    total += 1
                    if root_count == 0:
                        zero_span += 1
                    else:
                        raise AssertionError((n, beta, p, residue, width, root_count))
            cases.append((n, beta, p))
    print(
        "PASS c71 reduced support-span zero: "
        f"{zero_span}/{total} zero incidences, proper thin cases={cases}"
    )


if __name__ == "__main__":
    main()
