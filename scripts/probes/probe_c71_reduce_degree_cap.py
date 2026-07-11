#!/usr/bin/env python3
"""Probe for C71 sparse-strata reduced-degree incidence cap.

For proper thin 2-power subgroups mu_n < F_p^*, compare the root count of a high-degree sparse
polynomial on mu_n with the natDegree of its exponent-reduced mod-n polynomial.  This is the
machine analogue of C71SparseStrataReduce.sparse_munRoot_card_le_reduce_natDegree.
"""
from random import Random


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


def primitive_root(p: int) -> int:
    factors = []
    m = p - 1
    d = 2
    while d * d <= m:
        if m % d == 0:
            factors.append(d)
            while m % d == 0:
                m //= d
        d += 1
    if m > 1:
        factors.append(m)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in factors):
            return g
    raise RuntimeError("no primitive root")


def next_prime_congruent(start: int, n: int) -> int:
    p = start + ((1 - start) % n)
    if p <= n + 1:
        p += n
    while not is_prime(p):
        p += n
    return p


def reduced_coeffs(terms, n, p):
    coeff = {}
    for c, e in terms:
        r = e % n
        coeff[r] = (coeff.get(r, 0) + c) % p
        if coeff[r] == 0:
            del coeff[r]
    return coeff


def eval_terms(terms, x, p):
    return sum(c * pow(x, e, p) for c, e in terms) % p


def main():
    rng = Random(44471)
    cases = []
    for n in (8, 16, 32, 64):
        for beta in (4, 5):
            p = next_prime_congruent(n ** beta + 123, n)
            if (p - 1) // n <= 1:
                continue
            cases.append((n, p))
    total = 0
    strict = 0
    for n, p in cases:
        gen = primitive_root(p)
        zeta = pow(gen, (p - 1) // n, p)
        mu = [pow(zeta, j, p) for j in range(n)]
        for _ in range(80):
            width = rng.randint(2, 6)
            terms = []
            for _j in range(width):
                c = rng.randrange(1, p)
                # deliberately high exponents, including wrap-around beyond p/n scale
                e = rng.randrange(0, n * n * 3 + 11)
                terms.append((c, e))
            red = reduced_coeffs(terms, n, p)
            if not red:
                continue
            deg = max(red)
            roots = sum(1 for x in mu if x != 0 and eval_terms(terms, x, p) == 0)
            if roots > deg:
                raise AssertionError((n, p, terms, red, roots, deg))
            strict += int(roots < deg)
            total += 1
    print(f"PASS c71 reduced-degree cap: {total} nonzero reduced sparse directions, strict={strict}, proper thin cases={cases}")


if __name__ == "__main__":
    main()
