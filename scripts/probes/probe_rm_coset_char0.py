#!/usr/bin/env python3
"""Probe (#389): char-0 counterexample hunt for the agreement-rm coset-closure lemma.

Trustworthy (characteristic-zero) test, n = 2^mu so mu_n = <zeta_n>, zeta = primitive
n-th root of unity, minimal relation zeta^{n/2} = -1.  Any sum of n-th roots of unity
sum_i zeta^{a_i} reduces EXACTLY to an integer vector in basis {1, zeta, .., zeta^{n/2-1}}
via zeta^a = (-1)^{a // (n/2)} * zeta^{a mod (n/2)}; it is 0 iff that vector is 0.

LEMMA: R subset {zeta^0,..,zeta^{n-1}}, |R| = r*m, with power sums p_j(R) = 0 for
j in {1,..,m-1} U {m+1,..,2m-1}, is a union of cosets of the order-m subgroup
H = <zeta^s> (s = n/m).  We hunt EXACTLY (char 0) for a counterexample: a valid R
that is NOT coset-closed.

m=2 (production): conditions p_1 = p_3 = 0; coset-closure <=> R = -R (negation symmetric,
-zeta^a = zeta^{a + n/2}).  Exhaustive where feasible, structured otherwise.
"""
import itertools, sys
from math import comb


def reduce_sum(indices, n, jmul):
    """exact char-0 value of sum_i zeta_n^{jmul * a_i} as integer vector (len n/2).
    returns the coefficient tuple; the sum is zero iff all zero."""
    h = n // 2
    vec = [0] * h
    for a in indices:
        e = (jmul * a) % n
        sign = -1 if (e // h) % 2 == 1 else 1
        vec[e % h] += sign
    return vec


def is_zero(indices, n, jmul):
    return all(c == 0 for c in reduce_sum(indices, n, jmul))


def hunt_m2(n, r, exhaustive_limit=2_000_000):
    """R subset Z/n (as exponents), |R|=2r, p_1=p_3=0 (char 0), R != -R?"""
    a = 2 * r
    h = n // 2
    if comb(n, a) <= exhaustive_limit:
        total, asym, ex = 0, 0, None
        for R in itertools.combinations(range(n), a):
            if not is_zero(R, n, 1):
                continue
            if not is_zero(R, n, 3):
                continue
            total += 1
            negset = {(i + h) % n for i in R}
            if negset != set(R):
                asym += 1
                if ex is None:
                    ex = R
        return f"n={n} r={r} a={a}: EXHAUSTIVE {total} valid, {asym} ASYMMETRIC" + (
            f"  e.g. {ex}" if ex else "  -> all coset-closed"), ex
    else:
        # structured: enumerate by negation-pair structure.
        # A negation-symmetric R = union of antipodal pairs {i, i+h}; r pairs.
        # An asymmetric valid R must include some i without i+h.  Search subsets
        # built from singletons + pairs with p1=p3=0 via meet-in-the-middle on
        # the half-domain is complex; instead random + greedy.
        import random
        rng = random.Random(7 + n)
        total, ex = 0, None
        for _ in range(2_000_000):
            R = rng.sample(range(n), a)
            if not is_zero(R, n, 1):
                continue
            if not is_zero(R, n, 3):
                continue
            total += 1
            negset = {(i + h) % n for i in R}
            if negset != set(R):
                ex = R
                break
        return f"n={n} r={r} a={a}: RANDOMIZED {total} valid hits" + (
            f", ASYMMETRIC e.g. {ex}" if ex else ", none asymmetric"), ex


def hunt_general(n, m, r, exhaustive_limit=2_000_000):
    a = r * m
    s = n // m
    H = [(s * i) % n for i in range(m)]
    windows = list(range(1, m)) + list(range(m + 1, 2 * m))
    if comb(n, a) > exhaustive_limit:
        return f"n={n} m={m} r={r}: (C({n},{a}) too big)"
    total, asym, ex = 0, 0, None
    for R in itertools.combinations(range(n), a):
        if any(not is_zero(R, n, j) for j in windows):
            continue
        total += 1
        Rset = set(R)
        if not all(((i + hh) % n) in Rset for i in R for hh in H):
            asym += 1
            if ex is None:
                ex = R
    return f"n={n} m={m} r={r} a={a}: EXHAUSTIVE {total} valid, {asym} non-coset" + (
        f" e.g. {ex}" if ex else " -> all coset-closed")


def main():
    print("=== char-0 m=2 hunt: does p_1=p_3=0 force negation symmetry? ===",
          flush=True)
    for (n, r) in [(8, 2), (16, 3), (16, 4), (16, 5), (32, 3), (32, 4),
                   (32, 5), (64, 3), (64, 4)]:
        msg, ex = hunt_m2(n, r)
        print("  " + msg, flush=True)
    print("\n=== char-0 general-m exhaustive ===", flush=True)
    for (n, m, r) in [(16, 2, 3), (16, 4, 2), (16, 4, 3), (32, 4, 2),
                      (32, 8, 2), (64, 4, 2)]:
        print("  " + hunt_general(n, m, r), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
