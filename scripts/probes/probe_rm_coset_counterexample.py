#!/usr/bin/env python3
"""Probe (#389): counterexample hunt for the agreement-rm coset-closure lemma.

LEMMA (to prove or refute): an rm-subset R of the smooth domain <g> (cyclic order
n = s*m) with power sums p_j(R) = sum_{x in R} x^j = 0 for
    j in {1,..,m-1} U {m+1,..,2m-1}
is a union of cosets of the order-m subgroup H = <g^s> (equivalently: a fibre-union).

If TRUE, the ladder word's list at agreement rm is EXACTLY N_fib (no wall, provable).
If FALSE, exact list at agreement rm exceeds N_fib; the counterexample is the lead.

m=2 case (2-power, production-relevant): windows = {1} U {3}; conditions p_1 = p_3 = 0;
H = {1,-1}; coset-closure <=> R = -R (negation-symmetric).
We hunt for R subset mu_n, even |R|, p_1 = p_3 = 0, R != -R.

Strategy: build R from negation-asymmetric "atoms".  For each candidate multiset of
<= rm elements (sampled / structured), test p_1 = p_3 = 0 over F_p and symmetry.
We do exhaustive for small, randomized+structured for large.
"""
import itertools, random, sys


def find_g(p, n):
    for h in range(2, 4000):
        x = pow(h, (p - 1) // n, p)
        if pow(x, n // 2, p) != 1 and pow(x, n, p) == 1:
            return x
    return None


def hunt_m2(n, p, r, exhaustive_limit=300000):
    """search for R subset <g>, |R| = 2r, p_1 = p_3 = 0, R != -R."""
    g = find_g(p, n)
    if g is None:
        return ("no g", None)
    dom = [pow(g, i, p) for i in range(n)]
    neg1 = pow(g, n // 2, p)  # = -1
    a = 2 * r
    cubes = [pow(x, 3, p) for x in dom]
    found = []
    total = 0
    # exhaustive if small
    from math import comb
    if comb(n, a) <= exhaustive_limit:
        for R in itertools.combinations(range(n), a):
            s1 = sum(dom[i] for i in R) % p
            if s1 != 0:
                continue
            s3 = sum(cubes[i] for i in R) % p
            if s3 != 0:
                continue
            total += 1
            Rset = set(R)
            # negation index: -dom[i] = dom[(i + n/2) % n]
            negset = {(i + n // 2) % n for i in R}
            if negset != Rset:
                found.append(R)
                if len(found) >= 3:
                    break
        return (f"exhaustive: {total} valid, {len(found)} asymmetric", found[:3])
    # randomized + structured search for larger n
    rng = random.Random(389 + n)
    for _ in range(400000):
        R = rng.sample(range(n), a)
        s1 = sum(dom[i] for i in R) % p
        if s1 != 0:
            continue
        s3 = sum(cubes[i] for i in R) % p
        if s3 != 0:
            continue
        total += 1
        negset = {(i + n // 2) % n for i in R}
        if negset != set(R):
            found.append(R)
            if len(found) >= 3:
                break
    # structured: take a symmetric valid R and swap one antipodal pair for another
    return (f"randomized: {total} valid hits, {len(found)} asymmetric", found[:3])


def hunt_general(n, m, r, p):
    """exhaustive (small n) for general m: windows {1..m-1} U {m+1..2m-1}."""
    g = find_g(p, n)
    if g is None:
        return "no g"
    dom = [pow(g, i, p) for i in range(n)]
    s = n // m
    a = r * m
    H = sorted({(s * i) % n for i in range(m)})  # index-subgroup <g^s>
    windows = list(range(1, m)) + list(range(m + 1, 2 * m))
    pows = {j: [pow(x, j, p) for x in dom] for j in windows}
    from math import comb
    if comb(n, a) > 400000:
        return f"(C({n},{a}) too large for exhaustive)"
    total, asym = 0, 0
    ex = None
    for R in itertools.combinations(range(n), a):
        if any(sum(pows[j][i] for i in R) % p != 0 for j in windows):
            continue
        total += 1
        Rset = set(R)
        closed = all(((i + h) % n) in Rset for i in R for h in H)
        if not closed:
            asym += 1
            if ex is None:
                ex = R
    return f"n={n} m={m} r={r}: {total} valid, {asym} non-coset" + (
        f" (e.g. {ex})" if ex else "")


def main():
    print("=== m=2 counterexample hunt (coset-closure <=> negation-symmetric) ===")
    for (n, p, r) in [(16, 12289, 3), (32, 97, 3), (32, 97, 5),
                      (64, 193, 3), (64, 193, 5), (128, 257, 3)]:
        res, ex = hunt_m2(n, p, r)
        print(f"  n={n}, r={r} (a={2*r}), p={p}: {res}", flush=True)
        if ex:
            print(f"    ASYMMETRIC VALID R: {ex[0]}", flush=True)
    print("\n=== general-m exhaustive (small n) ===")
    print("  " + hunt_general(16, 2, 3, 12289), flush=True)
    print("  " + hunt_general(16, 4, 2, 12289), flush=True)
    print("  " + hunt_general(24, 4, 2, 13)  if (13 - 1) % 24 == 0 else "  (skip 24)",
          flush=True)
    print("  " + hunt_general(32, 4, 2, 97), flush=True)
    return 0


if __name__ == "__main__":
    sys.exit(main())
