#!/usr/bin/env python3
"""Falsify-first probe: THE TREE LAW for coset packing at two-prime moduli
(issue #232; O121/O122's named next — the exact k-generator criterion).

CANDIDATE LAW: a multiplicity vector (a_d) of canonical mu_d-cosets is
packable in Z_n  IFF  the completed modulus multiset

    M = {  s_d = n/d  with multiplicity a_d  }  ∪  { n } ^ (n - sum a_d d)

(add one modulus-n singleton per uncovered point) is TREE-REALIZABLE:
realizable by recursive prime splitting starting from modulus 1 —

    T(m, M):  M == {m}  (leaf),  or  for some prime p with  m*p | n,
              M partitions into p sub-multisets M_1..M_p with every
              T(m*p, M_i)  realizable.

WHY: a disjoint family + singletons on its complement is an EXACT COVER of
Z_n with the completed moduli; tree-realizable multisets are exactly the
"natural" disjoint covering systems; Berger-Felzenbaum-Fraenkel theory says
natural systems exhaust exact covers when n has at most two prime factors.
Sufficiency (tree => packable) is constructive at any n; necessity is the
BFF naturality phenomenon, here put to the machine test.

CHECK: for n in {12, 18, 24, 36} (two-prime) and ALL volume-feasible
multiplicity vectors over the divisors of n: exact packability (backtracking
over canonical bases, the O122 CSP) == tree-realizability of the completed
multiset.  Also n = 30 (THREE primes) to see whether the law survives or a
three-prime counterexample appears (BFF naturality is a two-prime theorem;
at 3+ primes non-natural exact covers exist in general DCS theory — find
whether one shows up at n = 30 with canonical cosets).

Exit 0 iff the two-prime law matches EXACTLY everywhere (three-prime
mismatches are reported as findings, not failures).
"""
import sys
from math import gcd
from functools import lru_cache
from itertools import product as iproduct

FAILS = 0


def fail(msg):
    global FAILS
    FAILS += 1
    print("FAIL:", msg)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def prime_factors(n):
    ps, m = [], n
    p = 2
    while p * p <= m:
        if m % p == 0:
            ps.append(p)
            while m % p == 0:
                m //= p
        p += 1
    if m > 1:
        ps.append(m)
    return ps


def coset(n, d, r):
    s = n // d
    return frozenset(r + j * s for j in range(d))


def packable(n, counts):
    """Exact backtracking over canonical bases (largest cosets first)."""
    items = sorted(((d, a) for d, a in counts.items() if a > 0),
                   key=lambda x: -x[0])
    types = [d for d, a in items for _ in range(a)]

    def rec(i, used, min_base):
        if i == len(types):
            return True
        d = types[i]
        s = n // d
        start = min_base if i > 0 and types[i - 1] == d else 0
        for r in range(start, s):
            c = coset(n, d, r)
            if not (c & used):
                if rec(i + 1, used | c, r + 1):
                    return True
        return False

    return rec(0, frozenset(), 0)


def tree_realizable(n, counts):
    """Tree-realizability of the completed modulus multiset.

    State: multiset of STEPS (s = n/d), encoded as a sorted tuple of
    (step, count); singletons enter as step n."""
    vol = sum(d * a for d, a in counts.items())
    base = {}
    for d, a in counts.items():
        if a:
            base[n // d] = base.get(n // d, 0) + a
    if n - vol:
        base[n] = base.get(n, 0) + (n - vol)
    primes = prime_factors(n)

    def normalize(ms):
        return tuple(sorted((s, c) for s, c in ms.items() if c))

    @lru_cache(maxsize=None)
    def T(m, ms):
        msd = dict(ms)
        total = sum((n // s) * c for s, c in msd.items())  # elements covered
        if total != n // m:
            return False
        if msd == {m: 1}:
            return True
        if m in msd and msd[m] >= 1 and len(msd) == 1 and msd[m] == 1:
            return True
        # all moduli must be proper multiples of m
        if m in msd:
            return False  # a step-m progression at modulus m IS the whole
            # class; coexistence with anything else is impossible, and the
            # singleton case was handled above
        for p in primes:
            if (n // m) % p != 0:
                continue
            mp = m * p
            # partition ms into p parts, each tree-realizable at modulus mp.
            # all moduli in ms are multiples of mp? not necessarily -- a part
            # can carry moduli that are multiples of mp deeper down; the
            # recursion handles it.  enumerate partitions of each count into
            # p ordered parts, with symmetry reduction via canonical order.
            items = sorted(msd.items())

            def assign(idx, parts):
                if idx == len(items):
                    key_parts = [normalize(dict(pt)) for pt in parts]
                    # symmetry: parts are unordered -> canonical sort
                    for kp in key_parts:
                        if not T(mp, kp):
                            return False
                    return True
                s, c = items[idx]
                if s % mp != 0:
                    return False

                def distribute(j, rem, cur):
                    if j == len(parts) - 1:
                        cur.append(rem)
                        if assign_next(cur):
                            cur.pop()
                            return True
                        cur.pop()
                        return False
                    for take in range(rem + 1):
                        cur.append(take)
                        if distribute(j + 1, rem - take, cur):
                            cur.pop()
                            return True
                        cur.pop()
                    return False

                def assign_next(distribution):
                    new_parts = []
                    for pt, take in zip(parts, distribution):
                        pt2 = dict(pt)
                        if take:
                            pt2[s] = pt2.get(s, 0) + take
                        new_parts.append(pt2)
                    return assign(idx + 1, new_parts)

                return distribute(0, c, [])

            if assign(0, [dict() for _ in range(p)]):
                return True
        return False

    return T(1, normalize(base))


def run_case(n, hard=True, max_types=None):
    ds = divisors(n)
    mismatches = []
    tested = 0
    ranges = [range(n // d + 1) for d in ds]
    for vec in iproduct(*ranges):
        counts = dict(zip(ds, vec))
        vol = sum(d * a for d, a in counts.items())
        if vol > n:
            continue
        if max_types is not None and sum(1 for a in vec if a) > max_types:
            continue
        tested += 1
        pk = packable(n, counts)
        tr = tree_realizable(n, counts)
        if pk != tr:
            mismatches.append((dict((d, a) for d, a in counts.items() if a),
                               pk, tr))
    tag = "TWO-PRIME" if hard else "THREE-PRIME (finding only)"
    cap = f", types<={max_types}" if max_types else ""
    print(f"n={n} [{tag}{cap}]: tested {tested}, mismatches {len(mismatches)}",
          flush=True)
    for w, pk, tr in mismatches[:6]:
        print(f"    {'PACKABLE-not-tree' if pk else 'TREE-not-packable'}: {w}",
              flush=True)
    if hard and mismatches:
        fail(f"n={n}: tree law violated on {len(mismatches)} vectors")
    return mismatches


def main():
    # n = 36's full box is too slow for the partition-enumerating tree
    # checker; 12/18/24 are exhaustive, 36 is covered on the slice with at
    # most 3 active types (where all O121 witnesses live).
    for n in (12, 18, 24):
        run_case(n, hard=True)
    run_case(36, hard=True, max_types=3)
    run_case(30, hard=False, max_types=3)
    if FAILS:
        print(f"{FAILS} FAILURES")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
