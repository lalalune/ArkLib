#!/usr/bin/env python3
"""Falsify-first probe: does PAIRWISE capacity suffice for 3+ generator
packing? (issue #232; O119's named next (a)).

Question: given divisor multiplicities (a_d)_{d in D}, D = distinct divisors
of n, is the family packable (all cosets pairwise disjoint, canonical bases)
iff every PAIR (d, d') satisfies the O119 ceiling bound
        ceil(a_d / m) + ceil(a_{d'} / m') <= G(d, d')          (P2)
(plus singleton feasibility a_d <= n/d)?

DCS folklore says NO for general disjoint covering systems; this probe finds
whether a witness exists among canonical coset families at two-prime-smooth n.

Also tests the natural STRONGER candidate, the fractional/volume bound: can
failure be explained by sum_d a_d * d > n (volume) plus pairwise?  I.e. find
witnesses satisfying (P2) + volume <= n but unpackable.

Method: for n in {12, 18, 24, 36}, enumerate ALL multiplicity vectors over
the divisor set (bounded by per-type max a_d <= n/d), test exact packability
by backtracking (positions decreasing-size first, prune by class structure),
and compare against (P2)+volume.  Report/store every separation.  Exit 0 iff
the run completes (separations are FINDINGS, not failures); exit 1 only on
internal inconsistency (packable but violating a proven-necessary bound).
"""
import sys
from math import gcd
from itertools import product as iproduct

FAILS = 0


def fail(msg):
    global FAILS
    FAILS += 1
    print("FAIL:", msg)


def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]


def coset(n, d, r):
    s = n // d
    return frozenset(r + j * s for j in range(d))


def ceil_div(a, m):
    return (a + m - 1) // m


def pairwise_ok(n, counts):
    ds = [d for d, a in counts.items() if a > 0]
    for d in ds:
        if counts[d] > n // d:
            return False
    for i, d in enumerate(ds):
        for dp in ds[i + 1:]:
            s, sp = n // d, n // dp
            G = gcd(s, sp)
            if ceil_div(counts[d], s // G) + ceil_div(counts[dp], sp // G) > G:
                return False
    return True


def packable(n, counts):
    """Exact backtracking over canonical bases, largest cosets first."""
    items = sorted(((d, a) for d, a in counts.items() if a > 0),
                   key=lambda x: -x[0])
    types = [d for d, a in items for _ in range(a)]

    def rec(i, used, min_base):
        if i == len(types):
            return True
        d = types[i]
        s = n // d
        # same-type symmetry: enforce increasing bases within a type run
        start = min_base if i > 0 and types[i - 1] == d else 0
        for r in range(start, s):
            c = coset(n, d, r)
            if not (c & used):
                if rec(i + 1, used | c, r + 1):
                    return True
        return False

    return rec(0, frozenset(), 0)


def run_case(n):
    ds = divisors(n)
    sep_p2 = []          # pairwise-OK + volume-OK but UNPACKABLE
    n_packable = 0
    n_tested = 0
    ranges = [range(n // d + 1) for d in ds]
    for vec in iproduct(*ranges):
        counts = dict(zip(ds, vec))
        vol = sum(d * a for d, a in counts.items())
        if vol > n:
            continue
        k = sum(1 for a in vec if a > 0)
        n_tested += 1
        p2 = pairwise_ok(n, counts)
        pk = packable(n, counts)
        if pk and not p2:
            fail(f"n={n} {counts}: packable but pairwise bound violated "
                 f"(O119 necessity broken?!)")
        if p2 and not pk and k >= 3:
            sep_p2.append(counts)
    print(f"n={n}: tested {n_tested} volume-feasible vectors; "
          f"pairwise+volume-but-unpackable (k>=3): {len(sep_p2)}")
    for w in sep_p2[:6]:
        print(f"    WITNESS: {dict((d, a) for d, a in w.items() if a)}")
    return sep_p2


def main():
    all_seps = {}
    for n in (12, 18, 24, 36):
        all_seps[n] = run_case(n)
    total = sum(len(v) for v in all_seps.values())
    if total:
        print(f"SEPARATION FOUND: pairwise capacity + volume do NOT imply "
              f"packability at k>=3 ({total} witnesses)")
    else:
        print("NO SEPARATION at tested n: pairwise + volume == packable "
              "on all k>=3 instances")
    if FAILS:
        print(f"{FAILS} FAILURES")
        return 1
    print("RUN COMPLETE")
    return 0


if __name__ == "__main__":
    sys.exit(main())
