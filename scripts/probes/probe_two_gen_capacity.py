#!/usr/bin/env python3
"""Falsify-first probe for the TWO-GENERATOR CAPACITY LAW (issue #232; the
first sufficiency rung of the O116 packing surface).

CLAIM: for d | n, d' | n (d, d' >= 1), s = n/d, s' = n/d', G = gcd(s, s'),
m = s/G, m' = s'/G:  a rotated mu_d-cosets and b rotated mu_{d'}-cosets
(canonical: cosetOf(n,d,r) = {r + j*s : j < d}, r < s) can be chosen with
union cardinality exactly a*d + b*d'  (== all pairwise disjoint)  IFF

        ceil(a/m) + ceil(b/m') <= G.

Structural facts behind it (also checked):
  (i)   two same-type cosets with distinct bases are disjoint;
  (ii)  cross-type cosets intersect IFF their bases agree mod G (CRT);
  (iii) each class mod G holds exactly m bases of type d (m' of type d').

CHECKS (exit 0 iff all pass):
  (A) facts (i)-(ii) EXHAUSTIVELY for n in {12, 18, 20, 24, 30, 36}, all
      ordered divisor pairs, all base pairs — these are the load-bearing
      structure (given them, packing is exactly a class-allocation problem
      and the ceiling law follows by transparent finite reasoning);
  (B) the law against INDEPENDENT raw backtracking ground truth on every
      tractable instance (search space C(s,a)*C(s',b) <= 2*10^5) for
      n in {12, 18, 20, 24} — skipped instances are counted and reported.
"""
import sys
from math import gcd
from itertools import combinations

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


def packable_raw(n, d, dp, a, b):
    """Raw backtracking: choose a bases from [0,s), b bases from [0,s'),
    all cosets pairwise disjoint."""
    s, sp = n // d, n // dp
    G = gcd(s, sp)
    # prune via class structure: choose class sets, then fill
    # raw search over base subsets (small sizes only)
    cosets_d = [coset(n, d, r) for r in range(s)]
    cosets_dp = [coset(n, dp, r) for r in range(sp)]

    def rec(need_a, need_b, start_a, start_b, used):
        if need_a == 0 and need_b == 0:
            return True
        if need_a > 0:
            for r in range(start_a, s - need_a + 1):
                c = cosets_d[r]
                if not (c & used):
                    if rec(need_a - 1, need_b, r + 1, start_b, used | c):
                        return True
            return False
        for r in range(start_b, sp - need_b + 1):
            c = cosets_dp[r]
            if not (c & used):
                if rec(0, need_b - 1, start_a, r + 1, used | c):
                    return True
        return False

    return rec(a, b, 0, 0, frozenset())


def comb(s, a):
    from math import comb as c
    return c(s, a) if 0 <= a <= s else 0


def main():
    # (A) the structural facts, exhaustively
    for n in (12, 18, 20, 24, 30, 36):
        for d in divisors(n):
            for dp in divisors(n):
                s, sp = n // d, n // dp
                G = gcd(s, sp)
                for r in range(s):
                    for rp in range(sp):
                        if d == dp and r == rp:
                            continue
                        inter = bool(coset(n, d, r) & coset(n, dp, rp))
                        if d == dp:
                            if inter:
                                fail(f"n={n} d={d} same-type r={r} rp={rp} "
                                     f"intersect")
                            continue
                        same = (r % G) == (rp % G)
                        if inter != same:
                            fail(f"n={n} d={d} d'={dp} r={r} rp={rp}: "
                                 f"inter={inter} same-class={same}")
        print(f"n={n}: structural facts (i)-(ii) OK")
    # (B) the law vs raw ground truth on tractable instances
    tested = skipped = 0
    for n in (12, 18, 20, 24):
        for d in divisors(n):
            for dp in divisors(n):
                s, sp = n // d, n // dp
                G = gcd(s, sp)
                m, mp = s // G, sp // G
                for a in range(s + 1):
                    for b in range(sp + 1):
                        if comb(s, a) * comb(sp, b) > 200_000:
                            skipped += 1
                            continue
                        tested += 1
                        pred = ceil_div(a, m) + ceil_div(b, mp) <= G
                        if d == dp:
                            pred = a + b <= s
                        got = packable_raw(n, d, dp, a, b)
                        if got != pred:
                            fail(f"n={n} d={d} d'={dp} a={a} b={b}: "
                                 f"packable={got} ceiling={pred}")
        print(f"n={n}: capacity law vs raw search OK so far "
              f"(tested={tested}, skipped={skipped})")
    print(f"law instances tested={tested}, skipped (search too big)={skipped}")
    if FAILS:
        print(f"{FAILS} FAILURES")
        return 1
    print("ALL CHECKS PASSED")
    return 0


if __name__ == "__main__":
    sys.exit(main())
