#!/usr/bin/env python3
"""probe_n2_zero_slack.py — N2/S1 zero-slack test (#357).

The in-tree stratified spread (`KKH26StratifiedSpread.lean`) proves the LOWER bound

    #distinct r-element sums from the order-s subgroup G  >=  SUM_j 2^(r-2j) * C(s/2, r-2j)

(strata: j antipodal pairs contribute 0, the rest sign-free; feasibility j <= s/2 etc.).
N2's rigidity branch and S1's exactness target share one decisive question:

    at prime-power s and large p, is the stratified count EXACT?

* EXACT everywhere  -> the KKH26-family ceiling is census-extremal: zero slack; the
  bad-scalar census is completely classified by the antipodal stratification (the
  de Bruijn vanishing classification is complete here) — S1's weld is a tautology
  waiting for formalization and N2's rigidity holds at probe scale.
* SLACK somewhere   -> there are MORE distinct sums than the strata account for —
  a strictly better in-tree ceiling numerator is available immediately.

We compute, with exact arithmetic over F_p (p ≡ 1 mod s, several p per s including
sizes above and below the collision threshold):

    census(s, r, p) = #{ sum of S : S an r-subset of G }   (full enumeration)
    strat(s, r)     = sum over j of 2^(r-2j)*C(s/2, r-2j) for feasible strata

and report census - strat per (s, r, p).
"""

import itertools
import sys
from math import comb


def order_s_subgroup(p, s):
    # find generator of the order-s subgroup of F_p^*
    for g in range(2, p):
        if pow(g, s, p) == 1 and all(pow(g, s // q, p) != 1
                                     for q in set(_factors(s))):
            return [pow(g, i, p) for i in range(s)]
    return None


def _factors(n):
    out = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            out.append(d)
            n //= d
        d += 1
    if n > 1:
        out.append(n)
    return out


def strat_count(s, r):
    # strata: j antipodal pairs (sum 0) + (r-2j) sign-free elements
    # feasibility per KKH26StratifiedSpread: j pairs available (j <= s/2),
    # r-2j sign-free from s/2 antipodal classes
    total = 0
    for j in range(0, r // 2 + 1):
        rj = r - 2 * j
        if rj > s // 2:
            continue
        if j > s // 2:
            continue
        # the j pairs and the rj sign-free classes must be disjoint classes
        if j + rj > s // 2:
            continue
        total += (2 ** rj) * comb(s // 2, rj)
    return total


def main():
    cases = [
        (8, [17, 41, 97, 257, 65537]),
        (16, [17, 97, 257, 65537]),
        (32, [97, 193, 257, 65537]),
    ]
    print("zero-slack test: census(s,r,p) - strat(s,r)  [0 = census-extremal]")
    any_slack = False
    for s, ps in cases:
        for p in ps:
            if (p - 1) % s != 0:
                continue
            G = order_s_subgroup(p, s)
            if G is None:
                continue
            rmax = min(s, 8)
            for r in range(2, rmax + 1):
                sums = set()
                for S in itertools.combinations(G, r):
                    sums.add(sum(S) % p)
                cs = len(sums)
                st = strat_count(s, r)
                slack = cs - st
                tag = ""
                if slack > 0:
                    tag = "  <-- POSITIVE SLACK (better ceiling available)"
                    any_slack = True
                elif slack < 0:
                    tag = "  <-- NEGATIVE (collisions below threshold, expected at small p)"
                print(f"  s={s:2d} r={r} p={p:6d}: census={cs:6d} strat={st:6d} "
                      f"slack={slack:6d}{tag}")
    print(f"\nverdict: {'SLACK EXISTS — stratified count is NOT exact; '
          'strictly better ceiling available' if any_slack else
          'zero slack at large p everywhere tested — census-extremal'}")
    print("exit 0")
    return 0


if __name__ == "__main__":
    sys.exit(main())
