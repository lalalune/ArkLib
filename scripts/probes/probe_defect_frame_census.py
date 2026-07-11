#!/usr/bin/env python3
"""
probe_defect_frame_census.py -- #357 sup-exactness lane: the GP-triangle falsifier.

PRE-REGISTERED HYPOTHESIS (2026-06-12, before computation):
  H-F: at the first defect cell (n=8, k=4, q=17, d=5, e=2), the 3-point frames
  occurring in the N = 7 (= n-1) maximizers are exactly the multiplicative
  geometric-progression triples in domain values, T = c*{1, t, t^2} (t != 0,1),
  up to the inverse-pair/leftover structure -- the natural 3-nmid-n generalization
  of the 3|n coset triangles (where t would be a cube root of unity).

Method: rerun the exhaustive two-ball-point sweep (criterion as in
probe_strip_sup_exactness.py, word-level validated there), and for every line with
7 bad scalars decompose the 7 supports into overlap-connected clumps; census the
3-point frame index-sets; test each occurring frame for the GP property in domain
values; also census the leftover 2-sets (inverse pairs?).
"""

import itertools
import sys
from collections import Counter

sys.path.insert(0, "scripts/probes")
from probe_strip_sup_exactness import Cell  # noqa: E402


def clumps(supports):
    """Overlap-connected components of a list of index-sets."""
    comps = []
    for s in supports:
        s = set(s)
        merged = [s]
        rest = []
        for c in comps:
            if c & s:
                merged.append(c)
            else:
                rest.append(c)
        comps = rest + [set().union(*merged)]
    return comps


def main():
    n, k, p, e = 8, 4, 17, 2
    cell = Cell(n, k, p, e)
    cell.build_ball()
    maxN, winners = cell.sweep(report_at=7)
    print(f"max N = {maxN}, winners (N >= 7): {len(winners)}")
    frame3 = Counter()
    frame2 = Counter()
    profiles = Counter()
    for (t1, t2, gs) in winners:
        desc = cell.describe(t1, t2, gs)
        sups = [tuple(x["support"]) for x in desc]
        cs = clumps(sups)
        profiles[tuple(sorted(len(c) for c in cs))] += 1
        for c in cs:
            if len(c) == 3:
                frame3[tuple(sorted(c))] += 1
            elif len(c) == 2:
                frame2[tuple(sorted(c))] += 1
    print("clump size profiles:", dict(profiles))
    dom = cell.dom
    print(f"domain: {dom}")

    def is_gp(tri):
        vals = [dom[i] for i in tri]
        for perm in itertools.permutations(vals):
            a, b, c = perm
            # b/a == c/b  <=>  b^2 == a*c (mod p)
            if (b * b - a * c) % p == 0:
                return True
        return False

    def is_invpair(pair):
        a, b = (dom[i] for i in pair)
        return (a * b - 1) % p == 0 or (a * b + 1) % p == 0

    print(f"\n3-frames occurring ({len(frame3)} distinct of {35+21} possible):")
    gp_yes = gp_no = 0
    for T, cnt in sorted(frame3.items(), key=lambda kv: -kv[1]):
        g = is_gp(T)
        gp_yes += g
        gp_no += not g
        print(f"  {T} vals={[dom[i] for i in T]} count={cnt} GP={g}")
    print(f"GP frames: {gp_yes}, non-GP frames: {gp_no}")
    print(f"\nleftover 2-sets ({len(frame2)} distinct):")
    for P, cnt in sorted(frame2.items(), key=lambda kv: -kv[1]):
        print(f"  {P} vals={[dom[i] for i in P]} count={cnt} "
              f"invpair={is_invpair(P)}")
    verdict = "CONFIRMED" if gp_no == 0 and gp_yes > 0 else "REFUTED"
    print(f"\nH-F (all frames are GP triples): {verdict}")


if __name__ == "__main__":
    main()
