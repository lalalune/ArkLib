#!/usr/bin/env python3
"""
probe_defect_joint_census.py -- #357 sup-exactness lane: the JOINT clump-triple census.

RESULT (2026-06-12, exhaustive at (8,4,17)): all 177,408 maximal (N = n-1 = 7) pencils
fall into EXACTLY 24 joint clump-structures with EXACTLY 7392 occurrences each
(24 * 7392 = 177,408 -- perfect uniformity), every one of the same shape:

  THE ARC-TILING LAW: {arc triangle {i,i+1,i+2}} (consecutive generator powers --
  automatically a ratio-g geometric progression; the true content of the marginal
  census's "GP frames") + {near-arc triangle {j,j+1,j+3}} + {complementary pair},
  an exact tiling of Z_n in index space.  24 = 8 rotations x 3 layout classes.

Consequence: the general 3-nmid-n defect certificate (the >= (n-1)/q half against the
landed <= n-1, BoundaryDefectBound.lean) should be built from per-arc degenerate
pencils (shift/difference families on consecutive Vandermonde columns).  Next
falsifier: the same census at an n = 10 cell (3 triangles + leftover point predicted).
"""

import itertools
import sys
from collections import Counter

sys.path.insert(0, "scripts/probes")
from probe_strip_sup_exactness import Cell  # noqa: E402
from probe_defect_frame_census import clumps  # noqa: E402


def main():
    n, k, p, e = 8, 4, 17, 2
    cell = Cell(n, k, p, e)
    cell.build_ball()
    maxN, winners = cell.sweep(report_at=n - 1)
    print(f"max N = {maxN}, winners (N >= {n-1}): {len(winners)}")
    joint = Counter()
    for (t1, t2, gs) in winners:
        desc = cell.describe(t1, t2, gs)
        cs = clumps([tuple(x["support"]) for x in desc])
        joint[frozenset(frozenset(c) for c in cs)] += 1
    print("distinct joint clump-structures:", len(joint))
    dom = cell.dom

    def gp(tri):
        vals = [dom[i] for i in tri]
        return any((b * b - a * c) % p == 0
                   for a, b, c in itertools.permutations(vals))

    for st, cnt in sorted(joint.items(), key=lambda kv: -kv[1]):
        parts = sorted([tuple(sorted(c)) for c in st], key=len)
        tag = [("P" if len(q) == 2 else ("GP" if gp(q) else "mx"))
               for q in parts]
        print(f"  count={cnt}: {parts} {tag}")


if __name__ == "__main__":
    main()
