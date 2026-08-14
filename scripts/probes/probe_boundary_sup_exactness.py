#!/usr/bin/env python3
"""
probe_boundary_sup_exactness.py -- #357 closing-audit item 4, boundary half.

PRE-REGISTERED HYPOTHESES (2026-06-11, registered before computation; follows
probe_strip_sup_exactness.py whose criterion is word-level-validated at d=5 and d=6):

  H-D (boundary law, sup side): at the band-3 boundary row (d = 5, e = 2), the EXACT
      max over all pencils of the bad-scalar count is n - [3 does not divide n]:
        cell C1 (n=8,  k=4, q=17, d=5): max N = 7   [3 nmid 8; fleet stratum scan: 7]
        cell C2 (n=9,  k=5, q=19, d=5): max N = 9   [3 | 9 -> n; new cell, untested
                                                     n ≡ 0 (mod 3) beyond n=6,12]
        cell C3 (n=12, k=8, q=13, d=5): max N = 12  [3 | 12; fleet coset-triangle probe
                                                     verified 12 -- cross-check]
  H-E (structure): every maximizer decomposes into "clusters" -- maximal
      overlap-connected sub-families -- each living on a 3-point set with <= 3 scalars
      (the coset/generic triangles), plus at most one extra pair when 3 nmid n.

Method identical to probe_strip_sup_exactness.py (exact arithmetic, syndrome
reduction, unique-rep regime 2e = 4 < 5 = d, two-ball-point line enumeration =
exhaustive for max over all pencils up to affine reparametrization).
"""

import sys

sys.path.insert(0, "scripts/probes")
from probe_strip_sup_exactness import run_cell  # noqa: E402

import json  # noqa: E402


def main():
    results = []
    results.append(run_cell("C1", 8, 4, 17, 2, expected=7))
    results.append(run_cell("C2", 9, 5, 19, 2, expected=9))
    results.append(run_cell("C3", 12, 8, 13, 2, expected=12))
    with open("scripts/probes/boundary_sup_exactness_results.json", "w") as f:
        json.dump(results, f, indent=1)
    print("done.")


if __name__ == "__main__":
    main()
