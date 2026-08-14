#!/usr/bin/env python3
"""
#444 probe (lane dedupstrict): is the dedup `N_r < C(2m, r)` STRICT at logarithmic depth?

CONTEXT. The A3 escape question (`_CoreA3_BackwardProof.lean`, dossier sec VI lever 2 + sec IX):
`WeakestSuff` is weaker-or-equal to BCHKS 1.12, the gap being the dedup slack `Sigma_r - D >= 0`.
Whether `WeakestSuff` is a REAL escape (strictly below the wall) or EQUAL (the wall) reduces to:
**is the deduplication `D <= Sigma_r` STRICT at log depth `r ~ log n`?**

CONCRETE INSTANCE (off the analytic wall, p-INDEPENDENT). The just-landed spectrum closed form
`_SubsetSumSpectrumClosedForm` (push 89151523f) gives the EXACT distinct r-subset-sum count over the
thin dyadic group mu_n (n = 2^a, m = n/2):
    N_r(C) = sum_{k == r (mod 2), 0 <= k <= min(r, 2m - r)} C(m, k) * 2^k.
The UN-deduplicated count (every r-subset counted with multiplicity) is C(2m, r) = C(n, r).
The dedup slack is
    slack(n, r) = C(n, r) - N_r(C)   >= 0,
and the dedup is STRICT at (n, r) iff slack > 0 (i.e. some two distinct r-subsets share a sum).

This probe computes slack EXACTLY (Python big ints) over the thin tower n = 2^a, a = 3..7, at:
  - the BINDING LOG DEPTH r = a = log2(n)  (the depth that controls the prize, r ~ log n);
  - a small window around it;
and reports whether the dedup is strict there and whether the slack GROWS up the tower at r = log2 n.
NEVER n = q-1 (these are subset counts over the thin subgroup, not the full group).

A strict-and-growing slack at r = log n is in-principle the A3 "escape" direction (D strictly below
Sigma at the binding depth); a vanishing slack would mean dedup is tight there (wall). Honest either
way -- this is a finite, exact, p-independent measurement of the named open A3 quantity.
"""
from math import comb


def N_r(m, r):
    """Distinct r-subset-sum count over mu_{2m} via the just-landed closed form."""
    tot = 0
    for k in range(0, min(r, 2 * m - r) + 1):
        if (k % 2) == (r % 2):
            tot += comb(m, k) * (2 ** k)
    return tot


def report():
    print("thin tower n = 2^a, m = n/2; slack(n,r) = C(n,r) - N_r  (dedup strict iff > 0)\n")
    binding_slacks = []
    for a in range(3, 8):
        n = 2 ** a
        m = n // 2
        rlog = a  # binding log depth r = log2 n
        print(f"n = {n:>3} (a={a}, m={m}); binding log-depth r = {rlog}")
        for r in range(max(1, rlog - 2), rlog + 3):
            if r > n:
                continue
            total = comb(n, r)
            distinct = N_r(m, r)
            slack = total - distinct
            strict = slack > 0
            mark = "  <-- r=log2 n" if r == rlog else ""
            ratio = (slack / total) if total else 0.0
            print(f"    r={r:>2}: C(n,r)={total:>20}  N_r={distinct:>20}  slack={slack:>20}"
                  f"  strict={strict}  slack/total={ratio:.4f}{mark}")
            if r == rlog:
                binding_slacks.append((n, slack, total))
        print()
    print("=== binding log-depth r = log2 n, up the tower ===")
    prev = None
    grows = True
    strict_all = True
    for n, slack, total in binding_slacks:
        print(f"    n={n:>3}: slack(n, log2 n) = {slack}   (of {total})")
        if slack <= 0:
            strict_all = False
        if prev is not None and not (slack > prev):
            grows = False
        prev = slack
    print()
    print(f"VERDICT: dedup STRICT at r=log2 n for all tested n: {strict_all}")
    print(f"VERDICT: binding-depth slack GROWS up the tower:      {grows}")
    if strict_all and grows:
        print("=> the dedup D <= Sigma_r is STRICT and the slack GROWS at the binding log depth:")
        print("   the A3 WeakestSuff escape direction is NON-vacuous at r = log n (p-independent).")
    return strict_all


if __name__ == "__main__":
    import sys
    ok = report()
    sys.exit(0 if ok else 1)
