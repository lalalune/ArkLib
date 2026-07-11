#!/usr/bin/env python3
"""Probe (#444): the TOTAL char-0 subset-sum spectrum mass of the 2-power subgroup mu_n.

Extends _SubsetSumSpectrumClosedForm.spectrumCount (the per-depth count
  N_r = sum_{k == r (2), k <= min(r, 2m-r)} C(m,k) * 2^k,  m = n/2)
to the TOTAL over all depths r = 0..2m:

  T(m) := sum_{r=0}^{2m} N_r  =  3^(m-1) * (m+3).

Mechanism (depth-multiplicity reindex, NOT a moment method): a net-vector class with k nonzeros
(contributing C(m,k)*2^k) is reachable at depth r iff k == r (2) and k <= r <= 2m-k, i.e. at
exactly (m-k+1) depths. Hence
  T(m) = sum_k (m-k+1) C(m,k) 2^k
       = (m+1) sum_k C(m,k) 2^k  -  sum_k k C(m,k) 2^k
       = (m+1) 3^m  -  2m 3^(m-1)        [the two binomial GF sums]
       = 3^(m-1) (m+3).

VERDICT: PASS iff all three forms (direct double sum, k-form, closed form) agree on n=2..2*MMAX.
NEVER validated at n=q-1 (this is a pure char-0 count identity; no field/prime involved).
Issue #444. Co-authored-by: wakesync <shadow@shad0w.xyz>
"""
from math import comb

MMAX = 40  # n up to 80


def spectrum_count(m, r):
    """N_r = distinct complex subset sums of size-r subsets of mu_n (n=2m)."""
    hi = min(r, 2 * m - r)
    return sum(comb(m, k) * 2 ** k for k in range(hi + 1) if k % 2 == r % 2)


def total_direct(m):
    return sum(spectrum_count(m, r) for r in range(2 * m + 1))


def total_kform(m):
    return sum((m - k + 1) * comb(m, k) * 2 ** k for k in range(m + 1))


def total_closed(m):
    return 3 ** (m - 1) * (m + 3)


def main():
    ok = True
    # component GF identities
    for m in range(1, MMAX + 1):
        a = sum(comb(m, k) * 2 ** k for k in range(m + 1))
        b = sum(k * comb(m, k) * 2 ** k for k in range(m + 1))
        if a != 3 ** m or b != 2 * m * 3 ** (m - 1):
            print(f"GF FAIL at m={m}: sumC2^k={a} (want {3**m}), sumkC2^k={b}")
            ok = False
    # total mass three-way agreement
    for m in range(1, MMAX + 1):
        td, tk, tc = total_direct(m), total_kform(m), total_closed(m)
        if not (td == tk == tc):
            print(f"TOTAL FAIL at m={m} (n={2*m}): direct={td} kform={tk} closed={tc}")
            ok = False
    # spot anchors used in the Lean file
    anchors = {1: 4, 2: 15, 3: 54, 4: 189, 8: 24057}
    for m, want in anchors.items():
        if total_direct(m) != want:
            print(f"ANCHOR FAIL m={m}: {total_direct(m)} != {want}")
            ok = False
    print("VERDICT:", "PASS" if ok else "FAIL")
    print("Examples: T(1)=4 T(2)=15 T(3)=54 T(4)=189 T(8)=3^7*11=24057")


if __name__ == "__main__":
    main()
