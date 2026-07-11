#!/usr/bin/env python3
"""
Probe (#444, lane risingstep): the rising-half second-difference recurrence of the char-0
subset-sum spectrum N_r = spectrumCount(m, r) of the 2-power subgroup mu_n (m = n/2).

CLAIM A (rising half, 2 <= r <= m):  N_r - N_{r-2} = C(m, r) * 2^r
    (the k=r antipodal cross-polytope term is the ONLY new term: spectrumCount filters the parity
     class k == r (mod 2); going from depth r-2 to r on the rising half adds exactly index k=r,
     since k=r-1 has the wrong parity.)

CLAIM B (parity-class partial sum):  N_r = sum_{j>=0} C(m, r-2j) * 2^{r-2j}.

Exact big-int. Thin 2-power tower m = 8,16,32,64. NEVER n = q-1 (full group / false positives).
NOT a moment/energy method: pure binomial-parity census recurrence. Does NOT close CORE.
"""
from math import comb


def spectrum_count(m, r):
    """In-tree _SubsetSumSpectrumClosedForm.spectrumCount m r."""
    s = 0
    top = min(r, 2 * m - r)
    for k in range(0, top + 1):
        if k % 2 == r % 2:
            s += comb(m, k) * (2 ** k)
    return s


def main():
    okA = True
    okB = True
    for m in [8, 16, 32, 64]:
        for r in range(2, m + 1):
            lhs = spectrum_count(m, r) - spectrum_count(m, r - 2)
            rhs = comb(m, r) * 2 ** r
            if lhs != rhs:
                okA = False
                print("FAIL A", m, r, lhs, rhs)
        for r in range(0, m + 1):
            val = sum(comb(m, r - 2 * j) * 2 ** (r - 2 * j)
                      for j in range((r // 2) + 1) if r - 2 * j >= 0)
            if val != spectrum_count(m, r):
                okB = False
                print("FAIL B", m, r)

    print("CLAIM A (N_r - N_{r-2} = C(m,r)2^r, rising half 2<=r<=m):", "PASS" if okA else "FAIL")
    print("CLAIM B (N_r = sum_j C(m,r-2j)2^{r-2j}):", "PASS" if okB else "FAIL")

    # Anchors used in the Lean brick.
    for m in [8, 16]:
        n0 = spectrum_count(m, 0)
        n2 = spectrum_count(m, 2)
        print(f"m={m}: N_0={n0} N_2={n2} C(m,2)*4={comb(m, 2) * 4} "
              f"(N_2 - N_0 = {n2 - n0})")
    print("VERDICT:", "PASS" if (okA and okB) else "FAIL")


if __name__ == "__main__":
    main()
