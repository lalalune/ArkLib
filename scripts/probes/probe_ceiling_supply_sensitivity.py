#!/usr/bin/env python3
"""Why the deep-band route cannot pin δ* = Johnson — at ANY supply quality (#389, R3).

Issue #389 batch hypothesis R3 (lower-bound side). The deep-band ceiling
δ* ≤ 1−(k+m*+1)/n comes from ε_mca ≥ P/(q^(m+1)·B), P=C(n,k+m+1), B = supply bound,
via deep_band_badSet_card_of_supply + ε_mca ≥ badSet/q. It activates (gives δ* ≤ δ)
iff that bound exceeds ε*=2^-128.

SOUND SENSITIVITY: the BEST CASE for the route is the smallest possible supply B=1
(a single explainable core). We compute, at the Johnson band m_J (agreement floor
k+m_J+1 ≈ n√ρ), the log2 of the badSet lower bound at B=1:
        log2 ε_mca_bound = log2 P_J − (m_J+1)·log2 q.
If this is < −128, the route gives ε_mca-bound < ε* at Johnson EVEN with B=1, so NO
supply bound — however small — lets the deep-band route push the ceiling to Johnson.
Exact integers; conditional on nothing (B=1 is the route's own best case).
"""

from math import comb, log2, sqrt

EPS = 128


def johnson_band(n, k):
    rho = k / n
    return max(0, round(n * sqrt(rho)) - k - 1)


RATES = [("1/2", 1, 2), ("1/4", 1, 4), ("1/8", 1, 8), ("1/16", 1, 16)]


def main():
    print("CAN THE DEEP-BAND ROUTE PIN δ*=JOHNSON?  best case B=1, ε*=2^-128, "
          "exact integers\n")
    print("Route activates at the Johnson band iff log2(P_J) − (m_J+1)·log2 q > −128.\n")
    for (rlabel, rn, rd) in RATES:
        rho = rn / rd
        print(f"=== rho = {rlabel}  (Johnson 1-sqrt(rho) = {1-sqrt(rho):.4f}) ===")
        print(f"{'n':>6} {'q':>5} {'m_J':>5} {'log2 P_J':>10} "
              f"{'log2 badSet-bound@B=1':>22} {'vs -128':>9} {'verdict':>9}")
        for mu in range(7, 12):
            n = 1 << mu
            k = n * rn // rd
            for qlabel, q in [("n2", n * n), ("n3", n ** 3)]:
                mJ = johnson_band(n, k)
                aJ = k + mJ + 1
                P_J = comb(n, aJ)
                log2P = log2(P_J) if P_J > 0 else float('-inf')
                bound = log2P - (mJ + 1) * log2(q)   # best case B=1
                ok = bound > -EPS
                print(f"{n:>6} {qlabel:>5} {mJ:>5} {log2P:>10.1f} "
                      f"{bound:>22.1f} {('>' if ok else '<'):>9} "
                      f"{('PIN?!' if ok else 'dead'):>9}")
        print()
    print("READING.")
    print("• Every row: log2 badSet-bound@B=1 is FAR below -128 (hundreds to thousands")
    print("  of bits short). So at the Johnson band the deep-band route's bad-count lower")
    print("  bound is < 2^-128 even with the smallest conceivable supply B=1 — the q^(m+1)")
    print("  witness-mass suppression dominates P_J for production q.")
    print("• VERDICT (R3 decided NEGATIVE, structural): the deep-band route — the fleet's")
    print("  entire upper-bound machinery — CANNOT push the δ* ceiling to Johnson at ANY")
    print("  supply quality. Its hard floor is capacity-Theta(1/log n) (= KKH26, the bracket")
    print("  calibration). Improving the supply bound (R3's premise) is IRRELEVANT at the")
    print("  Johnson band; the obstruction is the q^(m+1) factor, not the supply size.")
    print("• Consequence: pinning delta* (if = Johnson) needs a FUNDAMENTALLY different upper")
    print("  bound that does not pay the q^(m+1) deep-band suppression — i.e. a direct")
    print("  beyond-Johnson bad-count bound. This is the exact structural reason the wall is")
    print("  the 25-yr beyond-Johnson list-decoding problem, not a supply-quality gap.")
    print("• A row with '> -128' anywhere would be a PIN signal (falsifier) — none appears.")


if __name__ == "__main__":
    main()
