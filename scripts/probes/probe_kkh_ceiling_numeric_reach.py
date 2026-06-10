#!/usr/bin/env python3
"""Numeric reach of the in-tree KKH26 ceiling (kkh26_mcaDeltaStar_le) at
Proximity Prize parameters.

The formalized theorem (ArkLib/Data/CodingTheory/ProximityGap/KKH26WitnessSpread.lean)
gives, for the explicit evaluation code of degree <= (r-2)*m on the smooth
n = s*m point domain (s = 2^mu), with prime field size p:

    mcaDeltaStar(C, eps*) <= 1 - r/s    whenever
        (A)  p > s^(s/2)                 [explicit prime threshold of kkh26_lemma1]
        (B)  eps* < 2^r * C(s/2, r) / p  [bad-scalar mass beats the target]
        (C)  2 <= r <= s/2

This probe answers, with exact integer arithmetic: for the prize target
eps* = 2^-128 and prize rates rho in {1/2, 1/4, 1/8, 1/16}, for which
(s, |F|) does the in-tree ceiling actually bite?  I.e. when is the window

    s^(s/2) < p < min( 2^r * C(s/2,r) * 2^128 , 2^256 )

nonempty, with r pinned by the rate ((r-2)/s = rho, so r = rho*s + 2)?

It also brute-force cross-validates the count lower bound of kkh26_lemma1
at small parameters against real prime-field arithmetic (negative control:
the bound must hold with genuine sums of distinct subgroup elements).

Exit 0 iff all assertions pass.  Findings are printed as a table.
"""

from math import comb
from itertools import combinations

EPS_STAR_EXP = 128          # eps* = 2^-128
PRIZE_FIELD_CAP_EXP = 256   # |F| < 2^256
RATES = [(1, 2), (1, 4), (1, 8), (1, 16)]


def bitlen(x: int) -> int:
    return x.bit_length()


def brute_validate_lemma1() -> None:
    """Brute-force check of the kkh26_lemma1 count bound at small parameters.

    s = 4 (mu = 2), threshold s^(s/2) = 16.  Take p = 29 (prime, p = 1 mod 4,
    p > 16) and g = 12, which has order 4 in F_29 (12^2 = 144 = -1 mod 29).
    The lemma asserts: sums of r distinct elements of G = <g> take at least
    2^r * C(s/2, r) distinct values, for 2 <= r <= s/2 = 2.
    """
    p, s = 29, 4
    assert pow(12, 2, p) == p - 1 and pow(12, 4, p) == 1, "g=12 must have order 4"
    G = sorted({pow(12, i, p) for i in range(s)})
    assert len(G) == s
    for r in range(2, s // 2 + 1):
        sums = {sum(c) % p for c in combinations(G, r)}
        bound = (2 ** r) * comb(s // 2, r)
        assert len(sums) >= bound, (
            f"lemma1 violated at p={p}, s={s}, r={r}: {len(sums)} < {bound}")
    # second instance: s = 8 (mu = 3), threshold 8^4 = 4096; p = 12289 = 1 + 3*2^12
    # is prime with 2^12 | p-1, so an order-8 element exists.
    p2, s2 = 12289, 8
    g2 = None
    for cand in range(2, 200):
        h = pow(cand, (p2 - 1) // s2, p2)  # h^8 = 1; order exactly 8 iff h^4 != 1
        if pow(h, s2 // 2, p2) != 1:
            g2 = h
            break
    assert g2 is not None, "no order-8 element found in F_12289"
    assert p2 > s2 ** (s2 // 2)
    G2 = sorted({pow(g2, i, p2) for i in range(s2)})
    assert len(G2) == s2
    for r in range(2, s2 // 2 + 1):
        sums = {sum(c) % p2 for c in combinations(G2, r)}
        bound = (2 ** r) * comb(s2 // 2, r)
        assert len(sums) >= bound, (
            f"lemma1 violated at p={p2}, s={s2}, r={r}: {len(sums)} < {bound}")
    print("brute validation: kkh26_lemma1 count bound holds at (p,s) in "
          "{(29,4),(12289,8)} for all admissible r  [OK]")


def reach_table() -> None:
    print()
    print("Numeric reach of kkh26_mcaDeltaStar_le at eps* = 2^-128, |F| < 2^256")
    print(f"{'mu':>3} {'s':>5} {'rate':>5} {'r':>5} {'delta_bad':>10} "
          f"{'log2 s^(s/2)':>13} {'log2 count':>11} {'field window (log2 |F|)':>26}")
    any_nonempty = False
    for mu in range(2, 13):
        s = 2 ** mu
        half = s // 2
        thr_exp = half * mu  # exact: log2(s^(s/2))
        assert (s ** half).bit_length() - 1 == thr_exp  # exact power of two check
        for a, b in RATES:
            if (s * a) % b != 0:
                print(f"{mu:>3} {s:>5} {a}/{b:<3} {'-':>5} {'-':>10} {thr_exp:>13} "
                      f"{'-':>11} {'rate not integral at this s':>26}")
                continue
            r = (s * a) // b + 2
            if not (2 <= r <= half):
                print(f"{mu:>3} {s:>5} {a}/{b:<3} {r:>5} {'-':>10} {thr_exp:>13} "
                      f"{'-':>11} {'unreachable: r > s/2':>26}")
                continue
            count = (2 ** r) * comb(half, r)
            count_exp = bitlen(count) - 1  # floor(log2 count)
            upper_exp = min(count_exp + EPS_STAR_EXP, PRIZE_FIELD_CAP_EXP)
            nonempty = thr_exp < upper_exp
            any_nonempty = any_nonempty or nonempty
            delta_bad = f"1-{r}/{s}"
            window = (f"({thr_exp}, {upper_exp})  NONEMPTY" if nonempty
                      else f"({thr_exp}, {upper_exp})  empty")
            print(f"{mu:>3} {s:>5} {a}/{b:<3} {r:>5} {delta_bad:>10} {thr_exp:>13} "
                  f"{count_exp:>11} {window:>26}")
    assert any_nonempty, "expected at least one nonempty reach window"
    print()
    print("Reading: NONEMPTY rows are (s, rate) pairs where the in-tree theorem")
    print("already pins mcaDeltaStar <= 1 - r/s (just below capacity 1 - rate)")
    print("for every prime field in the stated log2-size window.  Empty rows")
    print("quantify exactly what the externals (Thorner-Zaman polynomial field")
    print("sizes, replacing the explicit s^(s/2) threshold) would buy: the lower")
    print("window edge would drop from (s/2)*mu bits to O(beta*log2 n) bits.")
    print("Rate-1/2 rows are unreachable at every finite s: r = s/2 + 2 > s/2;")
    print("the construction's rate is intrinsically <= 1/2 - 2/s.")


def monotonicity_control() -> None:
    """Negative control: the count 2^r * C(s/2,r) must be unimodal in r and the
    stated peak must dominate the rate-pinned value (sanity of the table)."""
    for mu in (4, 6, 8):
        s = 2 ** mu
        half = s // 2
        counts = [(2 ** r) * comb(half, r) for r in range(2, half + 1)]
        peak = max(counts)
        # unimodal: increases to peak then decreases
        k = counts.index(peak)
        assert all(counts[i] <= counts[i + 1] for i in range(k)), "not increasing to peak"
        assert all(counts[i] >= counts[i + 1] for i in range(k, len(counts) - 1)), \
            "not decreasing after peak"
        # the peak sits near r = s/3 (the (1+2)^(s/2) binomial dominant term)
        r_peak = k + 2
        assert abs(r_peak - s // 3) <= max(2, s // 16), \
            f"peak location {r_peak} far from s/3 = {s // 3}"
    print("monotonicity control: count is unimodal with peak near r = s/3  [OK]")


if __name__ == "__main__":
    brute_validate_lemma1()
    monotonicity_control()
    reach_table()
    print("\nall assertions passed")
