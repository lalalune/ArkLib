#!/usr/bin/env python3
"""Probe: di Benedetto edge-saving SENSITIVITY / t3-dominance (#444, lane dbsens).

diBenedettoSaving(t2,t3) = (10 - 2*t3 - t2/2)/72  [ArkLib _DiBenedettoNearSidonImprovement].

The parent file's docstring asserts (prose only) "t3 is the dominant input (sensitivity -2/72,
four times t2's -1/144)". This probe confirms, EXACTLY (rational arithmetic), the per-unit
sensitivities and the 4x dominance, for ALL (t2,t3) (the saving is affine, so finite differences
equal the slopes). VERDICT: PASS.

NOT a CORE move: this is energy-method lever-selection bookkeeping. The energy family is capped at
saving <= 1/24 < 1/2 (the prize cancellation exponent), proven in the parent file. cliff-at-n/2
(the delta*/incidence object) UNTOUCHED.
"""
from fractions import Fraction as F


def sav(t2: F, t3: F) -> F:
    return (F(10) - 2 * t3 - t2 / 2) / 72


def main() -> None:
    T2 = [F(2), F(49, 20), F(5), F(3)]
    T3 = [F(3), F(4), F(7, 2), F(9, 2)]
    ok = True
    for t2 in T2:
        for t3 in T3:
            d_t3 = sav(t2, t3) - sav(t2, t3 + 1)   # per-unit t3 DECREASE
            d_t2 = sav(t2, t3) - sav(t2 + 1, t3)   # per-unit t2 DECREASE
            assert d_t3 == F(1, 36), (t2, t3, d_t3)
            assert d_t2 == F(1, 144), (t2, t3, d_t2)
            assert d_t3 == 4 * d_t2, (t2, t3)
            # absolute slopes (one-unit INCREASE lowers the saving)
            assert sav(t2, t3 + 1) - sav(t2, t3) == F(-1, 36)
            assert sav(t2 + 1, t3) - sav(t2, t3) == F(-1, 144)
    # anchor values from the parent file
    assert sav(F(49, 20), F(4)) == F(31, 2880)    # baseline
    assert sav(F(2), F(3)) == F(1, 24)            # near-Sidon
    print("PASS: per-unit t3-decrease = 1/36, t2-decrease = 1/144, ratio = 4 (EXACT, all t2,t3).")
    print("PASS: absolute slopes -1/36 (t3), -1/144 (t2); baseline 31/2880, near-Sidon 1/24.")
    print("t3-dominance confirmed: lowering E3 exponent is the 4x-dominant edge-saving lever.")
    assert ok


if __name__ == "__main__":
    main()
