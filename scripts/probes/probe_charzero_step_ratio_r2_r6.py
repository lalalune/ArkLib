#!/usr/bin/env python3
"""Exact one-sweep check for the char-0 step-ratio gaps r=2..6.

This is a probe companion to Frontier/_CharZeroStepRatioMonotone.lean.  It uses the
landed closed-form polynomials E_2..E_8 and checks

    (2r+3) E_{r+1}(n)^2 - (2r+1) E_r(n) E_{r+2}(n) >= 0

on representative 2-power/proper-subgroup sizes.  It is not a CORE claim and does
not touch the cliff/capacity face.
"""
from __future__ import annotations


def E(r: int, n: int) -> int:
    if r == 2:
        return 3*n**2 - 3*n
    if r == 3:
        return 15*n**3 - 45*n**2 + 40*n
    if r == 4:
        return 105*n**4 - 630*n**3 + 1435*n**2 - 1155*n
    if r == 5:
        return 945*n**5 - 9450*n**4 + 39375*n**3 - 77175*n**2 + 57456*n
    if r == 6:
        return 10395*n**6 - 155925*n**5 + 1022175*n**4 - 3534300*n**3 + 6246471*n**2 - 4370520*n
    if r == 7:
        return 135135*n**7 - 2837835*n**6 + 26801775*n**5 - 141891750*n**4 + 433726293*n**3 - 708996288*n**2 + 471556800*n
    if r == 8:
        return (
            2027025*n**8 - 56756700*n**7 + 728377650*n**6 - 5439183750*n**5
            + 25055875845*n**4 - 69934975110*n**3 + 107438611995*n**2 - 68492499075*n
        )
    raise ValueError(r)


def gap(r: int, n: int) -> int:
    return (2*r + 3) * E(r + 1, n) ** 2 - (2*r + 1) * E(r, n) * E(r + 2, n)


def main() -> None:
    sizes = [8, 16, 32, 64, 128, 256]
    for n in sizes:
        row = []
        for r in range(2, 7):
            g = gap(r, n)
            assert g >= 0, (r, n, g)
            row.append(f"r={r}:gap>0 digits={len(str(g))}")
        print(f"n={n}: " + "; ".join(row))
    print("PASS: char-0 step-ratio monotonicity gaps are positive for r=2..6 on one exact 2-power sweep")


if __name__ == "__main__":
    main()
