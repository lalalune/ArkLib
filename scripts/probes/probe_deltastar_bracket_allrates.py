#!/usr/bin/env python3
"""The machine-checked δ* bracket at ALL FOUR prize rates, and its gap scaling.

Issue #389 (claim comment 4697225967). Complementary to moon's probe_ceiling_march.py
(which does the deep-band ceiling at ρ = 1/4 only): this computes, with EXACT integer
arithmetic, the current proven bracket on δ* at every prize rate, and analyzes how the
gap scales with n — the "how close are we to pinning δ*" question.

The bracket (both sides are in-tree, axiom-clean):
  LOWER  δ_J(ρ)      = 1 − √ρ          Johnson radius (BCIKS/Hab25 MCA floor)
  UPPER  δ_ceil(n,k,q) = 1 − (k+m*+1)/n  deep-band ceiling
         (moon's mcaDeltaStar_le_of_deep_band: band m activates at ε* = 2⁻¹²⁸ iff
          ε*·q·Λ² < P·Λ/q^m, P = C(n,k+m+1), Λ = P//q^(m+1) + C' + 2,
          C' = C(k+m+1,k+1)·C(n−(k+1),m); m* = deepest activated band)
  REF    δ_cap(ρ)    = 1 − ρ            capacity (excluded, strict)
  REF    KKH26 upper  = 1 − ρ − c/log₂n  the known window upper edge (Θ(1/log n) gap
          to capacity); we fit the OBSERVED ceiling's gap-to-capacity against c/log₂n.

The window is (1−√ρ, 1−ρ−Θ(1/log n)). δ* lies strictly inside. We report, per rate and n:
  bracket [δ_J, δ_ceil], its width, whether non-empty (δ_ceil > δ_J), the ceiling's
  gap-to-capacity g = (1−ρ) − δ_ceil, and g·log₂n (constant ⟺ ceiling tracks KKH26).

Exact integers for the activation; floats only for √ρ display and the scaling fit.
"""

from math import comb, log2

EPS_SHIFT = 128  # ε* = 2^−128, used as the exact integer relation lhs < rhs<<128


def deepest_band(n, k, q):
    """The deepest band m whose deep-band failure activates the δ* ceiling at ε*=2⁻¹²⁸.
    Exact integer test: ε*·q·Λ² < P·Λ/q^m  ⟺  q·Λ² < (P·Λ // q^m) << 128."""
    best = None
    for m in range(0, n - k - 1):
        a = k + m + 1
        if a > n:
            break
        P = comb(n, a)
        Cp = comb(a, k + 1) * comb(n - (k + 1), m)
        Lam = P // q ** (m + 1) + Cp + 2
        lhs = q * Lam * Lam
        rhs = (P * Lam) // q ** m
        if rhs == 0:
            continue
        if lhs < rhs << EPS_SHIFT:
            best = m
    return best


RATES = [("1/2", 1, 2), ("1/4", 1, 4), ("1/8", 1, 8), ("1/16", 1, 16)]


def run():
    print("δ* BRACKET at ε* = 2⁻¹²⁸ — all four prize rates "
          "(exact-integer deep-band activation)\n")
    # q regimes: n^2 (poly), n^3 (poly), and a 2^256-shaped large field
    for (rlabel, rn, rd) in RATES:
        rho = rn / rd
        d_J = 1 - rho ** 0.5
        d_cap = 1 - rho
        print(f"═══ rate ρ = {rlabel}  (Johnson 1−√ρ = {d_J:.4f}, capacity 1−ρ = {d_cap:.4f}) ═══")
        print(f"{'n':>6} {'q':>7} {'m*':>4} {'δ_ceil':>8} {'bracket [δ_J,δ_ceil]':>22} "
              f"{'width':>7} {'gap2cap g':>10} {'g·log₂n':>8}")
        for mu in range(6, 11):
            n = 1 << mu
            k = n * rn // rd
            if k < 1:
                continue
            for qlabel, q in [("n²", n * n), ("n³", n ** 3)]:
                m = deepest_band(n, k, q)
                if m is None:
                    print(f"{n:>6} {qlabel:>7} {'—':>4}  (no band activates)")
                    continue
                a = k + m + 1
                d_ceil = 1 - a / n
                width = d_ceil - d_J
                g = d_cap - d_ceil
                glogn = g * log2(n)
                ne = "" if d_ceil > d_J else "  ✗EMPTY"
                print(f"{n:>6} {qlabel:>7} {m:>4} {d_ceil:>8.4f} "
                      f"[{d_J:>6.4f}, {d_ceil:>6.4f}]{'':>5} {width:>7.4f} "
                      f"{g:>10.4f} {glogn:>8.3f}{ne}")
        print()
    print("Reading: width > 0 ⟹ bracket non-empty (δ* genuinely bracketed inside the "
          "window). g·log₂n roughly constant in n ⟹ the deep-band ceiling tracks the "
          "KKH26 capacity-side bound 1−ρ−Θ(1/log n) — i.e. the UPPER side is essentially "
          "at the known frontier and the remaining open content is the lower bound in "
          "the window. g·log₂n growing ⟹ the ceiling is looser than KKH26 (more upper-"
          "side room). All bounds are in-tree axiom-clean; this is calibration only.")


if __name__ == "__main__":
    run()
