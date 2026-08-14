#!/usr/bin/env python3
"""
probe_r2_unfolded_floor.py  (#407, R2 / CZ25 subspace-design route)

Numeric corroboration of the proven structural floor in
  ArkLib/Data/CodingTheory/ProximityGap/Frontier/R2UnfoldedDesignFloor.lean

CLAIM (proven, axiom-clean): For UNFOLDED (s = 1) RS — the prize target, scalar
alphabet — any tau-subspace-design with an m-dimensional subcode has
  tau(r) >= (m - 1)/m   for all r >= m
("free vanishing of one scalar coordinate": range(eval_i) <= F has dim <= 1, so
 by rank-nullity dim(A cap ker eval_i) >= dim A - 1 at EVERY coordinate).

CONSEQUENCE for the CZ25 capacity radius  delta = 1 - tau(r0) - eta,  r0 = floor(1/eta):
  - r0 = 1 (eta in (1/2, 1]): tau(1) floor = 0,  delta <= 1 - eta < 1/2.
  - r0 >= 2 (eta in (1/(r0+1), 1/r0]): an r0-dim subcode (k >= r0) forces
    tau(r0) >= (r0-1)/r0, so delta <= 1/r0 - eta < 1/r0 - 1/(r0+1) = 1/(r0(r0+1)).

So sup over all eta of the unfolded-R2 certified radius is < 1/2 (only at r0=1),
and < 1/6 for r0 >= 2 — INDEPENDENT of rho. This is strictly below the prize
window UPPER edge (capacity 1-rho) for every prize rate, and below the window
LOWER edge (1-sqrt(rho)) for rho in {1/8, 1/16}.

This probe prints the exact bracket and the window comparison per prize rate.
Pure python3, no sympy.
"""

import math

PRIZE_RATES = [0.5, 0.25, 0.125, 0.0625]   # 1/2, 1/4, 1/8, 1/16


def unfolded_radius_sup_at(r0: int) -> float:
    """sup over eta in (1/(r0+1), 1/r0] of the certified radius 1/r0 - eta."""
    eta_inf = 1.0 / (r0 + 1)
    if r0 == 1:
        # tau(1) floor is 0 (1-dim subcode contributes >= 0), radius <= 1 - eta;
        # eta in (1/2, 1], sup at eta -> 1/2+: radius -> 1/2-.
        return 1.0 - eta_inf  # = 1/2
    # tau(r0) >= (r0-1)/r0 (r0-dim subcode), radius <= 1/r0 - eta.
    return 1.0 / r0 - eta_inf  # = 1/(r0(r0+1))


def main():
    print("=== R2 unfolded (s=1) certified-radius bracket per r0 ===")
    best = 0.0
    for r0 in range(1, 9):
        sup = unfolded_radius_sup_at(r0)
        closed = 1.0 / (r0 * (r0 + 1)) if r0 >= 2 else 0.5
        ok = abs(sup - closed) < 1e-12
        best = max(best, sup)
        print(f"  r0={r0}:  sup radius = {sup:.6f}  (= 1/(r0(r0+1))={closed:.6f}) [{ok}]")
    print(f"\n  sup over ALL eta of unfolded-R2 radius = {best:.6f}  (attained only at r0=1)")

    print("\n=== window comparison per prize rate (unfolded radius STRICTLY < 1/2) ===")
    # The sup 1/2 is NOT attained (r0=1 needs eta>1/2, radius=1-eta<1/2 strictly).
    # So the certified radius is < 1/2 for every eta; compare 1/2 (as a strict cap) to window.
    sup = 0.5
    for rho in PRIZE_RATES:
        lo = 1 - math.sqrt(rho)   # window lower edge 1 - sqrt(rho)
        hi = 1 - rho              # capacity (window upper edge)
        below_cap = sup <= hi     # radius < 1/2 <= capacity (1/2<=hi for all prize rho)
        below_lo = sup <= lo      # radius < 1/2 <= lower-edge
        print(f"  rho={rho:<7}: window=({lo:.4f},{hi:.4f})  "
              f"radius(<1/2) below-or-eq capacity {hi:.4f}? {below_cap}  "
              f"below-or-eq lower-edge {lo:.4f}? {below_lo}")

    print("\nVERDICT: unfolded-R2 certified radius < 1/2 < capacity (1-rho) for ALL four "
          "prize rates\n         => R2/CZ25 CANNOT reach the prize window on UNFOLDED RS; "
          "it requires FOLDING (s >> 1,\n         where dim(A cap ker eval_i) >= dim A - s "
          "allows tau(r) ~ rho on r in [s], per GK16/GG25).")
    print("\n(below window LOWER edge 1-sqrt(rho) holds for rho in {1/8,1/16}; "
          "for rho in {1/2,1/4}\n the radius is below the UPPER edge / capacity but not the "
          "lower edge — the docstring\n statement is the capacity comparison.)")


if __name__ == "__main__":
    main()
