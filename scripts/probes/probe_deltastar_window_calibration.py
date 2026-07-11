#!/usr/bin/env python3
"""Issue #389 — calibration of the kkh26-ceiling delta* pin vs the ABF26 prize window.

HONEST FINDING (reproducible): the value 1 - r/2^mu pinned by the kkh26 upper witness +
allWitnessDom lower bound (KKH26DeltaStarPinAllWitness.lean, unconditional for the bulk range)
ALWAYS sits in the NEAR-CAPACITY strip (1-rho-Theta(1/log n), 1-rho), and NEVER inside the
prize window (1-sqrt(rho), 1-rho-Theta(1/log n)). Hence this route pins delta* ABOVE the window,
not in it: it cannot resolve the prize's window-interior question by sharper counting alone.
Also: the bulk range (budget < supply, where the pin is unconditional) shrinks as mu grows,
covering a vanishing fraction of rates asymptotically. Both facts bound exactly what the
unconditional pin does (a real finite near-capacity result) and does not (the $1M open core).
"""
from math import comb, sqrt, log2

def window_table():
    print("mu   r     rho  Johnson  ceiling capacity  win-up~  in-win?")
    for mu in [4, 6, 8, 10]:
        n = 2 ** mu
        for r in [2, n // 8, n // 4, 3 * n // 8, n // 2 - 1]:
            if r < 2:
                continue
            k = r - 1
            rho = k / n
            johnson = 1 - sqrt(rho)
            ceiling = 1 - r / n
            cap = 1 - rho
            winup = cap - 1.0 / log2(n)            # Theta(1/log n) proxy, constant 1
            inwin = johnson < ceiling < winup
            print(f"{mu:>3} {r:>3} {rho:>7.4f} {johnson:>8.4f} {ceiling:>8.4f} "
                  f"{cap:>8.4f} {winup:>8.4f} {str(inwin):>8}")

def bulk_boundary():
    print("\nbulk range (budget C(n,r)/r < supply 2^r*C(n/2,r)), m=1:")
    for mu in [4, 5, 6, 8]:
        n = 2 ** mu
        last_ok = first_bad = None
        for r in range(2, n // 2 + 1):
            if comb(n, r) // r < (2 ** r) * comb(n // 2, r):
                last_ok = r
            elif first_bad is None:
                first_bad = r
        print(f"mu={mu} n={n}: holds up to r={last_ok} (={last_ok/n:.3f}n), "
              f"first fail r={first_bad} (={(first_bad or 0)/n:.3f}n)")

if __name__ == "__main__":
    window_table()
    bulk_boundary()
