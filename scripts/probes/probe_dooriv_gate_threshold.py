#!/usr/bin/env python3
"""
probe(#444) door-(iv) Lane-3: the XGatedRatio gate-threshold obstruction.

The reduction _DoorIVXGatedPrizeReduction proves:
    XGatedRatio psi G zeta mu x0 lnm  AND  (gate: x0*lnm <= |level k| for all k<=mu)
        ==>  M_mu <= (sqrt2)^mu * M_0  =  sqrt(n) * M_0   (prize floor at n=2^mu).

But the gate "x0*lnm <= |level k|" is a hypothesis the BASE level cannot satisfy:
|level k| = 2^k * |G| (levelTower_card), so the gate FIRST holds at
    k >= k* := ceil( log2( x0*lnm / |G| ) ).
For k < k* the level is BELOW the cancellation threshold; there the per-level
ratio is the TRIVIAL doubling factor 2 (levelRatio_at_zero_eq_two, b=0 aligned),
NOT sqrt2.  So the honest telescope splits:
    M_mu <= 2^{k*} * (sqrt2)^{mu-k*} * M_0     (k* trivial levels, mu-k* cancelling)
which is WORSE than the clean (sqrt2)^mu by exactly a factor 2^{k*}/(sqrt2)^{k*}
= (sqrt2)^{k*} = sqrt(2^{k*}).

This probe confirms the arithmetic + the asymptotic verdict (k* is mu-independent,
so the loss is a harmless polylog at the prize point, but the saving is genuinely
(sqrt2)^{mu-k*} not (sqrt2)^mu: the thin base levels are NON-cancelling).
"""
import math

print("k* = ceil(log2(x0*lnm/|G|)); telescope = 2^{k*}*(sqrt2)^{mu-k*}; clean = (sqrt2)^mu")
print()
cases = [
    (2,  6, 89.0,  30),
    (4,  6, 89.0,  30),
    (16, 6, 89.0,  30),
    (2,  4, 30.0,  30),
    (2,  8, 128*math.log(2), 30),
]
for (G, x0, lnm, mu) in cases:
    arg = x0 * lnm / G
    kstar = max(0, math.ceil(math.log2(arg))) if arg > 1 else 0
    clean_log2 = mu * 0.5                              # log2 (sqrt2)^mu = mu/2
    gated_log2 = kstar * 1.0 + (mu - kstar) * 0.5      # log2 [2^{k*}(sqrt2)^{mu-k*}]
    extra = gated_log2 - clean_log2                    # = k*/2
    print(f"G={G:3d} x0={x0} lnm={lnm:6.1f}: k*={kstar:2d}  "
          f"clean=2^{clean_log2:.1f}  gated=2^{gated_log2:.1f}  "
          f"EXTRA_COST=2^{extra:.2f} (=sqrt(2^k*)=2^{kstar/2:.2f})")

print()
print("VERDICT (probe-confirmed arithmetic):")
print("- gate fails for k<k*; those k* base levels are trivial-doubling (factor 2), not sqrt2.")
print("- honest descent saving is (sqrt2)^{mu-k*}, NOT (sqrt2)^mu.")
print("- extra multiplicative cost over the clean prize floor = sqrt(2^{k*}), with")
print("  k* = O(log(lnm/|G|)) = O(log log p) = mu-INDEPENDENT.")
print("- so the descent's prize-scale saving SURVIVES asymptotically (loss is polylog),")
print("  but ONLY because k* does not grow with mu. The constraint to lock: M_mu obeys")
print("  the split bound 2^{k*}(sqrt2)^{mu-k*} M_0, equivalently M_mu <= sqrt(2^{k*}) * sqrt(n) * M_0.")
print("- This QUANTIFIES the non-cancelling base of the tower the gate cannot reach.")
print("- NO CORE / cancellation / completion / moment / capacity claim. CORE OPEN.")
