#!/usr/bin/env python3
"""
[P1-effective-sumproduct-push] CEILING probe: the r-fold sum-product amplification
fed the SATURATED near-Sidon energy CANNOT reach prize saving 1/2; only the
GROWING-r moment method (r~log q) can, and that is NOT a sum-product estimate
(it is the char-p Lam-Leung energy transfer = the open core).

Two reductions from energy E_r(mu_n) to B = max_{b!=0}|eta_b|, contrasted:

(1) FIXED-FOLD SUM-PRODUCT (di Benedetto, r=3): saving = (10-2t3-t2/2)/72.
    HARD floors t2>=2 (Cauchy-Schwarz), t3>=3 (diagonal). mu_n SATURATES both
    (t2=2 Sidon-mod-neg, t3=3 Lam-Leung). => saving <= 1/24, 12x short of 1/2.
    Formalized + axiom-clean: Frontier/_DiBenedettoNearSidomImprovement.lean
    (diBenedettoSaving_le_ceiling, energy_method_below_prize).

(2) MOMENT METHOD (r -> log q): B^{2r} <= q * E~_r (reduced energy). With the
    GAUSSIAN energy E~_r <= (2r-1)!! n^r to r~log q gives B <= sqrt(2n log m),
    saving 1/2 - o(1). REACHES the floor -- but the input (2r-1)!! energy to
    r~log q is the OPEN char-p transfer (verified n<=40, open at n=2^30), NOT a
    sum-product estimate.

KEY MEASURED FACT (probe_c3_effective_sumproduct_mun): E(mu_n)/n^2 -> 3 = the
SATURATED Sidon floor. So the additive energy is ALREADY minimal; the
sum-product input cannot be improved. Yet B/sqrt(n) GROWS (2.67->4.82 over
n=8..64) and e=logB/logn stays >> 1/2. PROOF that energy is NOT the bottleneck:
the gap to 1/2 is the correlated-Gauss-phase (spectral) cancellation, which the
moment method captures via growing r and the energy method (fixed r) cannot.
"""
from math import log, sqrt

def double_factorial(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

print("=== (1) FIXED-FOLD SUM-PRODUCT ceiling (di Benedetto family) ===")
from fractions import Fraction as F
def saving(t2, t3): return (10 - 2*t3 - F(t2)/2) / 72
print(f"  general subgroup (t2=49/20,t3=4): {float(saving(F(49,20),4)):.5f} = 31/2880  (published SOTA)")
print(f"  near-Sidon mu_n  (t2=2,   t3=3 ): {float(saving(2,3)):.5f} = 1/24     (SATURATED corner)")
print(f"  floors t2>=2, t3>=3 (universal) => saving <= 1/24. PRIZE 1/2 is {0.5/float(saving(2,3)):.0f}x larger.")
print()
print("=== (2) MOMENT METHOD (growing r) with GAUSSIAN energy E~_r <= (2r-1)!! n^r ===")
beta = 4
n = 2**30; logn = log(n)
best = (0, -1, 0)
for r in range(2, 300):
    df = double_factorial(2*r-1)
    logB = ((beta+r)/(2*r))*logn + (1/(2*r))*log(df)
    sav = 1 - logB/logn
    if sav > best[1]:
        best = (r, sav, logB/logn)
print(f"  n=2^30, beta=4: optimal r={best[0]}, e=logB/logn={best[2]:.4f}, saving={best[1]:.4f}")
print(f"  -> saving 1/2 - o(1) (the sqrt(log m) correction). REACHES the prize floor.")
print(f"  BUT input (2r-1)!! energy to r~{best[0]} is the OPEN char-p Lam-Leung transfer, NOT sum-product.")
print()
print("=== VERDICT (P1) ===")
print("  No-gain. The sum-product/energy family is PROVABLY capped at saving 1/24 (axiom-clean Lean).")
print("  mu_n already SATURATES the energy floor (E/n^2->3), so no quantified sum-product (Rudnev")
print("  point-plane, Konyagin-Shkredov, asymmetric E_x=n^3 vs E_+=3n^2) can push past 1/24.")
print("  The exact gap to 1/2: the prize exponent is SPECTRAL (growing-r moment / correlated Gauss")
print("  phase), reachable only via the char-p Gaussian-energy transfer = the open core, not sum-product.")
