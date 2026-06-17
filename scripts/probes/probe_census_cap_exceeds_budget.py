#!/usr/bin/env python3
"""
PROBE: census-cap necessity floor vs deployed weld budget, at the DEEP central band.

The census weld (CensusDominationWeld) pins delta* GRANTING:
  (i) CensusDomination dom k a0 K  -- per-stack alignable-set count <= K at all bands a>=a0,
  (ii) the deployed budget  K/p <= eps*  (so K <= eps* * p).

The necessity floor (CensusCapForcedBelow.censusDomination_cap_ge_choose), instantiated on the
KKH26 supply realizer (kkh26_fibreUnion_aligned_nondegenerate: a gamma-aligned set A with
|A| = r*m at code dim k=(r-2)m+1 on n=s*m domain, carrying a nondegenerate (k+1)-tuple), forces

  C(|A|-(k+1), a-(k+1)) <= K   for ANY band a in [k+1, |A|].

|A| = r*m, k+1 = (r-2)m+2  =>  |A|-(k+1) = 2m-2.  Choosing band a = (r-2)m+2 + (m-1) = (r-1)m+1
(the CENTRAL band of the residual window) gives the floor C(2m-2, m-1) = centralBinom(m-1).

PRIZE REGIME: n = 2^a (thin), q = n^beta (beta ~ 4-5), eps* * q ~ n  =>  K <= eps* p ~ n (POLY).
But C(2m-2, m-1) ~ 4^{m-1}/sqrt(m) is EXPONENTIAL in m.  So at the deep central band the floor
overruns the deployed budget => CensusDomination at that band is INFEASIBLE there.

This probe checks: for prize-regime (n,k,m,r,p,eps*), is centralBinom(m-1) > K_max := floor(eps* p)?
If YES universally in the regime, the deployed census weld CANNOT be invoked at the deep central
band (it must live at Johnson scale a ~ sqrt(kn)), a precise constraint-lemma on the weld.
"""
import math
from math import comb


def central_floor(m):
    # C(2m-2, m-1)  (the max of C(2m-2, j))
    return comb(2 * m - 2, m - 1) if m >= 1 else 1


print("%8s %4s %3s %4s %5s %7s %5s %18s %5s %14s %10s %14s %8s" % (
    "n", "m", "r", "s", "k", "a_band", "|A|",
    "floor=C(2m-2,m-1)", "beta", "q=p", "eps*", "K_max~eps*q", "INFEAS?"))

regime_all_infeasible = True
rows = 0
for a_exp in range(2, 9):          # n = 2^a_exp, thin dyadic subgroup
    n = 2 ** a_exp
    for r in range(2, 6):          # ladder order
        for m_exp in range(1, a_exp):   # m = 2^m_exp (so m | n)
            m = 2 ** m_exp
            if r * m > n:          # |A| must fit in the domain
                continue
            s = n // m
            if s < r:              # need an r-subset T of the s-elt m-power subgroup
                continue
            k = (r - 2) * m + 1
            a_band = (r - 1) * m + 1   # central residual band
            if not (k + 1 <= a_band <= r * m):
                continue
            floor = central_floor(m)   # C(2m-2, m-1)
            for beta in (4, 5):
                q = n ** beta            # p = q, the prize field size (n^beta)
                # prize calibration eps* * q ~ n => eps* ~ n/q ; K_max = floor(eps* q) ~ n
                eps_star = n / q
                K_max = math.floor(eps_star * q)   # ~ n
                infeasible = floor > K_max
                # the result is only meaningful where the floor is nontrivial (m>=2)
                if m >= 2:
                    regime_all_infeasible = regime_all_infeasible and infeasible
                if rows < 40 and (m_exp == 1 or m == n // 2 or r == 2):
                    rows += 1
                    print("%8d %4d %3d %4d %5d %7d %5d %18d %5d %14d %10.2e %14d %8s" % (
                        n, m, r, s, k, a_band, r * m,
                        floor, beta, q, eps_star, K_max,
                        "YES" if infeasible else "no"))

print()
print("DEEP-BAND CENSUS INFEASIBILITY (m>=2) universal across sampled prize regime: %s"
      % regime_all_infeasible)
print("Mechanism: floor C(2m-2,m-1)=centralBinom(m-1) ~ 4^{m-1}/sqrt(pi(m-1)) is EXPONENTIAL in m,")
print("while the deployed budget K_max ~ eps* q ~ n is POLYNOMIAL. For m >= ~4 the floor overruns K.")
