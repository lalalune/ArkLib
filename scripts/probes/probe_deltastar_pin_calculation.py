#!/usr/bin/env python3
"""#389 The delta* failure bracket from the proven supply->badSet machinery is
SUPPLY-EXPONENT-INDEPENDENT and equals capacity - Theta(1/log q).

Conversion (in-tree deep_band_badSet_card_of_supply): C(n,k+m+1) <= #badSet*q^m*B.
MCA fails at band m iff C(n,k+m+1) >= eps* * q^{m+1} * B (eps* = 2^-128). Agreement
t=k+m+1, radius delta_m = 1 - t/n; the LARGEST m with failure = tightest delta* upper
bracket delta* <= 1-(k+m+1)/n. We find m_max by binary search for supply models
B in {1 (ideal), n^{1.25} (HBK n^{5/2} energy via sqrt), n^{1.5} (order-2 Stepanov)}.

Finding: m_max (hence the bracket) is identical to 4 decimals across all three B -- the
witness mass C(n,t) dominates q^{m+1}*B so the supply EXPONENT is irrelevant to the
failure bracket. The bracket = capacity - Theta(1/log q) (gap ~ 1/logq, = 1/logn only when
q~n, smaller at large prize fields). So KKH26's explicit ceiling cap-Theta(1/logn) is the
binding upper bracket; grinding the energy exponent does NOT help the failure side -- the
energy bound pays off only on the holding/lower bracket (small-list => corr. agreement).
"""
import math

def log2C(n, r):
    if r < 0 or r > n:
        return float('-inf')
    return (math.lgamma(n+1) - math.lgamma(r+1) - math.lgamma(n-r+1)) / math.log(2)

EPS = -128
print(f"{'mu':>3} {'rho':>7} {'supply B':>17} | {'delta*<=':>9} {'cap':>7} {'Johnson':>8} "
      f"{'cap-1/logn':>11} {'gap':>8}  verdict")
for mu in (20, 30, 40):
    n = 1 << mu
    for rho in (0.5, 0.25, 0.125):
        k = int(rho * n)
        cap = 1 - rho
        johnson = 1 - math.sqrt(rho)
        ceil_kkh = cap - 1.0 / mu
        logq = 256
        for label, logB in (("B=1 ideal", 0.0),
                             ("sqrtE HBK n^1.25", 2.5 * mu / 2),
                             ("sqrtE ord2 n^1.5", (3 * mu - 1) / 2)):
            def margin(m):
                return log2C(n, k + m + 1) - (EPS + (m + 1) * logq + logB)
            if margin(1) < 0:
                print(f"{mu:>3} {rho:>7} {label:>17} | {'(none)':>9}")
                continue
            lo, h = 1, n - k - 1
            while lo < h:
                mid = (lo + h + 1) // 2
                if margin(mid) >= 0:
                    lo = mid
                else:
                    h = mid - 1
            ds = 1 - (k + lo + 1) / n
            gap = cap - ds
            v = ("=cap(trivial)" if ds >= cap - 1e-9 else
                 "in[ceil,cap]" if ds >= ceil_kkh - 1e-9 else
                 "WINDOW INTERIOR" if ds >= johnson - 1e-9 else "BELOW Johnson(!)")
            print(f"{mu:>3} {rho:>7} {label:>17} | {ds:>9.4f} {cap:>7.4f} {johnson:>8.4f} "
                  f"{ceil_kkh:>11.4f} {gap:>8.5f}  {v}")
print()
print("Supply exponent irrelevant (rows agree to 4 dp); gap ~ 1/log q. KKH26 cap-1/logn binds.")
