#!/usr/bin/env python3
"""wf407/T371-01-census : production-rate scaling => moment order r = Theta(n).

Confirms the moment-depth verdict: at FIXED production rate rho, the CensusDomination
subset-size parameter r grows LINEARLY with n, and the extremal bad/supply count sits at
the DEEP band, NOT at any fixed low order. Also pins the exact relation between the pin's
(mu,m,r) and the supply subset size, and shows the supply C(s,r) is exponential at rho=1/2.

Deployed pin (CensusDominationWeld): k=(r-2)m+1, n=2^mu*m, band a=rm, code dim k => rate
  rho = k/n = ((r-2)m+1)/(2^mu*m) ~ (r-2)/2^mu.  So r ~ rho*2^mu + 2 = rho*s + 2, s=2^mu.
At rho=1/2 (FRI rate): r ~ s/2 = n/2 = Theta(n). The supply subset size = MOMENT ORDER.
"""
import sys
from math import comb, log2

def main():
    print("="*78)
    print("Production-rate => moment order r grows linearly in n (DEEP).")
    print("="*78)
    print(f"\nm=1 dyadic (n=2^mu). rho fixes r ~ rho*n+2 = the subset size = moment order.")
    print(f"{'rho':>6} {'mu':>3} {'n=2^mu':>8} {'r~rho*n+2':>10} {'supply C(s,r)':>16} "
          f"{'log2 supply':>12} {'r/n (depth frac)':>16}")
    for rho in (0.5, 0.25, 0.125, 0.0625):
        for mu in (4, 6, 8, 10, 12, 20, 30):
            n = 2 ** mu
            s = n  # m=1
            r = round(rho * n) + 2
            if r > s: r = s
            # supply = C(s,r); for huge n report log2 via lgamma
            from math import lgamma
            log2_supply = (lgamma(s + 1) - lgamma(r + 1) - lgamma(s - r + 1)) / log2(2.718281828459045) / 1.0
            # convert ln to log2
            import math
            log2_supply = (math.lgamma(s+1)-math.lgamma(r+1)-math.lgamma(s-r+1))/math.log(2)
            print(f"{rho:>6} {mu:>3} {n:>8} {r:>10} {'C(%d,%d)'%(s,r):>16} "
                  f"{log2_supply:>12.1f} {r/n:>16.4f}", flush=True)
        print()
    print("VERDICT INPUTS:")
    print(" * moment order r = subset size grows LINEARLY in n at every fixed rate.")
    print(" * supply C(s,r) ~ 2^{H(rho)*n} is EXPONENTIAL in n (e.g. rho=1/2, n=2^30:")
    print("   log2 supply ~ 2^30 bits) -- the pin needs #bad <= eps*p = 2^{log2 p -128}.")
    print(" * The required moment depth r = Theta(n) >> r_max = 2 log_n p = O(1) at prize")
    print("   (p ~ n*2^128 => log_n p = 1 + 128/log2 n -> 1+128/30 ~ 5.3 for n=2^30).")
    print(" * So the census supply lives at moment order ~n/2 while the PROVABLE (char-0")
    print("   transferable) moment depth is r_max ~ 5. Gap = n/2 vs O(1) = the W4 master wall.")
    return 0

if __name__ == "__main__":
    sys.exit(main())
