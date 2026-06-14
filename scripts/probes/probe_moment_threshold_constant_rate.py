#!/usr/bin/env python3
"""
probe(#389): the moment/Bessel method's clean regime r*(n) FALLS BELOW r~log p at constant rate
-- it closes the log-short family (wakesync) but NOT the constant-rate prize. A method-boundary
result, NOT a prize refutation.

Setup (wakesync's Bessel reduction, RungBesselEnergy.lean / deltastar-bessel-energy-reduction-...md):
the moment method needs E_r(mu_2^mu) clean (= Gaussian baseline (2r-1)!!*n^r, the C value) up to
r ~ log p; then sup_t|S(t)| <= sqrt(2 n log p) and delta* closes. At constant rate n~p^{1/beta} the
finite-p excess E_r^{(p)} - E_r^infty (= #{small points of the prime P above p that are sums of 2r
roots of unity}) appears at some threshold r*(n).

MEASURED (E_r^{(const p~n^4)} / E_r^{(clean p~n^9)}, first r where ratio>1.01):
    n=8  : clean to r~7-8   (ln p=8.33)   r*/ln p ~ 0.90
    n=16 : clean to r~5     (ln p=11.09)  r*/ln p ~ 0.50
    n=32 : clean to r~3     (ln p=13.86)  r*/ln p ~ 0.25
=> r*/ln p HALVES per doubling of n -> 0. Fit r*(n) ~ 13.5 - 2 log2(n); required ~ 2.77 log2(n)
(=ln(n^4)); they cross at n~7, so for EVERY prize n>=8 the clean regime is short of r~log p and the
deficit grows linearly in log n.

CONSEQUENCE. The Bessel/moment route is PROVEN to close delta* only for log-short n
(p > (2r)^{n/2} at r~log p, i.e. n = O(log p/log log p)); at constant rate it does NOT reach r~log p,
so sup_t|S| is not controlled to sqrt(n log p) by this method. This sharpens the boundary of
wakesync's result and confirms the constant-rate prize stays open VIA THIS ROUTE. It does NOT refute
the prize (the sup may still be sqrt(n log p); the moment method is merely insufficient to prove it,
like BGK/Weil). The open core is unchanged: the small points of P at r~log p, constant rate.
"""
import sympy, math
from collections import Counter
from itertools import product

def E_r(H, p, r):
    c = Counter()
    for tup in product(H, repeat=r): c[sum(tup) % p] += 1
    return sum(v*v for v in c.values())

def mu(p, n):
    g = int(sympy.primitive_root(p)); z = pow(g, (p-1)//n, p)
    return [pow(z, j, p) for j in range(n)]

def main():
    print(f"{'n':>4} {'p_const~n^4':>12} {'ln p':>6} {'r':>2} {'E_r const/clean':>16}")
    for k in (3, 4, 5):
        n = 1 << k
        m = (n**4 - 1)//n
        while True:
            pc = m*n+1; m += 1
            if sympy.isprime(pc): break
        m2 = (n**9 - 1)//n
        while True:
            pcl = m2*n+1; m2 += 1
            if sympy.isprime(pcl): break
        Hc, Hcl = mu(pc, n), mu(pcl, n)
        rmax = 8 if n == 8 else (6 if n == 16 else 5)
        for r in range(2, rmax+1):
            if n**r > 40_000_000: break
            ratio = E_r(Hc, pc, r)/E_r(Hcl, pcl, r)
            flag = "  <-- excess" if ratio > 1.01 else ""
            print(f"{n:>4} {pc:>12} {math.log(pc):>6.2f} {r:>2} {ratio:>16.5f}{flag}")

if __name__ == "__main__":
    main()
