#!/usr/bin/env python3
"""The multiplicative-subspace supply BOUNDARY vs the CensusDomination band floor.
Pin parametrization (CensusDominationWeld / interiorCeiling_of_censusDomination):
  n = 2^mu * m,  code dim k = (r-2)*m  (evalCode degree),  rho = (r-2)/2^mu,
  ceiling agreement alpha* = r/2^mu,   CensusDomination band floor a0 = r*m + 1.
Construction (EsymmFiber): a union of s cosets of mu_d (d=2^j, d | n) is an explainable
t-core for band offset b iff d >= b+2 and t = s*d, code dim k = t - b - 1, giving
>= C(n/d, s) explainable cores at agreement t.
QUESTION: at band a >= a0 = rm+1, is max over valid (d=2^j>=b+2, d|a, b=a-k-1>=0) of
C(n/d, a/d) exponential in n (=> CensusDomination FALSE on dyadic mu_n, pin broken on
target domains) or polynomial (=> pin survives, exp supply harmless near capacity)?
EXACT integer arithmetic; report log2(supply)/n (the exponential rate) and the
divisibility-feasible bands. Falsifier for 'pin survives': any exp supply at a = a0."""
from math import comb, log2

def valid_supplies(n, mu, m, r):
    """For pin params (n=2^mu*m, k=(r-2)*m), scan bands a from a0=rm+1 down to the
    construction's native band (r-1)m+1, AND up toward capacity; at each band find the
    max coset-union supply over d=2^j with d|n, d|a, d>=b+2 (b=a-k-1>=0)."""
    k = (r - 2) * m
    a0 = r * m + 1            # CensusDomination band floor
    nat = (r - 1) * m + 1     # construction's native band k+m+1
    dyadic_d = [1 << j for j in range(mu + 1) if (1 << j) <= n and n % (1 << j) == 0]
    rows = []
    # scan a representative set of bands: native, floor, and a few between/above
    bands = sorted(set([nat, a0] + [a0 + i for i in range(0, 3*m+1)] + [k + 1 + i for i in range(0, 4*m+2)]))
    bands = [a for a in bands if 1 <= a <= n]
    for a in bands:
        b = a - k - 1                 # band offset m_constr; need >= 0
        if b < 0: continue
        best = 0; best_d = None
        for d in dyadic_d:
            if d < b + 2: continue    # e_1..e_{b+1} vanish needs d>=b+2
            if a % d != 0: continue   # need d | a (a = s*d)
            s = a // d
            Nc = n // d               # available cosets
            if s > Nc: continue
            sup = comb(Nc, s)
            if sup > best: best, best_d = sup, d
        rate = log2(best) / n if best > 0 else None
        rows.append((a, b, best, best_d, rate))
    return k, a0, nat, rows

print("Pin: n=2^mu*m, k=(r-2)m, rho=(r-2)/2^mu, ceiling alpha*=r/2^mu, CensusDom floor a0=rm+1")
print("Construction native band = k+m+1 = (r-1)m+1.  exp-rate = log2(supply)/n.\n")
# production rate rho = 1/2: (r-2)/2^mu = 1/2 => r = 2^(mu-1)+2.  Take m=1 (pure dyadic FFT domain).
for mu in [6, 8, 10]:
    for rho_name, num, den in [("1/2",1,2),("1/4",1,4)]:
        m = 1
        n = (1 << mu) * m
        r = (num * (1 << mu)) // den + 2     # (r-2)/2^mu = rho
        if r < 2: continue
        k, a0, nat, rows = valid_supplies(n, mu, m, r)
        # find max exp-rate at/above a0, and at the native band
        at_floor = [x for x in rows if x[0] == a0]
        at_native = [x for x in rows if x[0] == nat]
        above = [x for x in rows if x[0] >= a0 and x[4] is not None]
        maxabove = max(above, key=lambda x: x[4]) if above else None
        print(f"mu={mu} rho={rho_name}: n={n} k={k} rho={(r-2)/(1<<mu):.4f} "
              f"alpha*={r/(1<<mu):.4f} (Johnson sqrt(rho)={(((r-2)/(1<<mu))**0.5):.4f}) a0={a0} native={nat}")
        for tag, xs in [("native(k+m+1)", at_native), ("FLOOR(rm+1)", at_floor)]:
            for a, b, sup, bd, rate in xs:
                print(f"    {tag} a={a}: best d={bd} supply={sup} exp-rate={rate if rate else 0:.4f}"
                      + ("  [EXPONENTIAL]" if rate and rate > 0.01 else "  [poly/none]"))
        if maxabove:
            print(f"    max exp-rate over bands >= a0: {maxabove[4]:.4f} at a={maxabove[0]} (d={maxabove[3]})")
        print()
