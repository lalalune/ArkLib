#!/usr/bin/env python3
"""Does the EsymmFiber multiplicative-subspace construction EVER fire at production
parameters? Firing condition (exact, from smooth_dyadic_supply_lower_bound):
  exists d = 2^j with  d | t  and  d >= m+2  where  t = k+m+1, m = t-k-1 >= 0.
Equivalently: exists power-of-2 d in (t-k, t] with d | t, i.e. 2^{v2(t)} >= t-k+1.
Supply when it fires: C(n/d, t/d).  Falsify-first: hunt for ANY firing at production
rates (rho in {1/2,1/4,1/8,1/16}, n=2^mu => k=rho*n is a power of 2)."""
from math import comb, log2

def v2(x):
    c = 0
    while x % 2 == 0 and x > 0: x //= 2; c += 1
    return c

def fires(n, k, mmax=None):
    """scan m=0.. for a valid dyadic d; return list of (m, t, d, supply, agreement)."""
    hits = []
    if mmax is None: mmax = n - k - 1
    for m in range(0, mmax + 1):
        t = k + m + 1
        if t > n: break
        # largest power of 2 dividing t:
        d2 = 1 << v2(t)
        # need a power-of-2 divisor d of t with d >= m+2; the best is d2 (and its powers-of-2 divisors)
        # any power-of-2 divisor of t is <= d2; so feasible iff d2 >= m+2
        if d2 >= m + 2 and d2 >= 2:
            d = d2
            s = t // d
            Nc = n // d
            if s <= Nc:
                hits.append((m, t, d, comb(Nc, s), t / n))
    return hits

print("PRODUCTION RATES (k = rho*n a power of 2): hunting for ANY construction firing\n")
total_fires = 0
for mu in range(4, 13):
    n = 1 << mu
    for name, num, den in [("1/2",1,2),("1/4",1,4),("1/8",1,8),("1/16",1,16)]:
        k = n * num // den
        if k < 1: continue
        h = fires(n, k)
        if h:
            total_fires += 1
            print(f"  mu={mu} rho={name} k={k}: FIRES at {len(h)} bands, e.g. {h[:2]}")
print(f"production firings found: {total_fires}  (0 => construction VACUOUS at all production rates)\n")

# Now: WHERE does it fire? non-power-of-2 k. characterize the firing set.
print("WHERE IT FIRES (non-power-of-2 k): the construction needs k+m+1 to have a large 2-adic part\n")
for mu in [8]:
    n = 1 << mu
    examples = []
    for k in range(2, n):
        h = fires(n, k, mmax=min(40, n-k-1))
        # keep only exponential firings (supply rate > 0.05)
        exp_h = [(m,t,d,sup,a) for (m,t,d,sup,a) in h if sup>0 and log2(sup)/n > 0.05]
        if exp_h:
            best = max(exp_h, key=lambda x: log2(x[3])/n)
            examples.append((k, best[0], best[2], log2(best[3])/n, best[4], k/n))
    print(f"n={n}: {len(examples)} of {n-2} k-values admit EXPONENTIAL firing")
    if examples:
        # show a few, sorted by how close k/n is to a production rate
        for k, m, d, rate, agr, rho in examples[:6]:
            print(f"    k={k} (rho={rho:.4f}): m={m} d={d} exp-rate={rate:.3f} at agreement={agr:.4f}")
        # is any firing k a power of 2?
        pow2_fires = [e for e in examples if (e[0] & (e[0]-1)) == 0]
        print(f"    power-of-2 k values that fire exponentially: {[e[0] for e in pow2_fires]}")
