#!/usr/bin/env python3
"""
LANE wf4IWA (#444) — EXTREME-v2 + heavy-direction MULTIPLICITY adversarial check.

Two final adversarial tests of the v2(p-1)-interpolation hope for the BGK floor:

  TEST C (extreme v2 at MATCHED beta): pick, in the SAME narrow beta band, the SMALLEST-v2 prime
     (v2=v2(n), generic) and the LARGEST-v2 prime (Fermat-rich, v2 maximal in band). If high-v2
     FORCES the floor up/down (mission hypothesis) the two M/sqrt(n) must differ systematically.

  TEST D (multiplicity, the prize-relevant quantity): the prize list size is driven not by the
     single max |eta_b| but by HOW MANY b have |eta_b| within (1-o(1)) of the max (the heavy-cluster
     count). Does v2(p-1) gate the heavy-cluster COUNT (#{b: |eta_b| >= 0.9*max}) at fixed n,beta?

EXACT complex char sum over the order-n subgroup. Vectorized. n=2^mu thin subgroup, never full group.
"""
import math, sys
import numpy as np

def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    if x % 3 == 0: return x == 3
    d = 5
    while d*d <= x:
        if x % d == 0 or x % (d+2) == 0: return False
        d += 6
    return True

def v2(m):
    c = 0
    while m % 2 == 0:
        m //= 2; c += 1
    return c

def proot(p):
    m = p-1; fac = []; d = 2
    while d*d <= m:
        if m % d == 0:
            fac.append(d)
            while m % d == 0: m //= d
        d += 1
    if m > 1: fac.append(m)
    for g in range(2, p):
        if all(pow(g, (p-1)//f, p) != 1 for f in fac): return g

def mags(n, p):
    g = proot(p); h = pow(g, (p-1)//n, p)
    xs = []; cur = 1
    for _ in range(n):
        xs.append(cur); cur = (cur*h) % p
    xs = np.array(xs, dtype=np.int64)
    m = (p-1)//n
    CAP = 50000
    if m <= CAP:
        js = np.arange(m, dtype=np.int64)
    else:
        rng = np.random.default_rng(7)
        js = np.unique(np.concatenate([np.arange(2000, dtype=np.int64),
                                       rng.integers(0, m, size=CAP-2000)]))
    breps = np.array([pow(g, int(j), p) for j in js], dtype=np.int64)
    bx = (breps[:, None]*xs[None, :]) % p
    ang = (2.0*np.pi/p)*bx
    eta = np.cos(ang).sum(axis=1) + 1j*np.sin(ang).sum(axis=1)
    return np.abs(eta), m

def primes_in_band(n, b0, b1):
    plo = int(n**b0); phi = int(n**b1)
    out = []
    p = plo - (plo % n) + 1
    while p < phi:
        if p > 2 and isprime(p) and (p-1) % n == 0:
            out.append((v2(p-1), p))
        p += n
    return out

def run(n, b0=3.3, b1=3.45):
    sn = math.sqrt(n)
    band = primes_in_band(n, b0, b1)
    if len(band) < 4:
        band = primes_in_band(n, b0, b1+0.3)
    band.sort()
    minv2 = band[0][0]; maxv2 = band[-1][0]
    print("="*82)
    print(f"n={n}  beta band [{b0:.2f},{b1:.2f}]  #primes={len(band)}  v2 range [{minv2},{maxv2}]")
    print("="*82)
    print("TEST C+D: matched-beta extreme-v2 + heavy-cluster multiplicity")
    rows = []
    for c, p in band:
        mg, m = mags(n, p)
        mx = mg.max()
        heavy = int((mg >= 0.9*mx).sum())   # cluster of near-maximal directions
        # density of heavy cluster among sampled cosets (multiplicity normalized)
        dens = heavy/len(mg)
        beta = math.log(p)/math.log(n)
        rows.append((c, p, beta, mx/sn, heavy, dens))
    # group by v2
    byv2 = {}
    for c, p, beta, norm, heavy, dens in rows:
        byv2.setdefault(c, []).append((norm, dens))
        print(f"   v2={c:2d}  p={p:9d}  beta={beta:4.2f}  M/sqrt(n)={norm:5.3f}  "
              f"heavy(#>=.9max)={heavy:4d}  heavy_density={dens:.4f}")
    print(f"\n   -- per-v2 (M/sqrt(n) mean, heavy_density mean) --")
    for c in sorted(byv2):
        arr = byv2[c]
        nm = sum(a for a,_ in arr)/len(arr); dn = sum(d for _,d in arr)/len(arr)
        print(f"     v2={c:2d}: M/sqrt(n)={nm:.3f}  heavy_density={dn:.4f}  (n={len(arr)})")
    norms = [(c, sum(a for a,_ in byv2[c])/len(byv2[c])) for c in sorted(byv2)]
    denss = [(c, sum(d for _,d in byv2[c])/len(byv2[c])) for c in sorted(byv2)]
    nspread = max(v for _,v in norms)-min(v for _,v in norms)
    dspread = max(v for _,v in denss)-min(v for _,v in denss)
    print(f"\n   across-v2 spread: M/sqrt(n)={nspread:.3f}   heavy_density={dspread:.4f}")
    print(f"   => {'NO v2-gating of magnitude or multiplicity (same wall)' if (nspread<0.4 and dspread<0.02) else 'inspect: residual v2 structure'}")

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 32
    run(n)
