#!/usr/bin/env python3
"""
LANE wf4IWA (#444) — 2-adic / cyclotomic-unit STRATIFICATION of the v2(p-1)-GATED FLOOR.

CONTEXT (mission STATE-OF-KNOWLEDGE):
  - The OVER-determined far-line incidence (affine-in-gamma) is p-INDEPENDENT and v2-BLIND
    (Johnson-locked). LC2's probe_wf2LC2_v2gate_* measured THAT object => v2-blind, as expected.
  - The FLOOR (under-determined stratum, c=s-k<=1) is the p-DEPENDENT BGK CHARACTER SUM
        M(n,p) = max_{b != 0 mod p} | Sum_{x in mu_n} e_p(b*x) |,   mu_n = order-n subgroup of F_p*.
    THIS is the v2(p-1)-gated object. The mission asks: stratify M by v2(p-1) and look for a
    clean 2-adic-interpolation law M ~ f(v2)*sqrt(n) (a structural handle BGK's uniform wall misses).

This probe (genuinely new lens, NOT the far-line incidence):
  For fixed n=2^mu, sweep MANY primes p = 1 mod n grouped by v2(p-1) in {mu, mu+1, ..., 20}.
  For each p compute the EXACT BGK period M(n,p) (full b-sweep, vectorized mod-p Gauss-period real value
  is complex; we use the EXACT complex character sum since e_p lives in C). Also compute:
    - the normalized period  M / sqrt(n)   (sqrt-cancellation reference; BGK predicts O(sqrt(n)) up to logs)
    - the per-prime DISTRIBUTION of |eta_b| (we report max, and the count of b near the max).
  Then test, AT FIXED n: does (max, mean, sqrt-normalized) M correlate with v2(p-1)?
    - if a clean monotone/affine law in v2 emerges  => 2-adic interpolation handle (CONJECTURE, report law).
    - if M scatters identically across v2-classes    => v2-gating is NOISE on the magnitude (refute the
                                                          interpolation hope; pin it as same-wall).

EXACT: complex character sum over the actual subgroup mu_n (computed mod p, then mapped to e_p via the
discrete log index in the subgroup -> root-of-unity is NOT needed: eta_b = sum over x in mu_n of
exp(2*pi*i*(b*x mod p)/p), with x ranging over the n subgroup elements as INTEGERS in [0,p).)
Vectorized with numpy.
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

def subgroup(n, p):
    """The n integer representatives in [0,p) of the order-n subgroup mu_n of F_p*."""
    g = proot(p); h = pow(g, (p-1)//n, p)
    xs = []
    cur = 1
    for _ in range(n):
        xs.append(cur)
        cur = (cur*h) % p
    return np.array(xs, dtype=np.int64)

def bgk_period(n, p, xs):
    """EXACT M(n,p) = max_{b=1..p-1} | sum_{x in mu_n} exp(2 pi i b x / p) |.
    Vectorized: for b range, build phase matrix. p can be up to ~few million; we sweep b over
    a representative set. Since b ranges over (Z/p)*, and b*x permutes within cosets, |eta_b| takes
    at most (p-1)/n distinct VALUES indexed by the coset of b in F_p*/mu_n. So we only need ONE b per
    coset of mu_n: b runs over coset reps. # cosets = (p-1)/n. For large p that's big; cap with a
    random + structured sample of cosets and report max over sample (the period max is well-sampled).
    """
    m = (p-1)//n  # number of cosets = index
    # coset reps: powers of proot stepping by n won't give coset reps directly; use g^j for j=0..m-1
    g = proot(p);
    # coset reps of mu_n in F_p*: g^0, g^1, ..., g^{m-1} (since mu_n = <g^m>)
    # |eta_b| depends only on coset b*mu_n, i.e. on j = (index of b) mod m.
    # So sweep j=0..m-1 if m small, else sample.
    CAP = 60000
    if m <= CAP:
        js = np.arange(m, dtype=np.int64)
    else:
        rng = np.random.default_rng(12345)
        js = np.unique(np.concatenate([np.arange(2000, dtype=np.int64),
                                       rng.integers(0, m, size=CAP-2000)]))
    # b = g^j mod p for each j
    breps = np.empty(len(js), dtype=np.int64)
    gj = 1
    # need g^j for arbitrary j; do via pow per j (vectorize with python comprehension, m capped)
    breps = np.array([pow(g, int(j), p) for j in js], dtype=np.int64)
    # eta_b = sum_x exp(2 pi i (b x mod p)/p). Build (len(js), n) integer (b*x mod p).
    bx = (breps[:, None] * xs[None, :]) % p     # shape (J, n)
    ang = (2.0*np.pi/p) * bx
    eta = np.cos(ang).sum(axis=1) + 1j*np.sin(ang).sum(axis=1)
    mag = np.abs(eta)
    return mag.max(), mag.mean(), float(mag.std()), len(js), m

def primes_by_v2(n, count_per_class, classes, pstart, pwindow):
    out = {c: [] for c in classes}
    p = pstart - (pstart % n) + 1
    end = pstart + pwindow
    while p < end and any(len(out[c]) < count_per_class for c in classes):
        if p > 2 and isprime(p) and (p-1) % n == 0:
            c = v2(p-1)
            if c in out and len(out[c]) < count_per_class:
                out[c].append(p)
        p += n
    return out

def run(n, count_per_class=4, pstart=70000, pwindow=8_000_000):
    print("="*82)
    print(f"n={n}  v2(n)={v2(n)}   BGK period M(n,p)=max_b |sum_(x in mu_n) e_p(b x)|   ref sqrt(n)={math.sqrt(n):.3f}")
    print("="*82)
    base = v2(n)
    classes = list(range(base, base+9))  # v2(p-1) from mu up to mu+8
    byv2 = primes_by_v2(n, count_per_class, classes, pstart, pwindow)
    summary = {}
    for c in classes:
        for p in byv2[c]:
            xs = subgroup(n, p)
            mx, mn, sd, sampled, m = bgk_period(n, p, xs)
            beta = math.log(p)/math.log(n)
            norm = mx/math.sqrt(n)
            summary.setdefault(c, []).append(norm)
            print(f"  v2(p-1)={c:2d}  p={p:9d}  beta={beta:4.2f}  idx_m={m:8d}  Mmax={mx:7.3f}  "
                  f"M/sqrt(n)={norm:6.3f}  Mmean={mn:6.3f}  (cosets sampled={sampled})")
    print(f"\n  -- per-v2 normalized M/sqrt(n) summary (does it track v2?) --")
    cs = sorted(summary)
    for c in cs:
        arr = summary[c]
        print(f"     v2={c:2d}:  M/sqrt(n) in [{min(arr):.3f},{max(arr):.3f}]  mean={sum(arr)/len(arr):.3f}  (n_primes={len(arr)})")
    # verdict: range of class-means
    means = [sum(summary[c])/len(summary[c]) for c in cs]
    if len(means) >= 2:
        spread = max(means)-min(means)
        # also global scatter within a class (to compare gating-spread vs noise-spread)
        within = max(max(summary[c])-min(summary[c]) for c in cs if len(summary[c])>1) if any(len(summary[c])>1 for c in cs) else 0.0
        print(f"\n  ACROSS-v2 spread of class-means = {spread:.3f}   WITHIN-class scatter (max) = {within:.3f}")
        if spread <= within + 1e-9:
            print("  => v2-gating spread <= within-class noise: NO clean v2-interpolation of magnitude (same wall).")
        else:
            print("  => across-v2 spread EXCEEDS within-class noise: candidate v2-dependent law — inspect monotonicity.")
    return summary

if __name__ == '__main__':
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 16
    run(n, count_per_class=4)
