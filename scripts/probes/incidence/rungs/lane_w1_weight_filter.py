#!/usr/bin/env python3
"""W1 — the weight-filter cut, first measurement (pre-registered in HYPOTHESES.md).
q=97, n=32. V_Z = {f : deg f < 16, evenSlice and oddSlice vanish on Z}, parameterized
exactly by (he, ho) in degLT(8-z)^2 via f = (loc_Z*he)(X^2) + X*(loc_Z*ho)(X^2) scaled
(the O96 bijection, char != 2). Sample f uniformly from V_Z; measure #zeros on the
domain; compare smooth domain mu_32 vs random 32-subsets of F_97^*.
Note deg f < 16 = k: f IS a codeword; zeros on domain = 32 - wt(f). List band: >= 5 zeros."""
import random
from collections import Counter
q = 97
# smooth domain: mu_32 in F_97 (32 | 96)
g = None
for c in range(2, 97):
    s = set(); x = 1
    for _ in range(32): x = x*c % q; s.add(x)
    if len(s) == 32 and pow(c, 32, q) == 1: g = c; break
mu32 = []
x = 1
for _ in range(32): x = x*g % q; mu32.append(x)
assert len(set(mu32)) == 32
random.seed(20260611)
nonzero = [a for a in range(1, q)]
def rand_domain(): return random.sample(nonzero, 32)
def pmulmod(a, b):
    out = [0]*(len(a)+len(b)-1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                if bj: out[i+j] = (out[i+j] + ai*bj) % q
    return out
def peval(c, x):
    r = 0
    for co in reversed(c): r = (r*x + co) % q
    return r
def sample_VZ_weights(domain, Z, trials):
    """Z: set of fiber indices (i<16) -> locus points = squares domain[i]*domain[i].
    For smooth: fiber structure i,i+16 antipodal. For random domains there are no
    fibers — use the abstract V_Z: slices vanish on a set of z points of the SQUARED
    multiset. To keep the comparison honest, define V_Z identically through the slice
    parameterization: f(X) = E(X^2) + X*O(X^2), E = locZ*he, O = locZ*ho over the same
    z points; the DOMAIN only enters through where we measure zeros."""
    zpts = [domain[i]*domain[i] % q for i in Z]
    loc = [1]
    for zp in zpts: loc = pmulmod(loc, [(-zp) % q, 1])
    db = 8 - len(zpts)
    hits = Counter()
    for _ in range(trials):
        he = [random.randrange(q) for _ in range(db)]
        ho = [random.randrange(q) for _ in range(db)]
        E = pmulmod(loc, he) if db else loc[:]
        O = pmulmod(loc, ho) if db else loc[:]
        if db == 0: E, O = loc[:], loc[:]
        f = [0]*16
        for j, co in enumerate(E):
            if 2*j < 16: f[2*j] = (f[2*j] + co) % q
        for j, co in enumerate(O):
            if 2*j+1 < 16: f[2*j+1] = (f[2*j+1] + co) % q
        nz = sum(1 for x in domain if peval(f, x) == 0)
        hits[nz] += 1
    return hits
TRIALS = 200000
Zsizes = [3, 5]
print(f"q={q}, n=32, trials={TRIALS} per cell; band threshold: >= 5 domain zeros")
for zs in Zsizes:
    Z = list(range(zs))
    hs = sample_VZ_weights(mu32, Z, TRIALS)
    smooth_band = sum(v for k2, v in hs.items() if k2 >= 5)
    rb = []
    for _ in range(3):
        hr = sample_VZ_weights(rand_domain(), Z, TRIALS)
        rb.append(sum(v for k2, v in hr.items() if k2 >= 5))
    print(f"|Z|={zs}: smooth band-hits {smooth_band}; random domains {rb}; "
          f"smooth zero-hist tail {dict(sorted((k2,v) for k2,v in hs.items() if k2>=4))}")
