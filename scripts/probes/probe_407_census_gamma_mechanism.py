#!/usr/bin/env python3
"""
MECHANISM of the gamma-census closed form gamma_worst(n,r=3) = n*C(n/4,2)+1 on the antipodal-adjacent
line (x^{n/2}, x^{n/2-1}). Goal: turn the 3-point fit (97,897,7681) into a PROVABLE cyclotomic count.

The C(n/4,2) prefactor + the n* multiplicity + the +1 strongly suggest:
  - the +1 is the gamma=0 / saturated admissible point (or a single distinguished orbit),
  - the n* is the full mu_n dilation orbit (z->h*z) of each gamma-rep,
  - the C(n/4,2) counts something inside a mu_{n/4} sub-structure (pairs).

THIS PROBE dissects the distinct-gamma SET on the worst line at n=16,32:
  1. confirm the dilation-orbit structure: is the gamma-set a union of full mu_n-cosets (size n)?
     => #gamma = n * (#orbits) + (gamma=0?). If #orbits = C(n/4,2) we have the mechanism.
  2. identify which a-subsets S (size a0=4, r=3 => k=2) realize each gamma-orbit, and whether their
     index-structure lives in a mu_{n/4} (the 4|. resonance backbone from the e2=0 census).
Exact mod-p, proper mu_n, p>>n^2, NEVER n=q-1.
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from prize_workspace import prime_factors
from math import comb

def find_prime_index(n, m, lo=None):
    p = (lo if lo else m*n); p += (1 - p) % n
    if p < 3: p = n + 1
    while True:
        if p > 2 and p % n == 1 and (p-1)//n >= m and all(p % d for d in range(2, int(p**0.5)+1)):
            return p
        p += n

def find_g(p, n):
    for h in range(2, 8000):
        x = pow(h, (p-1)//n, p)
        if pow(x, n, p) == 1 and all(pow(x, n//q, p) != 1 for q in prime_factors(n)):
            return x
    raise ValueError

def gamma_set_with_witnesses(aa, bb, xs, p, k, a, g):
    """Return dict gamma -> list of a-subsets (index tuples) realizing it, full (non-orbit-reduced)."""
    n = len(xs)
    u0 = [pow(x, aa, p) for x in xs]; u1 = [pow(x, bb, p) for x in xs]
    e0, e1 = {}, {}
    for T in itertools.combinations(range(n), k+1):
        t0 = t1 = 0
        for i in T:
            den = 1
            for j in T:
                if i != j: den = den*((xs[i]-xs[j]) % p) % p
            inv = pow(den, -1, p)
            t0 = (t0 + u0[i]*inv) % p; t1 = (t1 + u1[i]*inv) % p
        e0[T] = t0; e1[T] = t1
    def ratio(T):
        a_, b_ = e0[T], e1[T]
        if b_ != 0: return (-a_) * pow(b_, -1, p) % p
        return None if a_ == 0 else 'X'
    gmap = {}
    for S in itertools.combinations(range(n), a):
        r = None; ok = True; nd = False
        for T in itertools.combinations(S, k+1):
            rt = ratio(T)
            if rt is None: continue
            if rt == 'X': ok = False; break
            nd = True
            if r is None: r = rt
            elif r != rt: ok = False; break
        if ok and nd:
            gmap.setdefault(r, []).append(S)
    return gmap, g

def analyze(n, mu):
    r = 3; k = 2; a0 = 4
    p = find_prime_index(n, 12, lo=n**4)
    g = find_g(p, n); xs = [pow(g, i, p) for i in range(n)]
    aa, bb = n//2, n//2 - 1
    gmap, _ = gamma_set_with_witnesses(aa, bb, xs, p, k, a0, g)
    ng = len(gmap)
    # dilation orbit structure: gamma(h.S) = h^{bb-aa}*gamma. hd = h^{bb-aa} = h^{-1}.
    hd = pow(g, (bb - aa) % n, p)
    # partition gamma-set into <hd>-orbits
    gammas = set(gmap.keys())
    seen = set(); orbits = []
    for gm in sorted(gammas):
        if gm in seen: continue
        orb = []; x = gm
        for _ in range(n):
            if x in gammas: orb.append(x)
            seen.add(x); x = (x * hd) % p
        orbits.append(orb)
    sizes = sorted(set(len(o) for o in orbits))
    has0 = 0 in gammas
    print(f"\nn={n} line x^{aa},x^{bb} p={p}: #distinct-gamma={ng}  (closed form n*C(n/4,2)+1 = {n*comb(n//4,2)+1})")
    print(f"  #<hd>-orbits={len(orbits)}, orbit sizes={sizes}, gamma=0 present={has0}")
    full = [o for o in orbits if len(o) == n]
    print(f"  full-size-{n} orbits={len(full)}  => n*{len(full)} = {n*len(full)} ; C(n/4,2)={comb(n//4,2)}")
    print(f"  predicted: n*C(n/4,2)+1 = {n*comb(n//4,2)} + 1 = {n*comb(n//4,2)+1}; "
          f"actual n*{len(full)}+(non-full {ng-n*len(full)}) = {ng}")
    # index structure of one orbit-rep's witness sets: do they live in mu_{n/4}?
    # pick a full orbit, take a witness, show its 4 indices mod (n/4) structure
    if full:
        gm0 = full[0][0]
        wit = gmap[gm0][0]
        print(f"  sample gamma={gm0}: witness a-set indices={wit}  (mod n/4={n//4}: {tuple(i%(n//4) for i in wit)})")

if __name__ == '__main__':
    print("gamma-census MECHANISM on antipodal-adjacent worst line (exact, proper mu_n)")
    analyze(16, 4)
    analyze(32, 5)
