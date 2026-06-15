#!/usr/bin/env python3
"""
wf-NH (#407) fast n=32 p-independence check: ONE direction (the n=16 winner pattern (a=10,b=4)
lifted to n=32, plus the analogous low-far monomial b=k=4), across 3 primes incl >2^12.
Reuses the precomputed nulls but computes them per-prime ONCE and tests only ~4 monomial dirs
+ a handful of general dirs => fast.  Decides: is the over-det incidence p-independent at n=32?
"""
import sys, itertools
sys.path.insert(0, 'scripts/probes')
from probe_farline_incidence_exact import find_prime_cong1
from prize_workspace import get_W
from probe_wf2NH_decisive import precompute_nulls, inc_from_nulls, mono, v2

n, k, size = 32, 4, 6
r = n - size
print(f"n={n} k={k} over-det size={size}(s-k={size-k}) r={r} delta={r/n:.4f}", flush=True)
# directions to test: low-far monomials (b in [k,size)) x a few offsets; the worst is a high a, low b.
dirs = [('mono', a, b) for b in range(size) for a in (n-6, n-5, n-4, n-2, n-1) if a != b]
results = {}
for plo in [200003, 5000011, 16777259]:
    p = find_prime_cong1(n, plo); S = list(get_W(n, p).S)
    print(f"  building nulls p={p}...", flush=True)
    nulls = precompute_nulls(S, p, k, size)
    best = -1; barg = None
    for (_, a, b) in dirs:
        I = inc_from_nulls(mono(a, S, p), mono(b, S, p), nulls, p)
        if p > I > best: best = I; barg = (a, b)
    results[p] = best
    print(f"  p={p} v2={v2(p)} {'>2^12' if p>4096 else ''}: best over tested dirs = {best} at {barg}", flush=True)
vals = list(results.values())
print(f"-> over-det incidence (sampled dirs) p-INDEPENDENT: {len(set(vals))==1}; vals={vals}", flush=True)
print("DONE")
