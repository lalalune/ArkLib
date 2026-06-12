#!/usr/bin/env python3
"""Ownership-degeneracy probe at (13,6,1,w=2), k=1. Residual of a 2-tuple (i,j):
e(y) = y(j) - y(i). Ownership of bad gamma = max over valid witnesses S of
#{ordered pairs (i,j) in S^2 : u1(i) != u1(j)}. Compare Mobius extremal vs generic.
Count bound: #bad * M <= n(n-1) = 30."""
from itertools import combinations
from collections import Counter
import random
random.seed(5)
q, n, k, w = 13, 6, 1, 2
g = 4
dom = [pow(g, i, q) for i in range(n)]
t_min = n - w  # 4

def witnesses_and_bad(u0, u1):
    out = {}
    for gam in range(q):
        line = tuple((u0[i] + gam*u1[i]) % q for i in range(n))
        best = -1
        for c, m in Counter(line).most_common():
            if m < t_min: break
            A = [i for i in range(n) if line[i] == c]
            for size in range(len(A), t_min - 1, -1):
                for T in combinations(A, size):
                    # joint fails iff u0 or u1 nonconstant on T
                    if len(set(u0[i] for i in T)) > 1 or len(set(u1[i] for i in T)) > 1:
                        own = sum(1 for i in T for j in T if i != j and u1[i] != u1[j])
                        if own > best: best = own
        if best >= 0:
            out[gam] = best
    return out

# the Mobius extremal from the exhaustive scan
u0 = (0, 0, 0, 0, 1, 1); u1 = (0, 1, 1, 0, 2, 2)
ext = witnesses_and_bad(u0, u1)
print(f"MOBIUS EXTREMAL: bad gammas + max-ownership: {ext}")
print(f"  #bad = {len(ext)}, count bound check: sum of min-ownerships vs 30")
# generic stacks with >= 2 bad
gens = []
for _ in range(200000):
    v0 = tuple(random.randrange(q) for _ in range(n))
    v1 = tuple(random.randrange(q) for _ in range(n))
    o = witnesses_and_bad(v0, v1)
    if len(o) >= 2:
        gens.append((len(o), sorted(o.values())))
        if len(gens) >= 40: break
own_ext = sorted(ext.values())
own_gen = [o for _, oo in gens for o in oo]
print(f"extremal ownerships: {own_ext}")
print(f"generic (b>=2) ownership distribution: min={min(own_gen)}, " 
      f"mean={sum(own_gen)/len(own_gen):.1f}, max={max(own_gen)} over {len(own_gen)} bad scalars")
print(f"n(n-1) = {n*(n-1)}; extremal #bad * min-own = {len(ext)} * {min(own_ext)} = {len(ext)*min(own_ext)}")
