#!/usr/bin/env python3
"""Renormalization test: (q,n,k,w)=(13,12,1,4) — window check: 2w+k+1=10 <= 12 (below UDR),
3w+k=13 > 12 (beyond ladder). Conjecture from scale 1: max bad = w+1 = 5, extremals
Mobius-invariant under sigma(x) = -1/x. Domain = F13* (mu_12)."""
import random
from itertools import combinations
from collections import Counter
random.seed(13)
q, n, k, w = 13, 12, 1, 4
dom = list(range(1, 13))
t_min = n - w  # 8
sigma = {x: (-pow(x, q-2, q)) % q for x in dom}
orbits = []
seen = set()
for x in dom:
    if x in seen: continue
    y = sigma[x]
    if y == x: orbits.append((x,)); seen.add(x)
    else: orbits.append((x, y)); seen |= {x, y}
print(f"orbits ({len(orbits)}):", orbits, flush=True)
idx = {x: i for i, x in enumerate(dom)}
def bad_count(u0, u1):
    cnt = 0
    for gam in range(q):
        line = tuple((u0[i] + gam*u1[i]) % q for i in range(n))
        found = False
        for c, m in Counter(line).most_common():
            if m < t_min: break
            A = [i for i in range(n) if line[i] == c]
            # joint fails iff u0 or u1 nonconstant on T; T subset of A size t_min
            # nonconstant on SOME T ⟺ (since any T size 8 of |A| >= 8)… check all T? too many.
            # joint exists iff exists T with both rows constant. For k=1 rows must be constant on T.
            # u0 constant on some 8-subset of A ⟺ max multiplicity of u0|A >= 8. Same u1. And same T:
            # need T ⊆ A, |T|=8, u0 const on T and u1 const on T ⟺ exists (a,b): |{i ∈ A : u0[i]=a, u1[i]=b}| >= 8
            paircnt = Counter((u0[i], u1[i]) for i in A)
            if paircnt.most_common(1)[0][1] >= t_min:
                continue  # joint exists for this A... but other witnesses T might still fail
            # bad requires SOME witness with line-agreement and no joint: if pair-mult < 8, any T
            # containing two distinct pair-classes has no joint => found
            found = True
            break
        if found: cnt += 1
    return cnt
def invariant_word(vals):
    u = [0]*n
    for o, v in zip(orbits, vals):
        for x in o: u[idx[x]] = v
    return tuple(u)
best_inv = 0; arg = None
T = 60000
for trial in range(T):
    v0 = [random.randrange(q) for _ in orbits]
    v1 = [random.randrange(q) for _ in orbits]
    u0 = invariant_word(v0); u1 = invariant_word(v1)
    c = bad_count(u0, u1)
    if c > best_inv:
        best_inv = c; arg = (v0, v1)
        print(f"inv trial {trial}: new max {best_inv} at orbit-values {v0} | {v1}", flush=True)
print(f"\nMobius-invariant sample max: {best_inv} (w+1 = {w+1})", flush=True)
best_gen = 0
for trial in range(20000):
    u0 = tuple(random.randrange(q) for _ in range(n))
    u1 = tuple(random.randrange(q) for _ in range(n))
    c = bad_count(u0, u1)
    if c > best_gen:
        best_gen = c
        print(f"gen trial {trial}: new max {best_gen}", flush=True)
print(f"general sample max: {best_gen}", flush=True)
