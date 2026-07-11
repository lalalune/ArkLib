#!/usr/bin/env python3
"""Verify the Mobius structure of the window extremal + push adversarial search inside
the Mobius-symmetric family specifically."""
import random
from itertools import combinations
from collections import Counter
random.seed(7)
q, n, k, w = 13, 6, 1, 2
g = 4
dom = [pow(g, i, q) for i in range(n)]
print("domain:", dom)
# the involution x -> -1/x
inv = {x: (-pow(x, q-2, q)) % q for x in dom}
print("x -> -1/x pairs:", {x: inv[x] for x in dom})
u0=(6,8,8,6,7,7); u1=(10,9,9,10,4,4)
for i in range(n):
    j = dom.index(inv[dom[i]])
    assert u0[i] == u0[j] and u1[i] == u1[j], (i, j)
print("CONFIRMED: extremal stack invariant under x -> -1/x")
t_min = n - w
def bad_count(u0, u1):
    cnt = 0; gams = []
    for gam in range(q):
        line = tuple((u0[i] + gam*u1[i]) % q for i in range(n))
        found = False
        for c, m in Counter(line).most_common():
            if m < t_min: break
            A = [i for i in range(n) if line[i] == c]
            for T in combinations(A, t_min):
                if len(set(u0[i] for i in T)) > 1 or len(set(u1[i] for i in T)) > 1:
                    found = True; break
            if found: break
        if found: cnt += 1; gams.append(gam)
    return cnt, gams
c, gams = bad_count(u0, u1)
print(f"extremal bad count = {c}, gammas = {gams}")
# exhaustive over Mobius-invariant stacks: u determined by 3 values (one per orbit)
orbits = []
seen = set()
for i in range(n):
    if i in seen: continue
    j = dom.index(inv[dom[i]])
    orbits.append((i, j)); seen |= {i, j}
print("orbits:", orbits)
best = 0; barg = None
vals = range(q)
for a0 in vals:
    for b0 in vals:
        for c0 in vals:
            u0x = [0]*n
            for (i,j), v in zip(orbits, (a0,b0,c0)): u0x[i] = u0x[j] = v
            for a1 in vals:
                for b1 in vals:
                    for c1 in vals:
                        u1x = [0]*n
                        for (i,j), v in zip(orbits, (a1,b1,c1)): u1x[i] = u1x[j] = v
                        cc, _ = bad_count(tuple(u0x), tuple(u1x))
                        if cc > best:
                            best = cc; barg = (tuple(u0x), tuple(u1x))
print(f"EXHAUSTIVE Mobius-invariant family: max bad = {best} at {barg}")
print(f"reference: w+1 = {w+1}, w+3 = {w+3}, q = {q}")
