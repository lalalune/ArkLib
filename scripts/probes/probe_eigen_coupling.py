#!/usr/bin/env python3
"""The coupling question: does badness concentrate on eigencomponents? At (13,6,1,2)
decompose stacks u = u+ + u-, measure bad counts of (u0,u1) vs the four eigen-projected
stacks (u0±, u1±). k=1: T u (i) = u(sigma i) (weight x^0 = 1) — plain involution."""
from itertools import combinations
from collections import Counter
import random
random.seed(99)
q, n, k, w = 13, 6, 1, 2
g = 4
dom = [pow(g, i, q) for i in range(n)]
sigma_val = {x: (-pow(x, q-2, q)) % q for x in dom}
sigma = [dom.index(sigma_val[dom[i]]) for i in range(n)]
t_min = n - w
inv2 = pow(2, q-2, q)
def T(u): return tuple(u[sigma[i]] for i in range(n))
def plus(u):
    Tu = T(u)
    return tuple((u[i] + Tu[i]) * inv2 % q for i in range(n))
def minus(u):
    Tu = T(u)
    return tuple((u[i] - Tu[i]) * inv2 % q for i in range(n))
def bad_count(u0, u1):
    cnt = 0
    for gam in range(q):
        line = tuple((u0[i] + gam*u1[i]) % q for i in range(n))
        found = False
        for c, m in Counter(line).most_common():
            if m < t_min: break
            A = [i for i in range(n) if line[i] == c]
            paircnt = Counter((u0[i], u1[i]) for i in A)
            if paircnt.most_common(1)[0][1] >= t_min: continue
            found = True; break
        if found: cnt += 1
    return cnt
# stats: for random stacks with bad count >= 2, compare to eigen-projections
rows = []
for _ in range(120000):
    u0 = tuple(random.randrange(q) for _ in range(n))
    u1 = tuple(random.randrange(q) for _ in range(n))
    b = bad_count(u0, u1)
    if b >= 2:
        bpp = bad_count(plus(u0), plus(u1))
        bmm = bad_count(minus(u0), minus(u1))
        bpm = bad_count(plus(u0), minus(u1))
        bmp = bad_count(minus(u0), plus(u1))
        rows.append((b, bpp, bmm, bpm, bmp, u0, u1))
        if len(rows) <= 8:
            print(f"b={b}  (++)={bpp} (--)={bmm} (+-)={bpm} (-+)={bmp}", flush=True)
print(f"\ntotal stacks with b>=2: {len(rows)}")
viol = [r for r in rows if r[0] > max(r[1], r[2], r[3], r[4])]
print(f"stacks where mixed bad EXCEEDS all four eigen-projected: {len(viol)}")
for r in viol[:5]: print(f"  b={r[0]} eigen=({r[1]},{r[2]},{r[3]},{r[4]}) u0={r[5]} u1={r[6]}")
