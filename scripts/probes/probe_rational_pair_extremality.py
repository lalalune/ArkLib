#!/usr/bin/env python3
"""WB-2 open-core probe: among doubly-rational stacks at (17,8,2,w=2,|T|>=6),
which rational pairs maximize the exact bad-gamma count? Compare random rational
pairs (R/l, deg l <= 2 nonvanishing on D, deg R <= 3) vs structured smooth pairs."""
import random
from itertools import combinations
random.seed(371)
p, n, k, g, w = 17, 8, 2, 2, 2
dom = [pow(g, i, p) for i in range(n)]
t_min = n - w  # 6
codewords = [tuple((a + b*x) % p for x in dom) for a in range(p) for b in range(p)]
def dist(u, c): return sum(1 for a,b in zip(u,c) if a != b)
def explainable(line): return any(dist(line, c) <= n - t_min for c in codewords)
def joint_ok(T, u0, u1):
    for u in (u0, u1):
        ok = False
        for c in codewords:
            if all(c[i] == u[i] for i in T): ok = True; break
        if not ok: return False
    return True
def bad_count(u0, u1):
    cnt = 0
    for gam in range(p):
        line = tuple((u0[i] + gam*u1[i]) % p for i in range(n))
        found = False
        for c in codewords:
            if dist(line, c) > n - t_min: continue
            A = [i for i in range(n) if c[i] == line[i]]
            for T in combinations(A, t_min):
                if not joint_ok(T, u0, u1): found = True; break
            if found: break
        if found: cnt += 1
    return cnt
def evalpoly(co, x):
    a = 0
    for c in reversed(co): a = (a*x + c) % p
    return a
def rational_word(lco, rco):
    out = []
    for x in dom:
        lv = evalpoly(lco, x)
        if lv == 0: return None
        out.append(evalpoly(rco, x) * pow(lv, p-2, p) % p)
    return tuple(out)

best_rand = 0; best_rand_pair = None
for _ in range(250):
    l0 = [random.randrange(p) for _ in range(3)]; r0 = [random.randrange(p) for _ in range(4)]
    l1 = [random.randrange(p) for _ in range(3)]; r1 = [random.randrange(p) for _ in range(4)]
    u0 = rational_word(l0, r0); u1 = rational_word(l1, r1)
    if u0 is None or u1 is None: continue
    c = bad_count(u0, u1)
    if c > best_rand: best_rand = c; best_rand_pair = (l0,r0,l1,r1)
print(f"random rational pairs: max bad = {best_rand}", flush=True)

# structured smooth pairs: monomial stacks (x^a, x^b), incl KKH26 (x^a, x^{a-1})
best_mono = 0; arg = None
for a in range(8):
    for b in range(8):
        if a == b: continue
        u0 = tuple(pow(x, a, p) for x in dom); u1 = tuple(pow(x, b, p) for x in dom)
        c = bad_count(u0, u1)
        if c > best_mono: best_mono = c; arg = (a, b)
print(f"monomial pairs (x^a, x^b): max bad = {best_mono} at (a,b)={arg}", flush=True)

# rational pairs with smooth-structured denominators: l = X^2 - c (c in subgroup squares)
best_sm = 0; argsm = None
for c0 in range(1, p):
    for c1 in range(1, p):
        l0 = [(-c0) % p, 0, 1]; l1 = [(-c1) % p, 0, 1]
        for _ in range(6):
            r0 = [random.randrange(p) for _ in range(4)]; r1 = [random.randrange(p) for _ in range(4)]
            u0 = rational_word(l0, r0); u1 = rational_word(l1, r1)
            if u0 is None or u1 is None: continue
            cc = bad_count(u0, u1)
            if cc > best_sm: best_sm = cc; argsm = (c0, c1)
print(f"quadratic-denominator pairs: max bad = {best_sm} at (c0,c1)={argsm}", flush=True)
print(f"\nWB-2 sup reference: (w+3) = {w+3}; q = {p}", flush=True)
