#!/usr/bin/env python3
"""Targeted band-3 certificate extractor at (p=17, n=8, k=4, dom=<2>), delta=1/4 (|T|>=6).
Scans wt<=2 x wt<=2 stacks (normalized), exact bad-gamma count, emits Lean-ready certs."""
import sys
from itertools import combinations, product

p, n, k, g = 17, 8, 4, 2
dom = [pow(g, i, p) for i in range(n)]  # [1,2,4,8,16,15,13,9]
t_min = 6

def interp(pts):  # Lagrange deg<4 through 4 (x,y) pts -> coeff list deg<4
    coeffs = [0]*4
    for (xi, yi) in pts:
        li = [1]; denom = 1
        for (xj, _) in pts:
            if xj == xi: continue
            li = [(c * (-xj)) % p for c in li] + [0]
            for idx in range(len(li)-1): li[idx+1] = (li[idx+1] + ([1]+[0]*10)[0]*0) % p
        # redo polynomial mult properly
    return None

def polymul(a, b):
    r = [0]*(len(a)+len(b)-1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            r[i+j] = (r[i+j] + x*y) % p
    return r

def lagrange(pts):
    co = [0]*len(pts)
    for (xi, yi) in pts:
        num = [1]; den = 1
        for (xj, _) in pts:
            if xj == xi: continue
            num = polymul(num, [(-xj) % p, 1])
            den = den * (xi - xj) % p
        f = yi * pow(den, p-2, p) % p
        for idx in range(len(num)):
            co[idx] = (co[idx] + f*num[idx]) % p
    return co

def ev(co, x):
    a = 0
    for c in reversed(co): a = (a*x + c) % p
    return a

# syndrome setup: c in code iff c = eval of deg<k poly; use: word w in code iff
# lagrange through first 4 coords (as poly deg<4) matches the rest AND deg<k... k=4 so
# any word agreeing with its own 4-pt interpolation everywhere is in code.
def in_code(w):
    co = lagrange(list(zip(dom[:4], w[:4])))
    return all(ev(co, dom[i]) == w[i] for i in range(4, n))

# wt<=2 eta dict by syndrome (use 4-pt interpolation residual as syndrome surrogate is
# messy; instead precompute ALL eta wt<=2 and their "code-coset id" = tuple of
# (w - interp(first4(w)))(dom[4:]) ... simpler: brute candidates per line directly.)
etas = [tuple([0]*n)]
for i in range(n):
    for v in range(1, p):
        e = [0]*n; e[i] = v; etas.append(tuple(e))
for i, j in combinations(range(n), 2):
    for v1 in range(1, p):
        for v2 in range(1, p):
            e = [0]*n; e[i] = v1; e[j] = v2; etas.append(tuple(e))

def coset_id(w):
    co = lagrange(list(zip(dom[:4], w[:4])))
    return tuple((w[i] - ev(co, dom[i])) % p for i in range(4, n))

from collections import defaultdict
eta_by_id = defaultdict(list)
for e in etas:
    eta_by_id[coset_id(e)].append(e)

def joint_fails(T, u0, u1):
    # joint on T: exist codewords c0,c1 with ci|T = ui|T. k=4: candidate = interp of any
    # 4 pts of T, must match all of T. Check both rows; joint OK iff both explainable.
    for u in (u0, u1):
        pts = [(dom[i], u[i]) for i in T[:4]]
        co = lagrange(pts)
        if not all(ev(co, dom[i]) == u[i] for i in T):
            return True  # this row not explainable on T -> joint fails
    return False

def bad_gammas(u0, u1):
    bad = {}
    for gam in range(p):
        line = tuple((u0[i] + gam*u1[i]) % p for i in range(n))
        cid = coset_id(line)
        found = None
        for e in eta_by_id.get(cid, []):
            A = [i for i in range(n) if e[i] == 0]
            if len(A) < t_min: continue
            c = tuple((line[i] - e[i]) % p for i in range(n))
            for T in combinations(A, t_min):
                if joint_fails(list(T), u0, u1):
                    co = lagrange([(dom[i], c[i]) for i in T[:4]])
                    found = (T, c, co)
                    break
            if found: break
        if found: bad[gam] = found
    return bad

best = (0, None)
u1cands = []
for jpos in range(1, n):
    for b in range(1, p):
        u1 = [0]*n; u1[0] = 1; u1[jpos] = b; u1cands.append(tuple(u1))
u0cands = []
for i, j in combinations(range(n), 2):
    for v2 in range(1, p):
        u0 = [0]*n; u0[i] = 1; u0[j] = v2; u0cands.append(tuple(u0))

total = len(u1cands)*len(u0cands)
cnt = 0
for u1 in u1cands:
    for u0 in u0cands:
        cnt += 1
        bg = bad_gammas(u0, u1)
        if len(bg) > best[0]:
            best = (len(bg), (u0, u1, bg))
            print(f"NEW BEST B6 >= {best[0]} at u0={u0} u1={u1} gammas={sorted(bg)}", flush=True)
            if best[0] >= 8: break
    if best[0] >= 8: break
    if cnt % 5000 == 0: print(f"...{cnt}/{total}", flush=True)

b, (u0, u1, bg) = best
print(f"\nFINAL: B6 >= {b}, u0={u0}, u1={u1}")
for gam in sorted(bg):
    T, c, co = bg[gam]
    print(f"gamma={gam}: T={T} cw={c} poly={co}")
