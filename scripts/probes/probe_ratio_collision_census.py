#!/usr/bin/env python3
"""The ratio-collision census: at the ladder stack (X^3, X^2) over mu_8 in F12289,
compute all C(8,3) residual ratios gamma_T = -e_T(u0)/e_T(u1); the boundary-slice
exact law says badSet = this image. Expect 40 distinct (spectrum) — classify the
16 collisions by subset structure."""
from itertools import combinations
from collections import defaultdict
p, n, k = 12289, 8, 2
g = 8246
dom = [pow(g, i, p) for i in range(n)]
u0 = [pow(x, 3, p) for x in dom]
u1 = [pow(x, 2, p) for x in dom]
def det3(rows):
    (a,b,c),(d,e,f),(gg,h,i) = rows
    return (a*(e*i - f*h) - b*(d*i - f*gg) + c*(d*h - e*gg)) % p
def residual(T, y):
    rows = [(1, dom[i], y[i]) for i in T]
    return det3(rows)
ratios = {}
for T in combinations(range(n), 3):
    r0 = residual(T, u0); r1 = residual(T, u1)
    assert r1 % p != 0, T
    gam = (-r0) * pow(r1, p-2, p) % p
    ratios.setdefault(gam, []).append(T)
print(f"distinct ratios: {len(ratios)} (spectrum predicts 40); subsets: {sum(len(v) for v in ratios.values())}")
coll = {g_: Ts for g_, Ts in ratios.items() if len(Ts) > 1}
print(f"collided gammas: {len(coll)}")
# classify: index-shift structure? exponents mod 8
for gam, Ts in sorted(coll.items())[:8]:
    print(f"  γ={gam}: {Ts}")
# check shift-orbit: T+1 mod 8 maps gamma how? (rotation equivariance: gamma -> g*gamma?)
T0 = (0,1,2)
g0 = (-residual(T0,u0))*pow(residual(T0,u1),p-2,p)%p
T1 = tuple((i+1)%n for i in T0)
g1 = (-residual(tuple(sorted(T1)),u0))*pow(residual(tuple(sorted(T1)),u1),p-2,p)%p
print(f"rotation check: γ(T)={g0}, γ(T+1)={g1}, g·γ(T)={g0*g % p} (expect equal)")

# THE SCHUR LAW CHECK: gamma_T = -(sum of domain points of T)?
ok = 0
for T in combinations(range(n), 3):
    r0 = residual(T, u0); r1 = residual(T, u1)
    gam = (-r0) * pow(r1, p-2, p) % p
    s = (-(dom[T[0]] + dom[T[1]] + dom[T[2]])) % p
    if gam == s: ok += 1
print(f"Schur law gamma_T = -e1(T): {ok}/56")
# and at k=3 (t=4, u0=x^4, u1=x^3) to confirm generality
def det4(rows):
    import itertools
    s = 0
    for perm in itertools.permutations(range(4)):
        sign = 1
        pl = list(perm)
        for i in range(4):
            for j in range(i+1,4):
                if pl[i]>pl[j]: sign = -sign
        prod = 1
        for i in range(4): prod = prod*rows[i][perm[i]] % p
        s = (s + sign*prod) % p
    return s
u0b = [pow(x,4,p) for x in dom]; u1b = [pow(x,3,p) for x in dom]
ok4 = tot4 = 0
for T in combinations(range(n), 4):
    rows1 = [(1, dom[i], dom[i]**2 % p, u1b[i]) for i in T]
    rows0 = [(1, dom[i], dom[i]**2 % p, u0b[i]) for i in T]
    r1 = det4(rows1); r0 = det4(rows0)
    if r1 == 0: continue
    tot4 += 1
    gam = (-r0)*pow(r1,p-2,p)%p
    s = (-sum(dom[i] for i in T))%p
    if gam == s: ok4 += 1
print(f"k=3 Schur law: {ok4}/{tot4}")
