#!/usr/bin/env python3
"""
Hill-climb the rung census (p=12289, n=16, k=3, s=7): is 20 the global max?

Fast exact census: for each 7-subset S precompute (once) the 4x7 matrix M_S
whose rows are the degree-3..6 coefficient functionals of the Lagrange
interpolant through points of S.  Then a stack's census is, per subset,
ta = M_S u0|S, tb = M_S u1|S; a bad gamma exists iff tb != 0 and
ta + gamma*tb = 0 has the consistent unique solution.  ~1s per census.

Seeds: 2-block frame stacks (the 20-record construction) + random stacks.
Moves: single-coordinate perturbations of u0/u1, first-improvement accept.
"""
import itertools, random

p, n, s = 12289, 16, 7
g0 = next(g for g in range(2, 500)
          if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)))
w = pow(g0, (p - 1) // n, p)
D = [pow(w, j, p) for j in range(n)]

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return out

def peval(f, x):
    r = 0
    for c in reversed(f):
        r = (r * x + c) % p
    return r

SUBS = list(itertools.combinations(range(n), s))
print(f"precomputing {len(SUBS)} subset matrices ...")
MATS = []
for S in SUBS:
    pts = [D[i] for i in S]
    M = [[0] * s for _ in range(4)]   # rows: coeff 3..6
    for j in range(s):
        num = [1]
        den = 1
        for t in range(s):
            if t == j:
                continue
            num = polmul(num, [(-pts[t]) % p, 1])
            den = den * ((pts[j] - pts[t]) % p) % p
        dinv = pow(den, p - 2, p)
        for row in range(4):
            c = num[row + 3] if row + 3 < len(num) else 0
            M[row][j] = c * dinv % p
    MATS.append((S, M))
print("done.")

def census_count(u0, u1):
    bad = set()
    for S, M in MATS:
        v0 = [u0[i] for i in S]
        v1 = [u1[i] for i in S]
        tb = [sum(M[r][j] * v1[j] for j in range(s)) % p for r in range(4)]
        if not any(tb):
            continue
        ta = [sum(M[r][j] * v0[j] for j in range(s)) % p for r in range(4)]
        j = next(t for t in range(4) if tb[t])
        gam = (-ta[j]) * pow(tb[j], p - 2, p) % p
        if all((ta[t] + gam * tb[t]) % p == 0 for t in range(4)):
            bad.add(gam)
    return len(bad)

def two_block_seed(rng):
    q1 = [rng.randrange(p) for _ in range(3)]
    q2 = [rng.randrange(p) for _ in range(3)]
    r1 = [rng.randrange(p) for _ in range(3)]
    r2 = [rng.randrange(p) for _ in range(3)]
    u0, u1 = [0] * n, [0] * n
    for i in range(6):
        u1[i] = peval(q1, D[i]); u0[i] = peval(r1, D[i])
    for i in range(6, 12):
        u1[i] = peval(q2, D[i]); u0[i] = peval(r2, D[i])
    for i in range(12, 16):
        ga, gb = rng.randrange(1, p), rng.randrange(1, p)
        if ga == gb:
            gb = gb % (p - 1) + 1
        x = D[i]
        rhs1 = (peval(r1, x) + ga * peval(q1, x)) % p
        rhs2 = (peval(r2, x) + gb * peval(q2, x)) % p
        R1x = (rhs1 - rhs2) * pow((ga - gb) % p, p - 2, p) % p
        u1[i] = R1x
        u0[i] = (rhs1 - ga * R1x) % p
    return u0, u1

best_overall = 0
rng = random.Random(31337)
for seed_id in range(4):
    if seed_id < 3:
        u0, u1 = two_block_seed(random.Random(100 + seed_id))
        tag = "2-block"
    else:
        u0 = [rng.randrange(p) for _ in range(n)]
        u1 = [rng.randrange(p) for _ in range(n)]
        tag = "random"
    cur = census_count(u0, u1)
    print(f"[seed {seed_id} {tag}] start = {cur}")
    improved = True
    rounds = 0
    while improved and rounds < 4:
        improved = False
        rounds += 1
        order = [(reg, i) for reg in (0, 1) for i in range(n)]
        rng.shuffle(order)
        for reg, i in order:
            u = u0 if reg == 0 else u1
            old = u[i]
            for _ in range(8):
                u[i] = rng.randrange(p)
                c = census_count(u0, u1)
                if c > cur:
                    cur = c
                    old = u[i]
                    improved = True
                    print(f"  seed {seed_id}: improved to {cur}")
                    break
                u[i] = old
    print(f"[seed {seed_id} {tag}] local max = {cur}")
    best_overall = max(best_overall, cur)
print(f"HILL-CLIMB RESULT: best = {best_overall} (record 20, obligation 31)")
