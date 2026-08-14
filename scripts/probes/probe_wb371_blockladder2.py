#!/usr/bin/env python3
"""
Block-ladder, corrected constructor (p=12289): (6,6,3) + fiber-tuned
small-block scalars.

The pencil bottleneck: a small-block scalar gamma with witness
A3 + {x,y in A1} + {u,v in A2} needs the pencil members
(r1-r3) - gamma*(q1-q3) to vanish at x,y and (r2-r3) - gamma*(q2-q3) at
u,v -- a deg<=2 poly has <=2 roots, so 2 points per big block is the MAX
(4+ points per block forces full pencil degeneration = the q-collapse seen
in blockladder).  Equations are linear in the 18 block-poly coefficients
for FIXED gammas and points: solve jointly for ns in {1,2,3} small scalars,
randomize kernel, exact census.  Watch for: degenerate pencils (q1=q3 etc),
the f12-collapse, and the realized total vs record 20 / obligation 31.
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
MATS = []
for S in SUBS:
    pts = [D[i] for i in S]
    M = [[0] * s for _ in range(4)]
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

def census_set(u0, u1):
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
    return bad

def solve_linear(rows, nv, rng):
    m = len(rows)
    A = [r[:] for r in rows]
    piv = []
    rr = 0
    for c in range(nv):
        pr = next((r for r in range(rr, m) if A[r][c]), None)
        if pr is None:
            continue
        A[rr], A[pr] = A[pr], A[rr]
        inv = pow(A[rr][c], p - 2, p)
        A[rr] = [v * inv % p for v in A[rr]]
        for r2 in range(m):
            if r2 != rr and A[r2][c]:
                f = A[r2][c]
                A[r2] = [(A[r2][t] - f * A[rr][t]) % p for t in range(nv)]
        piv.append(c)
        rr += 1
        if rr == m:
            break
    free = [c for c in range(nv) if c not in piv]
    sol = [0] * nv
    for c in free:
        sol[c] = rng.randrange(p)
    for idx in range(len(piv) - 1, -1, -1):
        c = piv[idx]
        v = 0
        for c2 in range(c + 1, nv):
            v = (v + A[idx][c2] * sol[c2]) % p
        sol[c] = (-v) % p
    return sol

# vars: q1(0:3) q2(3:6) r1(6:9) r2(9:12) q3(12:15) r3(15:18)
def pencil_row(qb, rb, x, gam):
    """(r_b - r3)(x) - gam*(q_b - q3)(x) = 0"""
    row = [0] * 18
    for t in range(3):
        xt = pow(x, t, p)
        row[rb + t] = xt
        row[15 + t] = (row[15 + t] - xt) % p
        row[qb + t] = (-gam * xt) % p
        row[12 + t] = (row[12 + t] + gam * xt) % p
    return row

best_per_ns = {}
for ns_small in (1, 2, 3):
    best = 0
    for trial in range(20):
        rng = random.Random(7000 + 97 * trial + ns_small)
        gams = rng.sample(range(2, p), ns_small)
        # disjoint point pairs per scalar: 2 in A1, 2 in A2
        b1pts = rng.sample(range(0, 6), 2 * ns_small)
        b2pts = rng.sample(range(6, 12), 2 * ns_small)
        rows = []
        for j, gam in enumerate(gams):
            for i in b1pts[2 * j:2 * j + 2]:
                rows.append(pencil_row(0, 6, D[i], gam))
            for i in b2pts[2 * j:2 * j + 2]:
                rows.append(pencil_row(3, 9, D[i], gam))
        sol = solve_linear(rows, 18, rng)
        q1, q2 = sol[0:3], sol[3:6]
        r1, r2 = sol[6:9], sol[9:12]
        q3, r3 = sol[12:15], sol[15:18]
        if q1 == q2 or q1 == q3 or q2 == q3:
            continue
        # also reject pencil degenerations (f13 or f23 constant)
        def degen(qa, ra):
            dq = [(qa[t] - q3[t]) % p for t in range(3)]
            dr = [(ra[t] - r3[t]) % p for t in range(3)]
            if not any(dq):
                return True
            # dr = c*dq?
            jt = next(t for t in range(3) if dq[t])
            c = dr[jt] * pow(dq[jt], p - 2, p) % p
            return all((dr[t] - c * dq[t]) % p == 0 for t in range(3))
        if degen(q1, r1) or degen(q2, r2):
            continue
        u0, u1 = [0] * n, [0] * n
        for i in range(6):
            u1[i] = peval(q1, D[i]); u0[i] = peval(r1, D[i])
        for i in range(6, 12):
            u1[i] = peval(q2, D[i]); u0[i] = peval(r2, D[i])
        for i in (12, 13, 14):
            u1[i] = peval(q3, D[i]); u0[i] = peval(r3, D[i])
        # leftover pt 15: steer two fresh gammas
        ga, gb = rng.randrange(1, p), rng.randrange(1, p)
        if ga == gb:
            gb = gb % (p - 1) + 1
        x = D[15]
        rhs1 = (peval(r1, x) + ga * peval(q1, x)) % p
        rhs2 = (peval(r2, x) + gb * peval(q2, x)) % p
        R1x = (rhs1 - rhs2) * pow((ga - gb) % p, p - 2, p) % p
        u1[15] = R1x
        u0[15] = (rhs1 - ga * R1x) % p
        bad = census_set(u0, u1)
        got_small = sum(1 for g in gams if g in bad)
        if len(bad) > best:
            best = len(bad)
            print(f"  [ns={ns_small}] trial {trial}: total = {len(bad)} "
                  f"(planted small realized: {got_small}/{ns_small})")
    best_per_ns[ns_small] = best
print(f"LADDER-2 RESULTS: {best_per_ns} -- record 20, obligation 31")
