#!/usr/bin/env python3
"""
The block-design ladder (p=12289): can a third SMALL block escalate past 20?

Design: big blocks A1={0..5}, A2={6..11} (deg<3 q_i, r_i), plus a small
block A3 of size a3 in {3,4,5} on the leftover points {12..15} (plus one
glued block point when a3=5).  A small-block scalar needs a witness
A3 + (7-a3) off-points sharing ONE gamma: each off-point x in A_i gives the
linear equation  (r_i - r3)(x) = gamma * (q_i - q3)(x).

For FIXED gammas and chosen collision points, all equations are LINEAR in
the 18 coefficients of (q1,q2,r1,r2,q3,r3).  We solve the joint system
(gluing + collisions) exactly mod p, randomize the kernel, and run the
exact census.  Predictions: (6,6,3) -> 23, (6,6,4) -> 24, (6,6,5) -> 25;
the obligation needs the TRUE max <= 31.
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

def solve_linear(rows, rhs, nv, rng):
    """solve rows*x = rhs mod p, random kernel coords; None if infeasible."""
    m = len(rows)
    A = [rows[r][:] + [rhs[r]] for r in range(m)]
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
                A[r2] = [(A[r2][t] - f * A[rr][t]) % p
                         for t in range(nv + 1)]
        piv.append(c)
        rr += 1
        if rr == m:
            break
    for r2 in range(rr, m):
        if A[r2][nv] % p and not any(A[r2][:nv]):
            return None
    free = [c for c in range(nv) if c not in piv]
    sol = [0] * nv
    for c in free:
        sol[c] = rng.randrange(p)
    for idx in range(len(piv) - 1, -1, -1):
        c = piv[idx]
        v = A[idx][nv]
        for c2 in range(c + 1, nv):
            v = (v - A[idx][c2] * sol[c2]) % p
        sol[c] = v % p
    return sol

# variable layout: q1(0:3) q2(3:6) r1(6:9) r2(9:12) q3(12:15) r3(15:18)
def var_row(block_q, block_r, x, gam):
    """(r_blk - r3)(x) - gam*(q_blk - q3)(x) = 0 -> row over 18 vars."""
    row = [0] * 18
    for t in range(3):
        xt = pow(x, t, p)
        row[block_r + t] = xt                    # +r_blk
        row[15 + t] = (row[15 + t] - xt) % p     # -r3
        row[block_q + t] = (-gam * xt) % p       # -gam*q_blk
        row[12 + t] = (row[12 + t] + gam * xt) % p   # +gam*q3
    return row

def build_and_census(a3, trials, seed):
    best = 0
    off_need = s - a3            # off-points per small-block witness
    for trial in range(trials):
        rng = random.Random(seed + trial)
        A3 = [12, 13, 14] if a3 == 3 else (
             [12, 13, 14, 15] if a3 == 4 else [12, 13, 14, 15, 0])
        n3 = 16 - a3 - (12 if a3 < 5 else 11)    # leftover free pts count
        # small-block scalars: m(a3) = floor(off-pool / off_need)
        offpool = [i for i in range(12) if i not in A3]
        nsc = min(len(offpool) // off_need, a3)  # modest target
        gams3 = rng.sample(range(2, p), nsc)
        rows, rhs = [], []
        # gluing for a3=5: q3,r3 agree with q1,r1 at point 0
        if a3 == 5:
            x0 = D[0]
            for (a_, b_) in ((0, 12), (6, 15)):   # q1 vs q3 ; r1 vs r3
                row = [0] * 18
                for t in range(3):
                    xt = pow(x0, t, p)
                    row[a_ + t] = xt
                    row[b_ + t] = (-xt) % p
                rows.append(row)
                rhs.append(0)
        used = []
        pool = offpool[:]
        rng.shuffle(pool)
        for gi in range(nsc):
            pts = pool[gi * off_need:(gi + 1) * off_need]
            if len(pts) < off_need:
                break
            used.append((gams3[gi], pts))
            for i in pts:
                bq, br = (0, 6) if i < 6 else (3, 9)
                rows.append(var_row(bq, br, D[i], gams3[gi]))
                rhs.append(0)
        sol = solve_linear(rows, rhs, 18, rng)
        if sol is None:
            continue
        q1, q2 = sol[0:3], sol[3:6]
        r1, r2 = sol[6:9], sol[9:12]
        q3, r3 = sol[12:15], sol[15:18]
        if q1 == q2 or q1 == q3 or q2 == q3:
            continue
        u0, u1 = [0] * n, [0] * n
        for i in range(6):
            u1[i] = peval(q1, D[i]); u0[i] = peval(r1, D[i])
        for i in range(6, 12):
            u1[i] = peval(q2, D[i]); u0[i] = peval(r2, D[i])
        for i in A3:
            if i == 0:
                continue
            u1[i] = peval(q3, D[i]); u0[i] = peval(r3, D[i])
        for i in range(12, 16):
            if i not in A3:   # leftover: steer 2 fresh gammas
                ga, gb = rng.randrange(1, p), rng.randrange(1, p)
                if ga == gb:
                    gb = gb % (p - 1) + 1
                x = D[i]
                rhs1 = (peval(r1, x) + ga * peval(q1, x)) % p
                rhs2 = (peval(r2, x) + gb * peval(q2, x)) % p
                R1x = (rhs1 - rhs2) * pow((ga - gb) % p, p - 2, p) % p
                u1[i] = R1x
                u0[i] = (rhs1 - ga * R1x) % p
        c = census_count(u0, u1)
        if c > best:
            best = c
            print(f"  [(6,6,{a3})] trial {trial}: total = {c} "
                  f"(planted small-block scalars: {len(used)})")
    return best

results = {}
for a3 in (3, 4, 5):
    results[a3] = build_and_census(a3, 15, 4242 + a3 * 100)
print(f"LADDER RESULTS: {results} -- record 20, obligation 31")
