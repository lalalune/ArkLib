#!/usr/bin/env python3
"""
Multi-block frame designs, exact constructor (p=12289; n=16, k=3, s=7).

The 2-block design reaches 20 bad scalars (census-16 conjecture REFUTED).
Here: B blocks of 6 points, pairwise overlaps <= 2; deg<3 polys q_i (for
R1) and r_i (for R0) on each block, compatible on overlaps.  The
compatibility system is LINEAR in the 3B coefficients -- solved exactly
by Gaussian elimination mod p with randomized kernel coordinates (the
all-equal solution is excluded by requiring pairwise-distinct q's; retry
with fresh randomness if degenerate).  Free points (in no block) are
steered to fresh gammas.

Each block contributes up to 16-6 = 10 candidate scalars
gamma = -(R0(x)-r_i(x))/(R1(x)-q_i(x)) per off-block point x; B=4 gives
40 > 31: if realizable with few collisions, the round-7 obligation
SubCeilingInteriorCeiling(12289) <= 31 is FALSE.  Census is exact
(all C(16,7) subsets, joint-clause faithful).
"""
import itertools, random

p, n, s = 12289, 16, 7

g0 = next(g for g in range(2, 500)
          if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)))
w = pow(g0, (p - 1) // n, p)
assert pow(w, n, p) == 1 and all(pow(w, j, p) != 1 for j in range(1, n))
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

def interp(pts, vals):
    m = len(pts)
    coeffs = [0] * m
    for i in range(m):
        num = [1]
        den = 1
        for j in range(m):
            if j == i:
                continue
            num = polmul(num, [(-pts[j]) % p, 1])
            den = den * ((pts[i] - pts[j]) % p) % p
        ci = vals[i] * pow(den, p - 2, p) % p
        for t in range(len(num)):
            coeffs[t] = (coeffs[t] + ci * num[t]) % p
    return coeffs

def solve_block_polys(blocks, rng):
    """coefficients c[i][0..2] for deg<3 poly on block i; constraints
    q_i(x) = q_j(x) for x in overlap(i,j); random kernel solution."""
    B = len(blocks)
    nv = 3 * B
    rows = []
    for i in range(B):
        for j in range(i + 1, B):
            for pt in set(blocks[i]) & set(blocks[j]):
                x = D[pt]
                row = [0] * nv
                for t in range(3):
                    row[3 * i + t] = pow(x, t, p)
                    row[3 * j + t] = (-pow(x, t, p)) % p
                rows.append(row)
    # gaussian elimination -> basis of kernel; random kernel vector
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
    for r2 in range(len(piv) - 1, -1, -1):
        c = piv[r2]
        v = 0
        for c2 in range(c + 1, nv):
            v = (v + A[r2][c2] * sol[c2]) % p
        sol[c] = (-v) % p
    return [[sol[3 * i], sol[3 * i + 1], sol[3 * i + 2]] for i in range(B)]

def census(u0, u1):
    bad = {}
    for S in itertools.combinations(range(n), s):
        pts = [D[i] for i in S]
        a = interp(pts, [u0[i] for i in S])
        b = interp(pts, [u1[i] for i in S])
        ta = [a[t] if t < len(a) else 0 for t in range(3, s)]
        tb = [b[t] if t < len(b) else 0 for t in range(3, s)]
        if all(x == 0 for x in tb):
            continue
        j = next(t for t in range(len(tb)) if tb[t])
        gam = (-ta[j]) * pow(tb[j], p - 2, p) % p
        if all((ta[t] + gam * tb[t]) % p == 0 for t in range(len(tb))):
            bad.setdefault(gam, []).append(S)
    return bad

DESIGNS = {
    "3-block": [list(range(0, 6)), list(range(6, 12)),
                [0, 1, 6, 7, 12, 13]],
    "4-block": [list(range(0, 6)), list(range(6, 12)),
                [0, 1, 6, 7, 12, 13], [2, 3, 8, 9, 14, 15]],
    "5-block": [list(range(0, 6)), list(range(6, 12)),
                [0, 1, 6, 7, 12, 13], [2, 3, 8, 9, 14, 15],
                [4, 5, 10, 11, 12, 14]],
}

for name, blocks in DESIGNS.items():
    # sanity: pairwise overlaps <= 2
    for i in range(len(blocks)):
        for j in range(i + 1, len(blocks)):
            assert len(set(blocks[i]) & set(blocks[j])) <= 2, (name, i, j)
    covered = set().union(*[set(b) for b in blocks])
    freepts = [i for i in range(n) if i not in covered]
    best, best_detail = 0, None
    for trial in range(12):
        rng = random.Random(9000 + trial)
        qs = solve_block_polys(blocks, rng)
        rs = solve_block_polys(blocks, rng)
        if any(qs[i] == qs[j] for i in range(len(blocks))
               for j in range(i + 1, len(blocks))):
            continue
        u0, u1 = [None] * n, [None] * n
        for bi, blk in enumerate(blocks):
            for i in blk:
                u1[i] = peval(qs[bi], D[i])
                u0[i] = peval(rs[bi], D[i])
        for i in freepts:
            u1[i] = rng.randrange(p)
            u0[i] = rng.randrange(p)
        bad = census(u0, u1)
        if len(bad) > best:
            best = len(bad)
            wc = sorted(len(v) for v in bad.values())
            best_detail = wc[-6:]
    print(f"[{name}] max total bad over 12 trials = {best} "
          f"(top witness-counts {best_detail})")
print("REFERENCE: 2-block reached 20; census-old-record 16; obligation 31")
