#!/usr/bin/env python3
"""
Pool-extension probe: construct pool-pair stacks (the 60/60 recipe), then
enumerate the FULL mod-R1 fiber: do constructed pool stacks admit a THIRD
bad scalar?  If fibers are exactly {gamma1, gamma2} (+ zero-class), pool
cliques cap at 2 and the rung ledger closes at ~21 <= 31.
"""
import itertools, random

p, n, k = 12289, 16, 3

def mu_n():
    for g in range(2, 300):
        if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)):
            h = pow(g, (p - 1) // n, p)
            return sorted(pow(h, j, p) for j in range(n))
    raise RuntimeError

D = mu_n()

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return out

def m_of(T):
    out = [1]
    for x in T:
        out = polmul(out, [(-x) % p, 1])
    return out

def polmod(a, b):
    a = [x % p for x in a]
    db = max(i for i in range(len(b)) if b[i] % p)
    inv = pow(b[db], p - 2, p)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] % p
        if c:
            f = (c * inv) % p
            for j in range(db + 1):
                a[i - db + j] = (a[i - db + j] - f * b[j]) % p
    out = [x % p for x in a[:db]]
    return out + [0] * (db - len(out))

def solve_affine(M, rhs):
    rows = len(M); cols = len(M[0])
    Aug = [M[r][:] + [rhs[r]] for r in range(rows)]
    piv = []
    r = 0
    for c in range(cols):
        pr = None
        for rr in range(r, rows):
            if Aug[rr][c] % p:
                pr = rr; break
        if pr is None:
            continue
        Aug[r], Aug[pr] = Aug[pr], Aug[r]
        ip = pow(Aug[r][c], p - 2, p)
        Aug[r] = [(x * ip) % p for x in Aug[r]]
        for rr in range(rows):
            if rr != r and Aug[rr][c] % p:
                f = Aug[rr][c]
                Aug[rr] = [(Aug[rr][i] - f * Aug[r][i]) % p for i in range(cols + 1)]
        piv.append(c)
        r += 1
    for rr in range(r, rows):
        if Aug[rr][cols] % p:
            return None
    base = [0] * cols
    for i, c in enumerate(piv):
        base[c] = Aug[i][cols]
    return base, cols - len(piv)

SUBS7 = list(itertools.combinations(range(n), 7))

def fiber_gammas(R0, R1):
    R1 = R1[:]
    lead = R1[9]
    if lead != 1:
        inv = pow(lead, p - 2, p)
        R1 = [(x * inv) % p for x in R1]
        R0 = [(x * inv) % p for x in R0]
    R0p = [(R0[i] if i < len(R0) else 0) % p for i in range(10)]
    gam = set()
    for Sidx in SUBS7:
        S = [D[i] for i in Sidx]
        mS = m_of(S)
        cols = []
        for gi in range(3):
            cols.append(polmod(polmul([0] * gi + [1], mS), R1))
        for pi in range(3):
            cols.append(polmod([0] * pi + [1], R1))
        rhs_poly = polmod(R0p, R1)
        M = [[cols[c][r] for c in range(6)] for r in range(9)]
        rhs = [rhs_poly[r] for r in range(9)]
        sol = solve_affine(M, rhs)
        if sol is None:
            continue
        base, kdim = sol
        if kdim != 0:
            continue
        tot9 = 0
        for gi in range(3):
            full = polmul([0] * gi + [1], mS)
            if len(full) > 9:
                tot9 = (tot9 + base[gi] * full[9]) % p
        tot9 = (tot9 - (R0p[9] if len(R0p) > 9 else 0)) % p
        if tot9:
            gam.add(tot9)
    return gam

def padd(a, b, s=1):
    m = max(len(a), len(b))
    return [((a[i] if i < len(a) else 0) + s * (b[i] if i < len(b) else 0)) % p
            for i in range(m)]

random.seed(163)
sizes = {}
for trial in range(20):
    overlap = random.choice([0, 1, 2, 3])
    pts = random.sample(range(n), 14 - overlap)
    S1 = sorted(pts[:7]); S2 = sorted(pts[7 - overlap:14 - overlap])
    g1 = [random.randrange(p) for _ in range(2)] + [random.randrange(1, p)]
    g2 = [random.randrange(p) for _ in range(2)] + [random.randrange(1, p)]
    P1 = [random.randrange(p) for _ in range(3)]
    P2 = [random.randrange(p) for _ in range(3)]
    ga1, ga2 = 1, 2
    v1 = polmul(g1, m_of([D[i] for i in S1]))
    v2 = polmul(g2, m_of([D[i] for i in S2]))
    num = padd(padd(v1, v2, s=-1), padd(P1, P2, s=-1))
    cinv = pow((ga1 - ga2) % p, p - 2, p)
    R1 = [(x * cinv) % p for x in num]
    if max((i for i in range(len(R1)) if R1[i] % p), default=-1) != 9:
        continue
    R0 = padd(padd(v1, P1), [(-ga1 * x) % p for x in R1])
    gam = fiber_gammas(R0, R1)
    sizes.setdefault(len(gam), 0)
    sizes[len(gam)] += 1
print(f"fiber sizes over 20 constructed pool stacks: {dict(sorted(sizes.items()))}")
print(f"(built-in pair = 2; >2 means pool extends)")
