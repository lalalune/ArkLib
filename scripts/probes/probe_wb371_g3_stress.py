#!/usr/bin/env python3
"""
G3 stress probe: two-sided witness count on STRUCTURED stacks, deep window
(11,10,1,4) and (31,10,1,4). Strata: sigma-invariant genuine, pole stacks
(l0 with roots in D -- the system stays a sound upper bound: derivation used
only pointwise WB relations), mixed. Compare two-sided vs faithful bad.
"""
import itertools, random

def make(qq):
    global q, n, k, w, D_def, D, need, inv, sigma, idx
    q, n, k, w = qq, 10, 1, 4
    D_def = 3 * w + k - 1 - n
    D = None
    # mu_10 in F_q (10 | q-1): q = 11: F11*; q = 31: order-10 subgroup
    def order_subgroup(q, n):
        for cand in range(2, q):
            seen = set(); x = 1
            for _ in range(q - 1):
                x = (x * cand) % q; seen.add(x)
            if len(seen) == q - 1:
                g = cand; break
        h = pow(g, (q - 1) // n, q)
        return sorted({pow(h, j, q) for j in range(n)})
    D = order_subgroup(q, n)
    need = n - w
    inv = {x: pow(x, q - 2, q) for x in range(1, q)}
    sigma = {x: (q - inv[x]) % q for x in D}
    idx = {x: i for i, x in enumerate(D)}

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return out

def poleval(p, x):
    return sum(c * pow(x, i, q) for i, c in enumerate(p)) % q

def m_of(T):
    out = [1]
    for x in T:
        out = polmul(out, [(-x) % q, 1])
    return out

def fast_bad_set(u0, u1):
    out = []
    for g in range(q):
        line = [(u0[i] + g * u1[i]) % q for i in range(n)]
        levels = {}
        for i, v in enumerate(line):
            levels.setdefault(v, []).append(i)
        for v, P in levels.items():
            if len(P) >= need:
                if not (all(u0[i] == u0[P[0]] for i in P) and
                        all(u1[i] == u1[P[0]] for i in P)):
                    out.append(g)
                    break
    return out

def solve_affine(M, rhs):
    rows = len(M); cols = len(M[0])
    Aug = [M[r][:] + [rhs[r]] for r in range(rows)]
    piv_cols = []
    r = 0
    for c in range(cols):
        piv = None
        for rr in range(r, rows):
            if Aug[rr][c] % q:
                piv = rr; break
        if piv is None:
            continue
        Aug[r], Aug[piv] = Aug[piv], Aug[r]
        ip = pow(Aug[r][c], q - 2, q)
        Aug[r] = [(x * ip) % q for x in Aug[r]]
        for rr in range(rows):
            if rr != r and Aug[rr][c] % q:
                f = Aug[rr][c]
                Aug[rr] = [(Aug[rr][i] - f * Aug[r][i]) % q for i in range(cols + 1)]
        piv_cols.append(c)
        r += 1
    for rr in range(r, rows):
        if Aug[rr][cols] % q:
            return None
    base = [0] * cols
    for i, c in enumerate(piv_cols):
        base[c] = Aug[i][cols]
    kernel = []
    free = [c for c in range(cols) if c not in piv_cols]
    for fc in free:
        kv = [0] * cols
        kv[fc] = 1
        for i, c in enumerate(piv_cols):
            kv[c] = (-Aug[i][fc]) % q
        kernel.append(kv)
    return base, kernel

def twosided_gammas(l0, R0, l1, R1):
    A = polmul(R0, l1); B = polmul(R1, l0); L = polmul(l0, l1)
    deg_top = 2 * w
    def pad(p):
        return [(p[i] if i < len(p) else 0) % q for i in range(deg_top + 1)]
    Ap, Bp, Lp = pad(A), pad(B), pad(L)
    gammas = set()
    for j in range(0, D_def + 1):
        size = w - j
        gbudget = D_def - j
        for T in itertools.combinations(D, size):
            S = sorted(set(D) - set(T))
            mS = pad(m_of(S))
            nunk = 2 + gbudget + 1
            M = []; rhs = []
            for d in range(deg_top + 1):
                row = [0] * nunk
                row[0] = Bp[d]
                row[1] = (-Lp[d]) % q
                for i in range(gbudget + 1):
                    if d - i >= 0 and d - i < len(mS):
                        row[2 + i] = (-mS[d - i]) % q
                M.append(row); rhs.append((-Ap[d]) % q)
            sols = solve_affine(M, rhs)
            if sols is None:
                continue
            base, kernel = sols
            if len(kernel) > 3:
                continue
            for coeffs in itertools.product(range(q), repeat=len(kernel)):
                v = base[:]
                for c, kv in zip(coeffs, kernel):
                    v = [(v[i] + c * kv[i]) % q for i in range(len(v))]
                if any(x % q for x in v[2:]):
                    gammas.add(v[0] % q)
    return gammas

def u_of(R, l, spike=None):
    u = []
    for x in D:
        lx = poleval(l, x)
        if lx == 0:
            u.append(spike.get(x, 0) if spike else 0)
        else:
            u.append((poleval(R, x) * pow(lx, q - 2, q)) % q)
    return tuple(u)

for qq in (11, 31):
    make(qq)
    print(f"\n=== q={q}, D=mu_10, D_def={D_def} ===")
    random.seed(47)
    genuine_l = []
    while len(genuine_l) < 50:
        l = [random.randrange(q) for _ in range(w)] + [1]
        if all(poleval(l, x) for x in D):
            genuine_l.append(l)

    # (a) sigma-invariant genuine stacks (search for invariance via row check)
    mx2 = mxb = 0; gaps = 0
    found = 0; tries = 0
    while found < 120 and tries < 60000:
        tries += 1
        l0 = random.choice(genuine_l); R0 = [random.randrange(q) for _ in range(w + k)]
        u0 = u_of(R0, l0)
        if any(u0[idx[x]] != u0[idx[sigma[x]]] for x in D):
            continue
        l1 = random.choice(genuine_l); R1 = [random.randrange(q) for _ in range(w + k)]
        u1 = u_of(R1, l1)
        if any(u1[idx[x]] != u1[idx[sigma[x]]] for x in D):
            continue
        found += 1
        G2s = twosided_gammas(l0, R0, l1, R1)
        bad = set(fast_bad_set(u0, u1))
        mx2 = max(mx2, len(G2s)); mxb = max(mxb, len(bad))
        if not bad.issubset(G2s):
            gaps += 1
    print(f"  (a) sigma-invariant genuine: found={found}, max twosided={mx2}, "
          f"max bad={mxb}, gaps={gaps}")

    # (b) pole stacks: l0 with roots = sigma orbit pair; check SOUNDNESS only
    mx2 = mxb = 0; gaps = 0; worst = None
    for trial in range(800):
        orbs = []
        seen = set()
        for x in D:
            if x in seen: continue
            o = [x]; seen.add(x); y = sigma[x]
            while y != x:
                o.append(y); seen.add(y); y = sigma[y]
            orbs.append(o)
        chosen = random.sample(orbs, 2)
        roots = [x for o in chosen for x in o][:w]
        l0 = [1]
        for r0 in roots:
            l0 = polmul(l0, [(-r0) % q, 1])
        while len(l0) - 1 < w:
            l0 = polmul(l0, [1, 1])  # pad with (X+1)... careful: -1 may be in D
        R0 = [0] * (w + k)  # pure spike: R0 = 0
        spike = {x: random.randrange(1, q) for x in roots}
        u0 = u_of(R0, l0, spike)
        l1 = random.choice(genuine_l); R1 = [random.randrange(q) for _ in range(w + k)]
        u1 = u_of(R1, l1)
        G2s = twosided_gammas(l0, R0, l1, R1)
        bad = set(fast_bad_set(u0, u1))
        mx2 = max(mx2, len(G2s)); mxb = max(mxb, len(bad))
        if not bad.issubset(G2s):
            gaps += 1
            if gaps <= 2:
                print(f"    POLE GAP (expected -- spike breaks WB relation?): "
                      f"bad={sorted(bad)} ts={sorted(G2s)}")
    print(f"  (b) pole(spike) x genuine: max twosided={mx2}, max bad={mxb}, gaps={gaps}")
