#!/usr/bin/env python3
"""
G3 probe v3 — the TWO-SIDED witness count vs faithful bad count, deep window.

For an actual doubly-rational stack (l0,R0,l1,R1) at (11,10,1,4) (D_def=2),
enumerate ALL graded candidates (T, g) and check the FULL exact identity
solvability:  exists p (deg<k=1, constant) and gamma in F with
    R0*l1 + gamma*R1*l0 - p*l0*l1 = g*m_S,   S = D \\ T.
For fixed T: the identity is linear in (gamma, p, g-coeffs): solve the linear
system over F_q; collect the set of gamma values over all T. Compare with the
faithful fast-bad count. The two-sided count is the object the G3 theorem
must bound -- conjecture: <= w+1 always (matches faithful caps).
Sample many stacks incl. sigma-invariant / pole-free genuine.
"""
import itertools, random

q, n, k, w = 11, 10, 1, 4
D_def = 3 * w + k - 1 - n   # 2
D = list(range(1, 11))
need = n - w

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

def twosided_gammas(l0, R0, l1, R1):
    """all gamma admitting a graded witness: solve, per T, the linear system
       A + gamma*B - p*L = g * m_S  in unknowns (gamma, p, g_0..g_dbudget),
       where A = R0*l1, B = R1*l0, L = l0*l1, m_S = m_D / m_T.
       Each polynomial coefficient (deg 0..2w) gives one linear equation."""
    A = polmul(R0, l1)
    B = polmul(R1, l0)
    L = polmul(l0, l1)
    gammas = set()
    deg_top = 2 * w  # identity lives in deg <= 2w (k=1)
    def pad(p):
        return [(p[i] if i < len(p) else 0) % q for i in range(deg_top + 1)]
    Ap, Bp, Lp = pad(A), pad(B), pad(L)
    for j in range(0, D_def + 1):
        size = w - j
        gbudget = D_def - j
        for T in itertools.combinations(D, size):
            S = sorted(set(D) - set(T))
            mS = pad(m_of(S))
            # unknowns: gamma, p, g_0..g_gbudget  (count = 2 + gbudget+1)
            # equations: for each degree d: Ap[d] + gamma*Bp[d] - p*Lp[d]
            #            - sum_i g_i * mS-shifted... wait g*m_S with g poly:
            # (g*m_S)[d] = sum_i g_i * mS[d-i]
            nunk = 2 + gbudget + 1
            M = []
            rhs = []
            for d in range(deg_top + 1):
                row = [0] * nunk
                row[0] = Bp[d]                      # gamma coefficient
                row[1] = (-Lp[d]) % q               # p coefficient
                for i in range(gbudget + 1):
                    if 0 <= d - i <= deg_top:
                        row[2 + i] = (-mS[d - i]) % q if d - i < len(mS) else 0
                M.append(row)
                rhs.append((-Ap[d]) % q)
            # NOTE the equation: Ap + gamma*Bp - p*Lp - (g*mS) = 0
            # -> gamma*Bp - p*Lp - sum g_i mS_{d-i} = -Ap
            # solve; enumerate solution space; require g != 0 (some g_i nonzero)
            sols = solve_affine(M, rhs)
            if sols is None:
                continue
            base, kernel = sols
            # enumerate small solution space (dim should be tiny)
            dim = len(kernel)
            if dim > 3:
                continue  # explosion guard; record?
            for coeffs in itertools.product(range(q), repeat=dim):
                v = base[:]
                for c, kv in zip(coeffs, kernel):
                    v = [(v[i] + c * kv[i]) % q for i in range(len(v))]
                gvec = v[2:]
                if any(x % q for x in gvec):
                    gammas.add(v[0] % q)
    return gammas

def solve_affine(M, rhs):
    """solve M x = rhs over F_q; return (particular, kernel_basis) or None."""
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

# ---- run over sampled stacks ----
random.seed(43)
genuine_l = []
while len(genuine_l) < 60:
    l = [random.randrange(q) for _ in range(w)] + [1]
    if all(poleval(l, x) for x in D):
        genuine_l.append(l)

print(f"deep window (11,10,1,4), D_def={D_def}")
mx2 = 0; mxb = 0; mismatches = 0
for trial in range(250):
    l0 = random.choice(genuine_l); l1 = random.choice(genuine_l)
    R0 = [random.randrange(q) for _ in range(w + k)]
    R1 = [random.randrange(q) for _ in range(w + k)]
    u0 = tuple((poleval(R0, x) * pow(poleval(l0, x), q - 2, q)) % q for x in D)
    u1 = tuple((poleval(R1, x) * pow(poleval(l1, x), q - 2, q)) % q for x in D)
    G2 = twosided_gammas(l0, R0, l1, R1)
    bad = set(fast_bad_set(u0, u1))
    mx2 = max(mx2, len(G2)); mxb = max(mxb, len(bad))
    if not bad.issubset(G2):
        mismatches += 1
        if mismatches <= 2:
            print(f"  COVERAGE GAP: bad={sorted(bad)} twosided={sorted(G2)}")
            print(f"    l0={l0} R0={R0} l1={l1} R1={R1}")
print(f"max two-sided gamma count = {mx2}   (conjecture <= w+1 = {w+1})")
print(f"max faithful bad count    = {mxb}")
print(f"coverage gaps (bad not in twosided): {mismatches}")
