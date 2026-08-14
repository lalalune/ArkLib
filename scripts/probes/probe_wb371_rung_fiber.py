#!/usr/bin/env python3
"""
The mod-R1 fiber calculus at the d=2 level-1 rung (p=12289, n=16, k=3, |S|=7).

For polynomial-pair stacks (R0, R1) (deg <= 11), bad gamma satisfy the EXACT
identity   gamma*R1 = g*m_S + p - R0   with deg g <= 2, |S| = 7, deg p < 3
(degree forcing: deg LHS <= 9 caps deg g*m_S at 9).
Mod R1 (deg 9, assume R1 monic-normalized deg exactly 9):
   g*m_S + p == R0 (mod R1)   -- gamma-free fiber condition;
gamma is then the degree-9 coefficient of (g*m_S + p - R0)/R1 (exact division).

Probe:
 (1) pencil (R0, R1) = (X^8, X^9): enumerate the full graded fiber over all
     11440 S's; count distinct gammas; verify = the inversion orbit (16).
 (2) adversarial (R0, R1): random/structured pairs; max distinct-gamma count
     vs the budget 31.  Structures: R1 = X^9 with varied R0; R1 split products;
     orbit-aligned R0.
 (3) classify: fiber solutions per S (dimensions), chain/core structures.
"""
import itertools, random

p, n = 12289, 16
DEG_R1 = 9
GDEG, PDEG = 2, 2   # deg g <= 2, deg p <= 2

def mu_n():
    for g in range(2, 200):
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

def solve_affine(M, rhs, q):
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

SUBS7 = list(itertools.combinations(range(n), 7))

def fiber_gammas(R0, R1, cap_dim=2, verbose=False):
    """R1 monic deg 9. Enumerate graded fiber; return dict gamma -> #witnesses."""
    R0p = [(R0[i] if i < len(R0) else 0) % p for i in range(10)]
    gammas = {}
    big_dims = 0
    for Sidx in SUBS7:
        S = [D[i] for i in Sidx]
        mS = m_of(S)                       # deg 7, monic
        # unknowns: g0,g1,g2, p0,p1,p2 (6); condition: low 9 coeffs of
        # g*mS + p - R0 == multiple of R1 -> reduce mod R1 and set == 0...
        # cleaner: total = g*mS + p - R0 has deg <= 9; total == gamma*R1
        # <=> total mod R1 == 0 (then gamma = total[9]/R1[9] = total[9]).
        # Build: for each unknown, the residue of its basis poly mod R1.
        cols = []
        for gi in range(GDEG + 1):
            basis = polmod(polmul([0]*gi + [1], mS), R1)
            cols.append(basis)
        for pi in range(PDEG + 1):
            basis = polmod([0]*pi + [1], R1)
            cols.append(basis)
        rhs_poly = polmod(R0p, R1)
        M = [[cols[c][r] for c in range(6)] for r in range(DEG_R1)]
        rhs = [rhs_poly[r] for r in range(DEG_R1)]
        sol = solve_affine(M, rhs, p)
        if sol is None:
            continue
        base, kernel = sol
        dim = len(kernel)
        if dim > cap_dim:
            big_dims += 1
            continue
        for coeffs in itertools.product(range(p) if dim and p <= 50 else range(min(p, 1)), repeat=dim) \
                if dim == 0 or p > 50 else itertools.product(range(p), repeat=dim):
            # for p large only enumerate dim 0 (base) and dim>=1 via kernel sampling
            pass
        # large p: handle dim 0 exactly; dim>=1: the gamma varies affinely along
        # the kernel -> EVERY kernel direction with nonzero gamma-coefficient
        # gives all of F as gammas unless constrained by g != 0 etc.
        # compute gamma as a function: gamma(t) = gamma(base) + sum t_i * gamma(k_i)
        def gamma_of(v):
            # total = sum v_c * basisfull_c - R0 ; gamma = coeff 9
            tot9 = 0
            for gi in range(GDEG + 1):
                # coeff 9 of X^gi * mS
                full = polmul([0]*gi + [1], mS)
                if len(full) > 9:
                    tot9 = (tot9 + v[gi] * full[9]) % p
            # p-part contributes nothing at deg 9; R0 deg <= 9: subtract
            tot9 = (tot9 - (R0p[9] if len(R0p) > 9 else 0)) % p
            return tot9
        gv_base = gamma_of(base)
        gammas.setdefault(gv_base, 0)
        gammas[gv_base] += 1
        for kv in kernel:
            gk = 0
            for gi in range(GDEG + 1):
                full = polmul([0]*gi + [1], mS)
                if len(full) > 9:
                    gk = (gk + kv[gi] * full[9]) % p
            if gk % p:
                # gamma varies over ALL of F along this direction: flag
                gammas.setdefault("LINE", 0)
                gammas["LINE"] += 1
    return gammas, big_dims

# (1) the pencil
R0 = [0]*8 + [1]          # X^8
R1 = [0]*9 + [1]          # X^9
g_pencil, bd = fiber_gammas(R0, R1)
line_flags = g_pencil.pop("LINE", 0)
orbit = sorted((-pow(x, p - 2, p)) % p for x in D)
hit_orbit = sum(1 for g in g_pencil if g in orbit)
print(f"pencil fiber: {len(g_pencil)} distinct gammas "
      f"(orbit: {hit_orbit}/16), line-flags={line_flags}, big-dims={bd}")
nonzero = {g: c for g, c in g_pencil.items() if g != 0}
print(f"  nonzero gammas: {len(nonzero)}; sample counts: "
      f"{sorted(nonzero.values(), reverse=True)[:6]}")

# (2) adversarial
random.seed(131)
best = (len(nonzero), "pencil")
trials = [
    ("X^8+X^7, X^9", [0]*7 + [1, 1], [0]*9 + [1]),
    ("rand9, X^9", [random.randrange(p) for _ in range(9)] + [0], [0]*9 + [1]),
    ("X^8, X^9+X^8", [0]*8 + [1], [0]*8 + [1, 1]),
    ("X^8, split9", [0]*8 + [1], m_of([D[i] for i in range(9)])),
    ("orbitR0, X^9", None, [0]*9 + [1]),
]
for name, A, B in trials:
    if A is None:
        # R0 = product of (X - x) over half the orbit-ish points, deg 8
        A = m_of([D[i] for i in range(0, 16, 2)])
    gam, bd2 = fiber_gammas(A, B)
    lf = gam.pop("LINE", 0)
    nz = {g: c for g, c in gam.items() if g != 0}
    print(f"  {name}: distinct nonzero gammas = {len(nz)}, line-flags={lf}")
    if len(nz) > best[0]:
        best = (len(nz), name)
print(f"\nMAX distinct nonzero fiber-gammas: {best}  (budget: 31)")
