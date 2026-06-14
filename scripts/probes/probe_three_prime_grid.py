#!/usr/bin/env python3
"""Issue #232 — probe: the THREE-prime squarefree ZZ-GRID law (pre-formalization).

CLAIM (the Stage-2 brick): for distinct primes p, q, r, primitive roots
xi (p-th), eta (q-th), theta (r-th) in a char-0 field, and W : Z_p x Z_q x Z_r -> ZZ:

    sum_{i,j,k} W(i,j,k) xi^i eta^j theta^k = 0
      <=>  exists alpha : Z_q x Z_r -> ZZ, beta : Z_p x Z_r -> ZZ,
           gamma : Z_p x Z_q -> ZZ  with  W(i,j,k) = alpha(j,k) + beta(i,k) + gamma(i,j).

Exact verification strategy (STRONGER than any finite weight box — it settles the
claim for ALL of ZZ^(pqr) at each tested (p,q,r)):
  1. every generator of the alpha/beta/gamma lattice vanishes  (<= direction);
  2. QQ-dimensions match: rank(generators) = pqr - (p-1)(q-1)(r-1) = nullity(eval)
     (so QQ-span(gens) = QQ-kernel);
  3. the generator lattice is SATURATED: Smith normal form invariant factors all 1
     (so ZZ-kernel = ZZ-span(gens): no integrality gap — the => direction over ZZ);
  4. the Lean proof's route is checked separately: the per-slice MODULAR EQUATIONS
     are in the row span of the vanishing conditions, and the explicit
     alpha/beta/gamma construction reconstructs W on random integer kernel elements;
  5. the O105 witness S = {5,6,12,18,24,25} at n=30 in CRT grid coordinates:
     vanishes, decomposes over ZZ with NEGATIVE entries, and has NO NN-decomposition
     (exhaustive, via the per-entry min bounds A(j,k) <= min_i W(i,j,k) etc.).

Everything is exact integer/fraction arithmetic.  Exit 0 iff all checks pass.
"""

import itertools
import random
import sys
from fractions import Fraction

random.seed(232)
FAIL = []


def check(name, ok):
    print(("PASS" if ok else "FAIL"), name)
    if not ok:
        FAIL.append(name)


# ---------------------------------------------------------------- core machinery

def cell_index(i, j, k, p, q, r):
    return (i * q + j) * r + k


def reduce_tensor(W, p, q, r):
    """Reduce W (dict or list over cells) modulo Phi_p, Phi_q, Phi_r: result is the
    coefficient tensor on the QQ-basis xi^i eta^j theta^k (i<p-1, j<q-1, k<r-1),
    using x^{p-1} = -(1 + x + ... + x^{p-2}) per axis.  Vanishing <=> all zero."""
    T = [[[W[cell_index(i, j, k, p, q, r)] for k in range(r)]
          for j in range(q)] for i in range(p)]
    # axis i
    T = [[[T[i][j][k] - T[p - 1][j][k] for k in range(r)]
          for j in range(q)] for i in range(p - 1)]
    # axis j
    T = [[[T[i][j][k] - T[i][q - 1][k] for k in range(r)]
          for j in range(q - 1)] for i in range(p - 1)]
    # axis k
    T = [[[T[i][j][k] - T[i][j][r - 1] for k in range(r - 1)]
          for j in range(q - 1)] for i in range(p - 1)]
    return T


def vanishes(W, p, q, r):
    T = reduce_tensor(W, p, q, r)
    return all(x == 0 for a in T for b in a for x in b)


def generators(p, q, r):
    """The alpha/beta/gamma lattice generators as integer vectors of length pqr."""
    N = p * q * r
    gens = []
    for j0 in range(q):
        for k0 in range(r):
            v = [0] * N
            for i in range(p):
                v[cell_index(i, j0, k0, p, q, r)] = 1
            gens.append(v)
    for i0 in range(p):
        for k0 in range(r):
            v = [0] * N
            for j in range(q):
                v[cell_index(i0, j, k0, p, q, r)] = 1
            gens.append(v)
    for i0 in range(p):
        for j0 in range(q):
            v = [0] * N
            for k in range(r):
                v[cell_index(i0, j0, k, p, q, r)] = 1
            gens.append(v)
    return gens


def rank_QQ(rows):
    """Exact rank via fraction Gaussian elimination (row echelon)."""
    rows = [[Fraction(x) for x in row] for row in rows if any(row)]
    if not rows:
        return 0
    ncols = len(rows[0])
    rank = 0
    for col in range(ncols):
        piv = next((ri for ri in range(rank, len(rows)) if rows[ri][col] != 0), None)
        if piv is None:
            continue
        rows[rank], rows[piv] = rows[piv], rows[rank]
        prow = rows[rank]
        inv = 1 / prow[col]
        prow[:] = [x * inv for x in prow]
        for ri in range(len(rows)):
            if ri != rank and rows[ri][col] != 0:
                c = rows[ri][col]
                rows[ri] = [a - c * b for a, b in zip(rows[ri], prow)]
        rank += 1
        if rank == len(rows):
            break
    return rank


def smith_invariant_factors(M):
    """Smith normal form invariant factors of integer matrix M (list of rows)."""
    M = [row[:] for row in M]
    factors = []
    while M and M[0]:
        nr, nc = len(M), len(M[0])
        # find smallest nonzero pivot
        best = None
        for a in range(nr):
            for b in range(nc):
                if M[a][b] != 0 and (best is None or abs(M[a][b]) < abs(M[best[0]][best[1]])):
                    best = (a, b)
        if best is None:
            break
        a, b = best
        M[0], M[a] = M[a], M[0]
        for row in M:
            row[0], row[b] = row[b], row[0]
        # clear first row and column
        dirty = True
        while dirty:
            dirty = False
            piv = M[0][0]
            for a in range(1, len(M)):
                if M[a][0] != 0:
                    f = M[a][0] // piv
                    M[a] = [x - f * y for x, y in zip(M[a], M[0])]
                    if M[a][0] != 0:  # remainder smaller than pivot: swap up
                        M[0], M[a] = M[a], M[0]
                        dirty = True
            piv = M[0][0]
            for b in range(1, len(M[0])):
                if M[0][b] != 0:
                    f = M[0][b] // piv
                    for row in M:
                        row[b] -= f * row[0]
                    if M[0][b] != 0:
                        for row in M:
                            row[0], row[b] = row[b], row[0]
                        dirty = True
        piv = abs(M[0][0])
        # divisibility fix-up: fold rows whose entries are not divisible by piv
        bad = None
        for a in range(1, len(M)):
            if any(x % piv for x in M[a]):
                bad = a
                break
        if bad is not None:
            M[0] = [x + y for x, y in zip(M[0], M[bad])]
            continue
        factors.append(piv)
        M = [row[1:] for row in M[1:]]
        M = [row for row in M if any(row)] if M else M
    return factors


# ------------------------------------------------- per-(p,q,r) complete verification

def explicit_tables(W, p, q, r):
    """The Lean proof's explicit construction (no choice):
       alpha(j,k) = W(0,j,k); gamma(i,j) = W(i,j,0) - W(0,j,0);
       beta(i,k)  = W(i,0,k) - W(0,0,k) - W(i,0,0) + W(0,0,0)."""
    Wf = lambda i, j, k: W[cell_index(i, j, k, p, q, r)]
    alpha = {(j, k): Wf(0, j, k) for j in range(q) for k in range(r)}
    gamma = {(i, j): Wf(i, j, 0) - Wf(0, j, 0) for i in range(p) for j in range(q)}
    beta = {(i, k): Wf(i, 0, k) - Wf(0, 0, k) - Wf(i, 0, 0) + Wf(0, 0, 0)
            for i in range(p) for k in range(r)}
    return alpha, beta, gamma


def reconstructs(W, p, q, r):
    alpha, beta, gamma = explicit_tables(W, p, q, r)
    return all(W[cell_index(i, j, k, p, q, r)]
               == alpha[(j, k)] + beta[(i, k)] + gamma[(i, j)]
               for i in range(p) for j in range(q) for k in range(r))


def modular_rows(p, q, r):
    """The per-slice modular equations as functionals on W:
       for each i<p, j<q, k<r (D_i(j,k) := W(i,j,k) - W(0,j,k)):
       D_i(j,k) + D_i(0,0) - D_i(j,0) - D_i(0,k) = 0."""
    N = p * q * r
    rows = []
    for i in range(p):
        for j in range(q):
            for k in range(r):
                v = [0] * N
                for (ii, jj, kk, s) in [(i, j, k, 1), (0, j, k, -1),
                                        (i, 0, 0, 1), (0, 0, 0, -1),
                                        (i, j, 0, -1), (0, j, 0, 1),
                                        (i, 0, k, -1), (0, 0, k, 1)]:
                    v[cell_index(ii, jj, kk, p, q, r)] += s
                if any(v):
                    rows.append(v)
    return rows


def eval_rows(p, q, r):
    """The vanishing conditions as functionals: one row per reduced basis cell."""
    N = p * q * r
    rows = []
    for a in range(p - 1):
        for b in range(q - 1):
            for c in range(r - 1):
                v = [0] * N
                for i in (a, p - 1):
                    for j in (b, q - 1):
                        for k in (c, r - 1):
                            s = (1 if i == a else -1) * (1 if j == b else -1) \
                                * (1 if k == c else -1)
                            v[cell_index(i, j, k, p, q, r)] += s
                rows.append(v)
    return rows


def verify_triple(p, q, r):
    tag = f"({p},{q},{r})"
    N = p * q * r
    red_dim = (p - 1) * (q - 1) * (r - 1)
    gens = generators(p, q, r)

    # (1) every generator vanishes
    check(f"{tag} all {len(gens)} generators vanish",
          all(vanishes(g, p, q, r) for g in gens))

    # (2) QQ-dimension match
    ev = eval_rows(p, q, r)
    rk_ev = rank_QQ(ev)
    check(f"{tag} eval conditions independent (rank {rk_ev} = {red_dim})",
          rk_ev == red_dim)
    rk_g = rank_QQ(gens)
    check(f"{tag} rank(gens) {rk_g} = nullity {N - red_dim}", rk_g == N - red_dim)

    # (3) saturation: Smith invariant factors of the generator matrix all 1
    inv = smith_invariant_factors([row[:] for row in gens])
    check(f"{tag} generator lattice saturated (invariant factors {sorted(set(inv))})",
          len(inv) == rk_g and all(f == 1 for f in inv))

    # (4a) modular equations are consequences of vanishing (row-span containment)
    mod = modular_rows(p, q, r)
    rk_aug = rank_QQ(ev + mod)
    check(f"{tag} modular equations in span of vanishing conditions", rk_aug == rk_ev)

    # (4b) explicit construction reconstructs random integer kernel elements
    ok = True
    for _ in range(200):
        cs = [random.randint(-6, 6) for _ in gens]
        W = [sum(c * g[t] for c, g in zip(cs, gens)) for t in range(N)]
        if not vanishes(W, p, q, r) or not reconstructs(W, p, q, r):
            ok = False
            break
    check(f"{tag} explicit alpha/beta/gamma reconstructs 200 random kernel elements", ok)

    # (5) controls: non-kernel vectors do NOT vanish and do NOT reconstruct
    ok = True
    for t in range(N):
        e = [0] * N
        e[t] = 1
        if vanishes(e, p, q, r):
            ok = False
    check(f"{tag} unit bumps never vanish", ok)
    ok = True
    for _ in range(50):
        cs = [random.randint(-4, 4) for _ in gens]
        W = [sum(c * g[t] for c, g in zip(cs, gens)) for t in range(N)]
        W[random.randrange(N)] += random.choice([1, -1])
        if vanishes(W, p, q, r):
            ok = False
    check(f"{tag} perturbed kernel elements never vanish", ok)


for (p, q, r) in [(2, 3, 5), (2, 3, 7), (2, 3, 11), (3, 5, 7)]:
    verify_triple(p, q, r)

# ------------------------------------------------------------- the O105 witness

print("--- O105 witness S = {5,6,12,18,24,25} at n = 30, grid (p,q,r) = (2,3,5) ---")
p, q, r = 2, 3, 5
S = {5, 6, 12, 18, 24, 25}
W = [0] * 30
for e in range(30):
    if e in S:
        W[cell_index(e % 2, e % 3, e % 5, p, q, r)] = 1
check("witness CRT transport is a bijection (6 cells set)", sum(W) == 6)
check("witness vanishes on the grid", vanishes(W, p, q, r))
alpha, beta, gamma = explicit_tables(W, p, q, r)
check("witness explicit ZZ-decomposition reconstructs",
      reconstructs(W, p, q, r))
neg = [v for v in list(alpha.values()) + list(beta.values()) + list(gamma.values())
       if v < 0]
check("witness ZZ-decomposition has NEGATIVE entries (the O105 phenomenon)",
      len(neg) > 0)
print("    alpha (j,k):", {kk: v for kk, v in alpha.items() if v})
print("    beta  (i,k):", {kk: v for kk, v in beta.items() if v})
print("    gamma (i,j):", {kk: v for kk, v in gamma.items() if v})

# NN-impossibility, EXHAUSTIVE via per-entry min bounds:
#   A(j,k) <= min_i W, B(i,k) <= min_j W, C(i,j) <= min_k W  (all terms >= 0)
Wf = lambda i, j, k: W[cell_index(i, j, k, p, q, r)]
boundA = {(j, k): min(Wf(i, j, k) for i in range(p)) for j in range(q) for k in range(r)}
boundB = {(i, k): min(Wf(i, j, k) for j in range(q)) for i in range(p) for k in range(r)}
boundC = {(i, j): min(Wf(i, j, k) for k in range(r)) for i in range(p) for j in range(q)}
check("witness NN-bounds force A = B = C = 0 (exhaustive NN-impossibility)",
      all(v == 0 for v in boundA.values()) and all(v == 0 for v in boundB.values())
      and all(v == 0 for v in boundC.values()) and sum(W) > 0)

# the 4-cell omega argument used in Lean: cells (1,0,1), (0,0,1), (0,1,1), (0,0,0)
check("witness 4-cell contradiction instance values",
      (Wf(1, 0, 1), Wf(0, 0, 1), Wf(0, 1, 1), Wf(0, 0, 0)) == (0, 1, 0, 0))

# Stage-3 total identity: total = p*sum(alpha) + q*sum(beta) + r*sum(gamma)
total = sum(W)
sA, sB, sC = sum(alpha.values()), sum(beta.values()), sum(gamma.values())
check(f"witness total identity 6 = 2*{sA} + 3*{sB} + 5*{sC}",
      total == p * sA + q * sB + r * sC)

print()
if FAIL:
    print("FAILURES:", FAIL)
    sys.exit(1)
print("ALL CHECKS PASSED")
sys.exit(0)
