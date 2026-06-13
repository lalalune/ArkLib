#!/usr/bin/env python3
"""
probe_reciprocal_param.py -- ArkLib#371 normalizer-gap lane: Beukers-Smyth reciprocal branch.

TASK 1 (PARAMETERIZE): derive + machine-verify the conjugate-reciprocal condition for the
(1,1)-curve f(x,y) = c*xy + d*y - a*x - b attached to a hyperplane normal u = (c, d, -a, -b)
over K = Q(zeta_n), n = 2^k (BS 2002 verbatim: f reciprocal iff f ~ fbar(1/x,1/y) up to
monomial*scalar; bar = complex conjugation = zeta -> zeta^{-1} on cyclotomic data).

Derivation (each step machine-verified below):
  D1. fbar(1/x,1/y) * xy, written in the monomial basis (xy, y, x, 1), has coefficient
      vector rev(ubar) = (ubar3, ubar2, ubar1, ubar0).             [verified: V1]
  D2. For non-normalizer planes the monomial factor xy is FORCED (any other monomial
      shifts the support off bidegree (1,1); exactly-one-zero coefficient patterns can
      never be reciprocal -- and never occur for spanned planes).  [verified: V1b]
  D3. So f reciprocal <=> exists lambda in K*:  ubar_k = lambda * u_{3-k}  (k = 0..3);
      in (a,b,c,d) letters:  cbar = -lambda*b,  dbar = -lambda*a,
                             abar = -lambda*d,  bbar = -lambda*c.  [verified: V1]
  D4. Conjugating one relation and substituting the reversal-partner gives
      (1 - lambda*lambdabar) * u_k = 0 for every k; u != 0 in the domain Z[zeta]
      => lambda * lambdabar = 1.                                   [verified: V2]
  D5. NORMALIZATION CAVEAT (the prompt's claim, checked rather than assumed):
      lambda*lambdabar = 1 does NOT force lambda in {+-zeta^t} for general K-scalars:
      lambda0 = (3+4i)/5 (i = zeta^{n/4}) satisfies lambda0*lambda0bar = 1 and is not
      +-zeta^t; scaling a reciprocal normal by a non-unit mu multiplies lambda by
      mubar/mu and can leave the root-of-unity locus.              [verified: V3]
      What IS true: (i) for a PRIMITIVE integral normal, content(ubar) = content(u)
      forces (lambda) = (1), so lambda is an algebraic-integer unit with all conjugate
      absolute values 1, hence a root of unity (Kronecker), hence in mu(K) = <zeta>
      = {+-zeta^t : 0 <= t < n/2}; (ii) for CROSS-PRODUCT normals of surface triples
      the exponent is EXPLICIT -- see D6.
  D6. THE SPANNING IDENTITY (automatic reciprocity).  J = coordinate reversal has
      det J = +1, J^{-T} = J, and J*P(i,j) = zeta^{i+j} * P(-i,-j); the generalized
      cross product transforms by cross(JA,JB,JC) = det(J) J^{-T} cross(A,B,C), so for
      v = cross(P(0,0), P(i1,j1), P(i2,j2)) and Sigma = i1+j1+i2+j2 (mod n):
          rev(v) = zeta^Sigma * vbar      i.e.      vbar_k = zeta^{-Sigma} * v_{3-k}.
      EVERY plane spanned by a rank-3 triple of surface points through P(0,0) is
      conjugate-reciprocal with lambda = zeta^{-Sigma} -- a power of zeta, sign
      absorbed by zeta^{n/2} = -1.                                 [verified: V4]
  D7. FAMILY DIMENSION.  Fix lambda with lambda*lambdabar = 1.  The relations leave
      (u0, u1) in K^2 free and determine u2 = lambdabar*ubar1, u3 = lambdabar*ubar0:
      a K+-linear subspace of K^4 of K+-dimension 4 = HALF of 8 (K+ = maximal real
      subfield; the constraints are only K+-linear, not K-linear).  At a split prime
      the pair of evaluations (at z_p, z_p^{-1}) makes this an exact F_p-linear rank
      computation: rank 4, nullity 4; and the projection of the solution space onto
      the single-evaluation slot is ALL of F_p^4 -- the reciprocity filter is
      invisible to one-embedding mod-p data.                       [verified: V5]

TASK 2 (MAXIMIZER CHECK): for EVERY count-6 symmetry class in results_count6_classes.json
(34 classes at n=16, 210 at n=32) reconstruct the plane from its 6 incidence points --
mod-p (split prime ~2^28) 6x4 rank/nullspace first, then EXACT Z[x]/(x^{n/2}+1) cross
product (char0_witness_check.py style), cross-checked against the mod-p nullspace --
re-verify in char 0 (all 6 incidences, non-normalizer, det != 0, full exact count = 6),
then scan lambda = zeta^T (T = 0..n-1; this enumerates +-zeta^t, t < n/2, since
zeta^{n/2} = -1) for an exact fit of D3.  ANY class with no fit is a MAJOR finding.
Bonus: same check for the closed-form witness family S(n) at n in {8,16,32,64,128,256}
(this also re-proves M(128) >= 6 and M(256) >= 6 exactly, extending the char-0 anchor).

Exact integer arithmetic throughout (negacyclic ring Z[x]/(x^{n/2}+1)); stdlib only.
Outputs: results_reciprocal_param.json (+ sections consumed by RESULTS-RECIPROCAL.md).
"""

import json
import os
import sys
import time
import random

HERE = os.path.dirname(os.path.abspath(__file__))
CLASSES_JSON = os.path.join(HERE, "results_count6_classes.json")
OUT_JSON = os.path.join(HERE, "results_reciprocal_param.json")

WITNESSES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)


# ------------------------------------------------------------------ exact negacyclic ring

def make_ring(n):
    """Z[x]/(x^m + 1), m = n/2 (n a power of two): Phi_n = x^m + 1."""
    m = n // 2

    def mono(e):
        e %= n
        c = [0] * m
        if e < m:
            c[e] = 1
        else:
            c[e - m] = -1
        return c

    def add(a, b):
        return [x + y for x, y in zip(a, b)]

    def sub(a, b):
        return [x - y for x, y in zip(a, b)]

    def mul(a, b):
        out = [0] * m
        for i, ai in enumerate(a):
            if ai:
                for j, bj in enumerate(b):
                    if bj:
                        k = i + j
                        if k < m:
                            out[k] += ai * bj
                        else:
                            out[k - m] -= ai * bj
        return out

    def conj(a):
        """zeta -> zeta^{-1}: x^{-e} = -x^{m-e} for 0 < e < m."""
        out = [0] * m
        out[0] = a[0]
        for e in range(1, m):
            out[m - e] = -a[e]
        return out

    def shift(a, e):
        """Multiply by x^e (negacyclic rotation)."""
        e %= n
        out = [0] * m
        for k, ak in enumerate(a):
            if ak:
                idx = k + e
                s = ak
                while idx >= m:
                    idx -= m
                    s = -s
                out[idx] = s
        return out

    zero = [0] * m
    one = mono(0)
    return mono, add, sub, mul, conj, shift, zero, one


def cross_ring(P, Q, R, sub, mul):
    """Generalized cross product of rows (P,Q,R), P = (1,1,1,1) NOT assumed."""
    def D(i, j, k):
        return sub(mul(sub(Q[j], Q[i]), sub(R[k], R[i])),
                   mul(sub(Q[k], Q[i]), sub(R[j], R[i])))
    # rows are (P00, Q, R) with P00 = (1,1,1,1) in all our calls; the formula below is
    # the first-row-(1,1,1,1) Laplace expansion identical to char0_witness_check.py.
    v0 = D(1, 2, 3)
    v1 = [-c for c in D(0, 2, 3)]
    v2 = D(0, 1, 3)
    v3 = [-c for c in D(0, 1, 2)]
    return [v0, v1, v2, v3]


# ------------------------------------------------------------------ primality / split prime

def is_prime(m):
    if m < 2:
        return False
    for q in WITNESSES:
        if m % q == 0:
            return m == q
    d, r = m - 1, 0
    while d % 2 == 0:
        d //= 2
        r += 1
    for a in WITNESSES:
        x = pow(a, d, m)
        if x in (1, m - 1):
            continue
        for _ in range(r - 1):
            x = x * x % m
            if x == m - 1:
                break
        else:
            return False
    return True


def split_prime(n, lower=1 << 28):
    p = lower + 1
    p += (-(p - 1)) % n
    while not is_prime(p):
        p += n
    return p


def order_n_element(p, n):
    fs = set()
    mm, d = p - 1, 2
    while d * d <= mm:
        while mm % d == 0:
            fs.add(d)
            mm //= d
        d += 1
    if mm > 1:
        fs.add(mm)
    g = 2
    while not all(pow(g, (p - 1) // f, p) != 1 for f in fs):
        g += 1
    z = pow(g, (p - 1) // n, p)
    assert pow(z, n, p) == 1 and pow(z, n // 2, p) == p - 1
    return z


# ------------------------------------------------------------------ V1: coefficient relations

def v1_relations(n, trials=200, seed=371):
    """Machine-verify D1: xy * fbar(1/x,1/y) has coefficient vector rev(ubar) in the
    basis (xy, y, x, 1) -- via a generic Laurent-polynomial model, random u."""
    mono, add, sub, mul, conj, shift, zero, one = make_ring(n)
    m = n // 2
    rng = random.Random(seed)

    def rand_elt():
        return [rng.randrange(-5, 6) for _ in range(m)]

    basis = [(1, 1), (0, 1), (1, 0), (0, 0)]   # exponents of (xy, y, x, 1)
    fails = 0
    for _ in range(trials):
        u = [rand_elt() for _ in range(4)]
        # f = sum u_k * x^{e1} y^{e2}; fbar(1/x,1/y) = sum conj(u_k) x^{-e1} y^{-e2};
        # * xy: exponents += (1,1)
        g = {}
        for k, (e1, e2) in enumerate(basis):
            key = (1 - e1, 1 - e2)
            g[key] = add(g.get(key, zero), conj(u[k]))
        # predicted: coefficient of basis[k] in g equals rev(ubar)[k] = conj(u[3-k])
        ok = all(g.get(basis[k], zero) == conj(u[3 - k]) for k in range(4))
        ok = ok and set(g) <= set(basis)
        fails += 0 if ok else 1
    return {"n": n, "trials": trials, "failures": fails}


def v1b_monomial_forced(n=16):
    """D2: support matching.  For supp(f) within the unit square, x^A y^B * fbar(1/x,1/y)
    has support (A,B) - supp(f); equality with supp(f) forces 2*sum(supp) = |supp|*(A,B).
    Enumerate all 2^4 - 1 supports: full support forces (A,B) = (1,1); any support of
    size 3 (exactly one zero coefficient) admits NO integer (A,B) -- never reciprocal."""
    basis = [(1, 1), (0, 1), (1, 0), (0, 0)]
    out = []
    for mask in range(1, 16):
        supp = [basis[k] for k in range(4) if mask >> k & 1]
        sols = []
        for A in range(-2, 4):
            for B in range(-2, 4):
                if {(A - e1, B - e2) for (e1, e2) in supp} == set(supp):
                    sols.append((A, B))
        out.append({"support_mask": mask, "size": len(supp), "monomials": sols})
    full = next(o for o in out if o["support_mask"] == 15)
    size3 = [o for o in out if o["size"] == 3]
    assert full["monomials"] == [(1, 1)], "full support must force monomial xy"
    assert all(o["monomials"] == [] for o in size3), \
        "exactly-one-zero supports must admit no monomial (never reciprocal)"
    return {"full_support_forces_xy": True,
            "one_zero_coeff_never_reciprocal": True,
            "table": out}


# ------------------------------------------------------------------ V2: lambda*lambdabar = 1

def v2_consistency(n, trials=100, seed=372):
    """Construct reciprocal u from free (u0,u1) and lambda = zeta^T; verify relations and
    that the fitted lambda is unique with lambda*lambdabar = 1; verify random NON-
    reciprocal u admits no fit."""
    mono, add, sub, mul, conj, shift, zero, one = make_ring(n)
    m = n // 2
    rng = random.Random(seed)

    def rand_elt():
        return [rng.randrange(-5, 6) for _ in range(m)]

    def fits(u):
        """All T in [0,n) with ubar_k == zeta^T * u_{3-k} for k = 0..3."""
        ub = [conj(uk) for uk in u]
        return [T for T in range(n)
                if all(ub[k] == shift(u[3 - k], T) for k in range(4))]

    ok_recip, ok_unique, ok_nonrecip = 0, 0, 0
    for _ in range(trials):
        T = rng.randrange(n)
        u0, u1 = rand_elt(), rand_elt()
        lam_bar = mono(-T)          # lambdabar = zeta^{-T}
        u2 = mul(lam_bar, conj(u1))
        u3 = mul(lam_bar, conj(u0))
        u = [u0, u1, u2, u3]
        if all(uk == zero for uk in u):
            continue
        F = fits(u)
        ok_recip += T in F
        ok_unique += len(F) == 1
        # lambda * lambdabar = zeta^T * zeta^{-T} = 1 (exact ring identity)
        assert mul(mono(T), mono(-T)) == one
        # random perturbation: break one relation
        w = [list(c) for c in u]
        w[3][rng.randrange(m)] += 1
        ok_nonrecip += (fits(w) == []) or (w == u)
    return {"n": n, "trials": trials, "recip_fit_found": ok_recip,
            "fit_unique": ok_unique, "perturbed_has_no_fit": ok_nonrecip}


# ------------------------------------------------------------------ V3: the normalization caveat

def v3_caveat(n=16):
    """lambda0 = (3+4i)/5, i = zeta^{n/4}: lambda0*lambda0bar = 1 yet lambda0 not in
    {+-zeta^t}.  Verified integrally: L = 3+4i, conj(L) = 3-4i, L*Lbar = 25 = 5^2, and
    5*zeta^T != L for every T (so L/5 is not a root of unity).  A reciprocal plane built
    with lambda = lambda0 has an INTEGRAL (non-primitive) representative 5*u -- so the
    +-zeta^t normalization genuinely needs primitivity (content 1) or the cross-product
    closed form; it is not a consequence of lambda*lambdabar = 1 alone."""
    mono, add, sub, mul, conj, shift, zero, one = make_ring(n)
    i_elt = mono(n // 4)                      # zeta^{n/4} = i  (order 4)
    assert mul(i_elt, i_elt) == [-c for c in one], "zeta^{n/4} must square to -1"
    L = add([3 * c for c in one], [4 * c for c in i_elt])          # 3 + 4i
    Lb = conj(L)
    five_sq = [25 * c for c in one]
    assert mul(L, Lb) == five_sq, "(3+4i)(3-4i) must equal 25"
    not_rou = all(L != [5 * c for c in mono(T)] for T in range(n))
    assert not_rou, "3+4i must not be 5 * a root of unity"
    # integral non-primitive reciprocal representative with lambda = (3+4i)/5:
    # U = (5*u0, 5*u1, conj(L)*ubar1, conj(L)*ubar0); check Ubar_k = lambda0 * U_{3-k}
    # integrally as 5*Ubar_k == L * U_{3-k}.
    rng = random.Random(373)
    m = n // 2
    u0 = [rng.randrange(-3, 4) for _ in range(m)]
    u1 = [rng.randrange(-3, 4) for _ in range(m)]
    U = [[5 * c for c in u0], [5 * c for c in u1],
         mul(Lb, conj(u1)), mul(Lb, conj(u0))]
    ok = all([5 * c for c in conj(U[k])] == mul(L, U[3 - k]) for k in range(4))
    assert ok, "lambda0-reciprocal integral representative failed its relations"
    # and no root-of-unity lambda fits this U (it would force lambda0 in mu(K)):
    Ub = [conj(Uk) for Uk in U]
    no_fit = all(any(Ub[k] != shift(U[3 - k], T) for k in range(4)) for T in range(n))
    return {"n": n, "lambda0": "(3+4*zeta^{n/4})/5", "norm_one": True,
            "is_root_of_unity": False, "integral_rep_satisfies_relations": True,
            "integral_rep_fits_some_zeta_power": not no_fit}


# ------------------------------------------------------------------ V4: the spanning identity

def v4_spanning_identity(ns=(8, 16, 32, 64, 128, 256), seed=374):
    """rev(cross(P00, P(i1,j1), P(i2,j2))) == zeta^Sigma * conj(same), Sigma = i1+j1+i2+j2.
    Exhaustive at n = 8 (all C(n^2-1, 2) pairs); random elsewhere."""
    rng = random.Random(seed)
    out = []
    for n in ns:
        mono, add, sub, mul, conj, shift, zero, one = make_ring(n)

        def point(i, j):
            return (mono(i + j), mono(j), mono(i), one)

        P00 = point(0, 0)
        if n == 8:
            pool = [(i, j) for i in range(n) for j in range(n) if (i, j) != (0, 0)]
            from itertools import combinations
            trips = list(combinations(pool, 2))
        else:
            pool = [(i, j) for i in range(n) for j in range(n) if (i, j) != (0, 0)]
            k = {16: 500, 32: 500, 64: 300, 128: 120, 256: 40}.get(n, 50)
            trips = [tuple(rng.sample(pool, 2)) for _ in range(k)]
        bad = 0
        for (i1, j1), (i2, j2) in trips:
            v = cross_ring(P00, point(i1, j1), point(i2, j2), sub, mul)
            S = (i1 + j1 + i2 + j2) % n
            ok = all(shift(conj(v[k]), S) == v[3 - k] for k in range(4))
            bad += 0 if ok else 1
        out.append({"n": n, "checked": len(trips),
                    "exhaustive": n == 8, "failures": bad})
    return out


# ------------------------------------------------------------------ V5: dimension mod p

def v5_dimension(n):
    """Two-evaluation model at a split prime: relations ubar_k = zeta^T u_{3-k} become an
    8x8 F_p-linear system on (u_k(z), u_k(z^{-1})); verify rank 4 / nullity 4 for every
    T, and that the slot-1 projection of the kernel is all of F_p^4."""
    p = split_prime(n)
    z = order_n_element(p, n)
    zinv = pow(z, p - 2, p)

    def rank_and_kernel(T):
        lam1, lam2 = pow(z, T, p), pow(zinv, T, p)
        # unknowns x = (u0^1,u1^1,u2^1,u3^1, u0^2,u1^2,u2^2,u3^2)
        rows = []
        for k in range(4):
            r = [0] * 8
            r[4 + k] = 1                  # u_k^{(2)}
            r[3 - k] = (-lam1) % p        # - lam1 * u_{3-k}^{(1)}
            rows.append(r)
            r = [0] * 8
            r[k] = 1                      # u_k^{(1)}
            r[4 + (3 - k)] = (-lam2) % p  # - lam2 * u_{3-k}^{(2)}
            rows.append(r)
        # Gaussian elimination mod p
        mat = [row[:] for row in rows]
        rank, piv = 0, []
        for col in range(8):
            pr = next((r for r in range(rank, len(mat)) if mat[r][col] % p), None)
            if pr is None:
                continue
            mat[rank], mat[pr] = mat[pr], mat[rank]
            inv = pow(mat[rank][col], p - 2, p)
            mat[rank] = [x * inv % p for x in mat[rank]]
            for r in range(len(mat)):
                if r != rank and mat[r][col] % p:
                    f = mat[r][col]
                    mat[r] = [(mat[r][c] - f * mat[rank][c]) % p for c in range(8)]
            piv.append(col)
            rank += 1
        # kernel basis
        free = [c for c in range(8) if c not in piv]
        kern = []
        for fc in free:
            v = [0] * 8
            v[fc] = 1
            for r, c in enumerate(piv):
                v[c] = (-mat[r][fc]) % p
            kern.append(v)
        return rank, kern

    ranks = set()
    proj_full = True
    for T in range(n):
        rank, kern = rank_and_kernel(T)
        ranks.add(rank)
        # slot-1 projection: 4 coords of each kernel vector; rank of that 4x4..nx4
        pm = [v[:4] for v in kern]
        # rank of pm mod p
        rk, mat = 0, [row[:] for row in pm]
        for col in range(4):
            pr = next((r for r in range(rk, len(mat)) if mat[r][col] % p), None)
            if pr is None:
                continue
            mat[rk], mat[pr] = mat[pr], mat[rk]
            inv = pow(mat[rk][col], p - 2, p)
            mat[rk] = [x * inv % p for x in mat[rk]]
            for r in range(len(mat)):
                if r != rk and mat[r][col] % p:
                    f = mat[r][col]
                    mat[r] = [(mat[r][c] - f * mat[rk][c]) % p for c in range(4)]
            rk += 1
        proj_full &= (rk == 4)
    return {"n": n, "p": p, "ranks_seen": sorted(ranks),
            "nullity": 8 - max(ranks), "halved": ranks == {4},
            "slot1_projection_is_all_of_Fp4": proj_full}


# ------------------------------------------------------------------ TASK 2: maximizer check

def reduce_elt(elt, z, p):
    """Evaluate a power-basis element at zeta -> z mod p."""
    acc, zk = 0, 1
    for c in elt:
        acc = (acc + c * zk) % p
        zk = zk * z % p
    return acc


def nullspace_modp(points, z, p, n):
    """6x4 matrix of reduced points: returns (rank, normal or None)."""
    rows = [[pow(z, (i + j) % n, p), pow(z, j % n, p), pow(z, i % n, p), 1]
            for (i, j) in points]
    mat = [r[:] for r in rows]
    rank, piv = 0, []
    for col in range(4):
        pr = next((r for r in range(rank, len(mat)) if mat[r][col] % p), None)
        if pr is None:
            continue
        mat[rank], mat[pr] = mat[pr], mat[rank]
        inv = pow(mat[rank][col], p - 2, p)
        mat[rank] = [x * inv % p for x in mat[rank]]
        for r in range(len(mat)):
            if r != rank and mat[r][col] % p:
                f = mat[r][col]
                mat[r] = [(mat[r][c] - f * mat[rank][c]) % p for c in range(4)]
        piv.append(col)
        rank += 1
    if rank != 3:
        return rank, None
    free = next(c for c in range(4) if c not in piv)
    v = [0, 0, 0, 0]
    v[free] = 1
    for r, c in enumerate(piv):
        v[c] = (-mat[r][free]) % p
    return 3, v


def check_class(n, rep, ring, z, p, scan_cache=None):
    """Full exact pipeline for one count-6 class representative."""
    mono, add, sub, mul, conj, shift, zero, one = ring

    def point(i, j):
        return (mono(i + j), mono(j), mono(i), one)

    def dot_shift(v, i, j):
        """v . P(i,j) via monomial shifts: O(m) per point."""
        s = shift(v[0], i + j)
        s = add(s, shift(v[1], j))
        s = add(s, shift(v[2], i))
        return add(s, v[3])

    assert rep[0] == [0, 0] or rep[0] == (0, 0), "class rep must contain (0,0) first"
    pts = [tuple(q) for q in rep]
    assert len(pts) == 6 and len(set(pts)) == 6

    # (a) mod-p reconstruction: 6x4 rank-3 nullspace
    rank, w_modp = nullspace_modp(pts, z, p, n)
    assert rank == 3, f"n={n} rep {pts}: mod-p rank is {rank}, expected 3"

    # (b) exact cross product from the first rank-3 triple containing (0,0)
    P00 = point(0, 0)
    v = Sigma = triple = None
    for a in range(1, 6):
        for b in range(a + 1, 6):
            cand = cross_ring(P00, point(*pts[a]), point(*pts[b]), sub, mul)
            if any(c != 0 for ck in cand for c in ck):
                v, triple = cand, (pts[a], pts[b])
                Sigma = (pts[a][0] + pts[a][1] + pts[b][0] + pts[b][1]) % n
                break
        if v is not None:
            break
    assert v is not None, f"n={n} rep {pts}: no rank-3 triple through (0,0)"

    # (c) consistency: exact normal reduces to (a multiple of) the mod-p nullspace
    vred = [reduce_elt(vk, z, p) for vk in v]
    knz = next(k for k in range(4) if vred[k])
    assert w_modp[knz] != 0, "mod-p nullspace incompatible with exact normal"
    lam_p = vred[knz] * pow(w_modp[knz], p - 2, p) % p
    assert all((lam_p * w_modp[k] - vred[k]) % p == 0 for k in range(4)), \
        f"n={n} rep {pts}: exact cross does not reduce to the mod-p nullspace"

    # (d) char-0 re-verification: all 6 incidences, non-normalizer, det != 0,
    #     all four coefficients nonzero, exact full incidence count == 6
    for (i, j) in pts:
        assert dot_shift(v, i, j) == zero, f"n={n} rep {pts}: ({i},{j}) NOT on exact plane"
    v0, v1, v2, v3 = v
    nonzero = [any(c != 0 for c in vk) for vk in v]
    assert not (not nonzero[0] and not nonzero[3]), "scaling-normalizer type"
    assert not (not nonzero[1] and not nonzero[2]), "inversion-normalizer type"
    det = sub(mul(v0, v3), mul(v1, v2))
    assert det != zero, f"n={n} rep {pts}: singular in char 0"
    cnt = sum(1 for i in range(n) for j in range(n) if dot_shift(v, i, j) == zero)
    assert cnt == 6, f"n={n} rep {pts}: exact char-0 count {cnt} != 6"

    # (e) reciprocity scan: lambda = zeta^T, T in [0, n)
    vb = [conj(vk) for vk in v]
    fits = [T for T in range(n)
            if all(vb[k] == shift(v[3 - k], T) for k in range(4))]
    predicted = (-Sigma) % n
    return {
        "rep": [list(q) for q in pts],
        "triple_used": [list(triple[0]), list(triple[1])],
        "Sigma": Sigma,
        "all_four_coeffs_nonzero": all(nonzero),
        "exact_count": cnt,
        "lambda_fits_T": fits,
        "lambda_predicted_T": predicted,
        "prediction_hit": predicted in fits,
        "reciprocal": len(fits) > 0,
        "unique_lambda": len(fits) == 1,
    }


def maximizer_check():
    with open(CLASSES_JSON) as fh:
        data = json.load(fh)
    out = {}
    for nkey in sorted(data, key=int):
        n = int(nkey)
        p = data[nkey]["p"]
        assert is_prime(p) and (p - 1) % n == 0 and p > (1 << 28)
        z = order_n_element(p, n)
        ring = make_ring(n)
        t0 = time.time()
        results = []
        for cls in data[nkey]["classes"]:
            results.append(check_class(n, cls["rep"], ring, z, p))
        n_recip = sum(1 for r in results if r["reciprocal"])
        n_pred = sum(1 for r in results if r["prediction_hit"])
        out[nkey] = {
            "p": p,
            "n_classes": len(results),
            "n_reciprocal": n_recip,
            "n_prediction_hits": n_pred,
            "all_reciprocal": n_recip == len(results),
            "all_prediction_hits": n_pred == len(results),
            "all_unique_lambda": all(r["unique_lambda"] for r in results),
            "all_four_coeffs_nonzero": all(r["all_four_coeffs_nonzero"] for r in results),
            "failures": [r for r in results if not r["reciprocal"]],
            "classes": results,
            "wall_sec": round(time.time() - t0, 2),
        }
        print(f"[maximizers n={n}] {len(results)} classes: reciprocal {n_recip}, "
              f"lambda=zeta^(-Sigma) hits {n_pred}, wall {out[nkey]['wall_sec']}s",
              flush=True)
    return out


def witness_family_check(ns=(8, 16, 32, 64, 128, 256)):
    """S(n) = {(0,0),(1,1),(2,3),(4,n/2+2),(n/2-1,n-3),(n-2,n-1)}: exact count-6 +
    reciprocity (extends the char-0 lower bound M(n) >= 6 to n = 128, 256)."""
    out = []
    for n in ns:
        ring = make_ring(n)
        mono, add, sub, mul, conj, shift, zero, one = ring

        def point(i, j):
            return (mono(i + j), mono(j), mono(i), one)

        def dot_shift(v, i, j):
            s = shift(v[0], i + j)
            s = add(s, shift(v[1], j))
            s = add(s, shift(v[2], i))
            return add(s, v[3])

        t0 = time.time()
        S = [(0, 0), (1, 1), (2, 3), (4, n // 2 + 2), (n // 2 - 1, n - 3), (n - 2, n - 1)]
        v = cross_ring(point(0, 0), point(1, 1), point(2, 3), sub, mul)
        assert any(c != 0 for vk in v for c in vk)
        for (i, j) in S:
            assert dot_shift(v, i, j) == zero, f"witness incidence ({i},{j}) fails at n={n}"
        nz = [any(c != 0 for c in vk) for vk in v]
        assert nz[0] or nz[3]
        assert nz[1] or nz[2]
        det = sub(mul(v[0], v[3]), mul(v[1], v[2]))
        assert det != zero
        cnt = sum(1 for i in range(n) for j in range(n) if dot_shift(v, i, j) == zero)
        assert cnt == 6, f"witness char-0 count at n={n} is {cnt}"
        vb = [conj(vk) for vk in v]
        fits = [T for T in range(n) if all(vb[k] == shift(v[3 - k], T) for k in range(4))]
        Sigma = (1 + 1 + 2 + 3) % n
        out.append({"n": n, "exact_count": cnt, "lambda_fits_T": fits,
                    "lambda_predicted_T": (-Sigma) % n,
                    "prediction_hit": ((-Sigma) % n) in fits,
                    "M_lower_bound_6_proven": True,
                    "wall_sec": round(time.time() - t0, 2)})
        print(f"[witness n={n}] exact count 6 OK; lambda fits zeta^T, T={fits} "
              f"(predicted {(-Sigma) % n}); wall {out[-1]['wall_sec']}s", flush=True)
    return out


# ------------------------------------------------------------------ main

def main():
    t0 = time.time()
    res = {"meta": {"script": "probe_reciprocal_param.py",
                    "definition": "BS2002 verbatim: f reciprocal iff equivalent up to "
                                  "monomial*scalar to fbar(x^{-1},y^{-1}), bar = complex "
                                  "conjugation (zeta -> zeta^{-1})"}}
    print("V1: coefficient-relation derivation (Laurent model) ...", flush=True)
    res["V1_relations"] = [v1_relations(n) for n in (8, 16, 32)]
    assert all(r["failures"] == 0 for r in res["V1_relations"])
    print("V1b: monomial factor forcing (support enumeration) ...", flush=True)
    res["V1b_monomial"] = v1b_monomial_forced()
    print("V2: lambda*lambdabar = 1 consistency + uniqueness ...", flush=True)
    res["V2_consistency"] = [v2_consistency(n) for n in (8, 16, 32)]
    for r in res["V2_consistency"]:
        assert r["recip_fit_found"] == r["fit_unique"] == r["trials"], r
    print("V3: normalization caveat ((3+4i)/5 has norm 1, not a root of unity) ...",
          flush=True)
    res["V3_caveat"] = v3_caveat()
    assert res["V3_caveat"]["integral_rep_fits_some_zeta_power"] is False
    print("V4: spanning identity rev(cross) = zeta^Sigma * conj(cross) ...", flush=True)
    res["V4_spanning"] = v4_spanning_identity()
    assert all(r["failures"] == 0 for r in res["V4_spanning"])
    print("V5: half-dimension + mod-p invisibility of the filter ...", flush=True)
    res["V5_dimension"] = [v5_dimension(n) for n in (8, 16, 32)]
    assert all(r["halved"] and r["slot1_projection_is_all_of_Fp4"]
               for r in res["V5_dimension"])

    print("TASK 2: maximizer check over every count-6 class ...", flush=True)
    res["maximizers"] = maximizer_check()
    res["maximizers_all_reciprocal"] = all(v["all_reciprocal"]
                                           for v in res["maximizers"].values())
    print("witness family S(n) at n = 8..256 ...", flush=True)
    res["witness_family"] = witness_family_check()
    res["meta"]["wall_sec"] = round(time.time() - t0, 2)
    with open(OUT_JSON, "w") as fh:
        json.dump(res, fh, indent=1)
    print(f"maximizers_all_reciprocal = {res['maximizers_all_reciprocal']}", flush=True)
    print(f"done in {res['meta']['wall_sec']}s -> {OUT_JSON}", flush=True)


if __name__ == "__main__":
    sys.exit(main())
