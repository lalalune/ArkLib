#!/usr/bin/env python3
"""Probe: the degenerate-discriminant pencil explosion for RS codes at d = 3b-3.

PRE-REGISTERED HYPOTHESIS (refutes the "MDS rank conjecture" / d >= 2b RS staircase):

For RS[F, D, k] with m := n - k = 3b - 4 (so d = 3b - 3), suppose the domain D
contains b+1 (or more) disjoint blocks of size b-1 whose locators lie in a single
pencil  < V0, T^{b-1} >  (concretely: equal-sum pairs for b = 3; cosets of mu_{b-1}
for smooth domains).  Then the perfect-square syzygy branch

    A = B + lam*T^{b-1},  p = r = rho*T^{b-2},  h = 2*rho*T^{b-2},
    P_gam = rho*(1+gam)^2*T^{b-2},  Q_gam = (1+gam)*B + lam*T^{b-1}

gives, for each block with locator V_a, a scalar gam_a and an error word e_a
supported on that block (all weights nonzero) such that the GRS-twisted syndromes
synd(e_a) are AFFINE in gam_a.  Reconstructing the stack (u0, u1) from the affine
family yields >= b+1 mcaEvent-bad scalars on band b (delta*n in [b-1, b)) --
contradicting LinearStaircaseUpper(RS, b) at d = 3b-3 >= 2b (b >= 3), and at b = 4
(d = 9 = 2b+1) contradicting the formal MDSStaircaseConjecture hypothesis k+2b <= n.

Verification is end-to-end and independent of the derivation: mcaEvent is checked
from the definition (all near-codewords of the line point via error-support
enumeration; maximal agreement sets; per-row interpolability for the joint clause).

Instances:
  T1: q=11, n=8,  k=3,  D={1..8},  b=3  (equal-sum pairs, s=9)  -- predict >= 4 bad
  T2: q=17, n=8,  k=3,  D=mu_8,    b=3  (antipodal pairs, s=0)  -- predict >= 4 bad
  T3: q=19, n=18, k=10, D=mu_18,   b=4  (mu_3-cosets)           -- predict >= 6 bad
      (T3 satisfies k + 2b = 18 <= n = 18: the formal MDSStaircaseConjecture instance.)
"""

import itertools, sys

def inv(a, p): return pow(a % p, p - 2, p)

# ---------- polynomial helpers over F_p (lists, index = degree) ----------
def pmul(f, g, p):
    r = [0] * (len(f) + len(g) - 1)
    for i, a in enumerate(f):
        if a:
            for j, b in enumerate(g):
                r[i + j] = (r[i + j] + a * b) % p
    return r

def padd(f, g, p):
    r = [0] * max(len(f), len(g))
    for i, a in enumerate(f): r[i] = (r[i] + a) % p
    for i, b in enumerate(g): r[i] = (r[i] + b) % p
    return r

def pscale(c, f, p): return [(c * a) % p for a in f]

def peval(f, x, p):
    r = 0
    for a in reversed(f): r = (r * x + a) % p
    return r

def trunc(f, m): return ([a for a in f] + [0] * m)[:m]

def series_inv(f, m, p):
    # inverse of power series f (f[0] != 0) mod T^m
    g = [inv(f[0], p)] + [0] * (m - 1)
    for i in range(1, m):
        s = 0
        for j in range(1, i + 1):
            if j < len(f): s = (s + f[j] * g[i - j]) % p
        g[i] = (-g[i - 1 + 1 - 1] * 0 - s * g[0]) % p  # g[i] = -f0^{-1} * s
        g[i] = (-s * g[0]) % p
    return g

# ---------- linear algebra: is vector y on points S interpolable by deg<k poly ----------
def interpolable(points, vals, k, p):
    """exists f, deg f < k, f(x)=v for (x,v) in zip(points, vals)?"""
    # Gaussian elimination on Vandermonde system
    rows = [[pow(x, j, p) for j in range(k)] + [v % p] for x, v in zip(points, vals)]
    n_r, n_c = len(rows), k
    r = 0
    for c in range(n_c):
        piv = next((i for i in range(r, n_r) if rows[i][c]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        iv = inv(rows[r][c], p)
        rows[r] = [(a * iv) % p for a in rows[r]]
        for i in range(n_r):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[r])]
        r += 1
    # consistent iff no row 0..0 | nonzero
    for row in rows:
        if all(a == 0 for a in row[:-1]) and row[-1] != 0:
            return False
    return True

def in_code(word, xs, k, p):
    return interpolable(xs, word, k, p)

# ---------- full independent mcaEvent check ----------
def bad_scalars(u0, u1, xs, k, p, agree_floor):
    """Exact bad-scalar set: for each gamma, mcaEvent holds iff some codeword w within
    distance n-agree_floor of the line has maximal agreement set S_w (|S_w|>=floor) on
    which the pair (u0,u1) is NOT jointly explainable (checked row-wise)."""
    n = len(xs)
    bad = []
    max_err = n - agree_floor
    idx = list(range(n))
    for gam in range(p):
        y = [(u0[i] + gam * u1[i]) % p for i in range(n)]
        found = False
        # enumerate candidate disagreement supports E, |E| <= max_err
        for esz in range(0, max_err + 1):
            for E in itertools.combinations(idx, esz):
                Sc = [i for i in idx if i not in E]
                pts = [xs[i] for i in Sc]; vals = [y[i] for i in Sc]
                if not interpolable(pts, vals, k, p):
                    continue
                # w exists agreeing on Sc (maximal agreement set >= Sc; using S = Sc is
                # enough: joint on bigger S implies joint on Sc, and we test not-joint on Sc;
                # but for exactness use Sc itself as the witness candidate)
                ok0 = interpolable(pts, [u0[i] for i in Sc], k, p)
                ok1 = interpolable(pts, [u1[i] for i in Sc], k, p)
                if not (ok0 and ok1):
                    found = True
                    break
            if found: break
        if found: bad.append(gam)
    return bad

# ---------- the pencil construction ----------
def construct(xs, k, p, blocks, B_poly, lam=1, rho=1, b=3):
    """blocks: list of tuples of indices into xs; each block's locator must be
    proportional to (1+gam_a)*B + lam*T^{b-1} for some gam_a.
    Returns (gammas, errors) or raises."""
    n = len(xs); m = n - k
    assert m == 3 * b - 4, (m, b)
    gammas, errors = [], []
    for blk in blocks:
        # block locator V(T) = prod (1 - x_i T)
        V = [1]
        for i in blk:
            V = pmul(V, [1, (-xs[i]) % p], p)
        # find gam: (1+gam)*B + lam*T^{b-1} = kappa * V
        # match: constant coeff: (1+gam)*B[0] = kappa*V[0]; B normalized B[0]=1, V[0]=1
        # so kappa = (1+gam). Coefficient at T^{b-1}: (1+gam)*B[b-1] + lam = (1+gam)*V[b-1]
        Bb = B_poly[b - 1] if len(B_poly) > b - 1 else 0
        Vb = V[b - 1] if len(V) > b - 1 else 0
        denom = (Vb - Bb) % p
        if denom == 0: raise ValueError("block locator collides with B")
        one_plus_gam = (lam * inv(denom, p)) % p
        if one_plus_gam == 0: raise ValueError("gam = -1 degenerate")
        gam = (one_plus_gam - 1) % p
        # check full proportionality: (1+gam)*B + lam*T^{b-1} == (1+gam)*V
        lhs = padd(pscale(one_plus_gam, B_poly, p), [0] * (b - 1) + [lam], p)
        rhs = pscale(one_plus_gam, V, p)
        lhs = trunc(lhs, max(len(lhs), len(rhs)) )
        rhs = trunc(rhs, len(lhs))
        if lhs != rhs: raise ValueError(f"block {blk} not in pencil: {lhs} vs {rhs}")
        # P_gam = rho*(1+gam)^2*T^{b-2}; Q = (1+gam)*V  (use Q=V, P scaled by 1/(1+gam))
        # twisted weights from partial fractions of P/Q with Q = V:
        # P/Q = [rho*(1+gam)^2/(1+gam)] * T^{b-2} / V = rho*(1+gam)*T^{b-2}/V
        Pc = (rho * one_plus_gam) % p  # P(T) = Pc * T^{b-2}, Q = V
        wts = {}
        for i in blk:
            tau = inv(xs[i], p)  # root of V
            Pval = (Pc * pow(tau, b - 2, p)) % p
            dV = 1
            for j in blk:
                if j != i:
                    dV = (dV * (1 - xs[j] * tau)) % p
            wts[i] = (Pval * inv(dV, p)) % p
            if wts[i] == 0: raise ValueError("zero twisted weight")
        gammas.append(gam); errors.append(wts)
    return gammas, errors

def run_instance(name, p, xs, k, b, blocks, B_poly):
    n = len(xs); m = n - k
    print(f"\n=== {name}: q={p} n={n} k={k} d={n-k+1} b={b} (need d=3b-3={3*b-3}) ===")
    assert n - k + 1 == 3 * b - 3
    # GRS twist multipliers
    eta = []
    for i in range(n):
        prod = 1
        for l in range(n):
            if l != i: prod = (prod * (xs[i] - xs[l])) % p
        eta.append(inv(prod, p))
    gammas, errors = construct(xs, k, p, blocks, B_poly, b=b)
    print("  gammas:", gammas)
    assert len(set(gammas)) == len(gammas), "gammas not distinct"
    # untwisted error words
    e_words = []
    for wts in errors:
        e = [0] * n
        for i, w in wts.items():
            e[i] = (w * inv(eta[i], p)) % p
        e_words.append(e)
    # twisted syndromes  s_j = sum eta_i e_i x_i^j , j < m
    def synd(word):
        return tuple(sum(eta[i] * word[i] * pow(xs[i], j, p) for i in range(n)) % p
                     for j in range(m))
    synds = [synd(e) for e in e_words]
    # affine check: (s_a - s_1)/(gam_a - gam_1) constant
    g1 = gammas[0]
    v_dir = None
    for a in range(1, len(gammas)):
        dg = (gammas[a] - g1) % p
        cand = tuple((synds[a][j] - synds[0][j]) * inv(dg, p) % p for j in range(m))
        if v_dir is None: v_dir = cand
        assert cand == v_dir, f"AFFINE CHECK FAILED at block {a}: {cand} vs {v_dir}"
    print("  affine syndrome family: VERIFIED  (direction", v_dir, ")")
    # reconstruct stack: u1 = any word with twisted syndrome v_dir; u0 = e_1 - gam_1*u1 mod code
    # solve for u1 supported on first m coordinates: sum_{i<m} eta_i u1_i x_i^j = v_dir_j
    import copy
    rows = [[(eta[i] * pow(xs[i], j, p)) % p for i in range(m)] + [v_dir[j]] for j in range(m)]
    # gaussian solve (square system, Vandermonde*diag => invertible)
    for c in range(m):
        piv = next(i for i in range(c, m) if rows[i][c])
        rows[c], rows[piv] = rows[piv], rows[c]
        ivv = inv(rows[c][c], p)
        rows[c] = [(a * ivv) % p for a in rows[c]]
        for i in range(m):
            if i != c and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * bb) % p for a, bb in zip(rows[i], rows[c])]
    u1 = [rows[i][m] for i in range(m)] + [0] * (n - m)
    u0 = [(e_words[0][i] - g1 * u1[i]) % p for i in range(n)]
    # verify each line point is e_a + codeword
    for a, gam in enumerate(gammas):
        diff = [(u0[i] + gam * u1[i] - e_words[a][i]) % p for i in range(n)]
        assert in_code(diff, xs, k, p), f"line point {a} not e_a + codeword"
    print("  line decomposition u0+gam*u1 = codeword + e_a: VERIFIED for all blocks")
    # full independent mcaEvent scan
    agree_floor = n - (b - 1)   # delta*n = b-1, witness floor (1-delta)n = n-(b-1)
    bad = bad_scalars(u0, u1, xs, k, p, agree_floor)
    print(f"  EXACT bad-scalar set at delta*n={b-1} (floor {agree_floor}): {bad}")
    print(f"  count = {len(bad)}  (staircase-collapse claim: <= {b};"
          f" predicted blocks give {len(gammas)})")
    missing = [g for g in gammas if g not in bad]
    if missing: print("  WARNING: predicted scalars NOT bad:", missing)
    verdict = "REFUTES d>=2b MDS collapse" if len(bad) > b else "consistent with collapse"
    print("  VERDICT:", verdict)
    return len(bad), bad, gammas, u0, u1, e_words

# ---------- T1: q=11, D={1..8}, equal-sum pairs s=9 ----------
p = 11; xs = [1,2,3,4,5,6,7,8]; k = 3; b = 3
# pairs summing to 9: (1,8),(2,7),(3,6),(4,5) -> indices
blocks = [(0,7),(1,6),(2,5),(3,4)]
# B = 1 - s*T + beta*T^2 with beta avoiding the pair products {8, 14=3, 18=7, 20=9}
beta = 1
B = [1, (-9) % p, beta]
r1 = run_instance("T1 equal-sum pairs", p, xs, k, b, blocks, B)

# ---------- T2: q=17, D=mu_8, antipodal pairs ----------
p = 17
# mu_8 in F_17: 2 is a generator of order 8? 2^8=256=1 mod 17, ord(2)=8. yes
g = 2; xs = [pow(g, i, p) for i in range(8)]; k = 3; b = 3
# antipodal pairs {x,-x}: x and x*g^4 (g^4 = 16 = -1)
blocks = []
used = set()
for i in range(8):
    j = (i + 4) % 8
    if i not in used and j not in used:
        blocks.append((i, j)); used.update((i, j))
# B = 1 + 0*T + beta*T^2, beta avoiding pair products -x^2 (x in mu_8 -> -mu_4)
mu4 = {pow(g, 2*i, p) for i in range(4)}
forb = {(-x) % p for x in mu4}
beta = next(c for c in range(1, p) if c not in forb)
B = [1, 0, beta]
r2 = run_instance("T2 antipodal pairs (smooth)", p, xs, k, b, blocks, B)

# ---------- T3: q=19, D=mu_18, mu_3-cosets, b=4 ----------
p = 19
# F_19*: generator 2 (ord 18). mu_18 = all of F_19*
g = 2
assert sorted(pow(g, i, p) for i in range(18)) == list(range(1, 19))
xs = [pow(g, i, p) for i in range(18)]; k = 10; b = 4
# mu_3 = {g^6, g^12, 1} = cube roots of 1; cosets: x*mu_3
mu3 = [pow(g, 6*i, p) for i in range(3)]
blocks = []
used = set()
for i in range(18):
    if xs[i] in used: continue
    cos = [(xs[i] * h) % p for h in mu3]
    idxs = tuple(xs.index(c) for c in cos)
    blocks.append(idxs); used.update(cos)
assert len(blocks) == 6
# coset locator: 1 - (x^3)T^3 -> pencil <1, T^3>; B = 1 + beta*T^3, beta avoiding -x^3 set
cubes = {pow(x, 3, p) for x in range(1, p)}
forb = {(-c) % p for c in cubes}
beta = next(c for c in range(1, p) if c not in forb)
B = [1, 0, 0, beta]
r3 = run_instance("T3 mu_3-cosets b=4 (formal MDSStaircaseConjecture instance)",
                  p, xs, k, b, blocks, B)

print("\n=== SUMMARY ===")
for nm, r in [("T1", r1), ("T2", r2), ("T3", r3)]:
    print(f"{nm}: bad count {r[0]}, set {r[1]}")

# ================= EXTENSION: general f (strip depth) =================
# m = n-k = 2(b-1) + f for f in [0, b-2]; P_gam = rho*(1+gam)^2*T^f.
# Same pencil, same blocks; mismatch term gam*rho*lam^2*T^{f+2(b-1)} = 0 mod T^m.

def construct_f(xs, k, p, blocks, B_poly, b, f, lam=1, rho=1):
    n = len(xs); m = n - k
    assert m == 2 * (b - 1) + f, (m, b, f)
    gammas, errors = [], []
    for blk in blocks:
        V = [1]
        for i in blk:
            V = pmul(V, [1, (-xs[i]) % p], p)
        Bb = B_poly[b - 1] if len(B_poly) > b - 1 else 0
        Vb = V[b - 1] if len(V) > b - 1 else 0
        denom = (Vb - Bb) % p
        if denom == 0: raise ValueError("collide")
        one_plus_gam = (lam * inv(denom, p)) % p
        if one_plus_gam == 0: raise ValueError("gam=-1")
        gam = (one_plus_gam - 1) % p
        lhs = padd(pscale(one_plus_gam, B_poly, p), [0] * (b - 1) + [lam], p)
        rhs = pscale(one_plus_gam, V, p)
        L = max(len(lhs), len(rhs)); assert trunc(lhs, L) == trunc(rhs, L)
        Pc = (rho * one_plus_gam) % p   # P = Pc * T^f, Q = V
        wts = {}
        for i in blk:
            tau = inv(xs[i], p)
            Pval = (Pc * pow(tau, f, p)) % p
            dV = 1
            for j in blk:
                if j != i: dV = (dV * (1 - xs[j] * tau)) % p
            wts[i] = (Pval * inv(dV, p)) % p
            assert wts[i] != 0
        gammas.append(gam); errors.append(wts)
    return gammas, errors

def run_f(name, p, xs, k, b, f, blocks, B_poly):
    n = len(xs); m = n - k
    print(f"\n=== {name}: q={p} n={n} k={k} d={n-k+1} b={b} f={f} ===")
    eta = []
    for i in range(n):
        prod = 1
        for l in range(n):
            if l != i: prod = (prod * (xs[i] - xs[l])) % p
        eta.append(inv(prod, p))
    gammas, errors = construct_f(xs, k, p, blocks, B_poly, b, f)
    print("  gammas:", sorted(gammas))
    assert len(set(gammas)) == len(gammas)
    e_words = []
    for wts in errors:
        e = [0] * n
        for i, w in wts.items(): e[i] = (w * inv(eta[i], p)) % p
        e_words.append(e)
    def synd(word):
        return tuple(sum(eta[i] * word[i] * pow(xs[i], j, p) for i in range(n)) % p
                     for j in range(m))
    synds = [synd(e) for e in e_words]
    g1 = gammas[0]; v_dir = None; ok = True
    for a in range(1, len(gammas)):
        dg = (gammas[a] - g1) % p
        cand = tuple((synds[a][j] - synds[0][j]) * inv(dg, p) % p for j in range(m))
        if v_dir is None: v_dir = cand
        elif cand != v_dir: ok = False
    print("  affine:", "VERIFIED" if ok else "FAILED")
    if not ok: return None
    rows = [[(eta[i] * pow(xs[i], j, p)) % p for i in range(m)] + [v_dir[j]] for j in range(m)]
    for c in range(m):
        piv = next(i for i in range(c, m) if rows[i][c])
        rows[c], rows[piv] = rows[piv], rows[c]
        ivv = inv(rows[c][c], p)
        rows[c] = [(a * ivv) % p for a in rows[c]]
        for i in range(m):
            if i != c and rows[i][c]:
                fc = rows[i][c]
                rows[i] = [(a - fc * bb) % p for a, bb in zip(rows[i], rows[c])]
    u1 = [rows[i][m] for i in range(m)] + [0] * (n - m)
    u0 = [(e_words[0][i] - g1 * u1[i]) % p for i in range(n)]
    for a, gam in enumerate(gammas):
        diff = [(u0[i] + gam * u1[i] - e_words[a][i]) % p for i in range(n)]
        assert in_code(diff, xs, k, p)
    bad = bad_scalars(u0, u1, xs, k, p, n - (b - 1))
    print(f"  EXACT bad set at delta*n={b-1}: {bad}  count={len(bad)} (collapse claim <= {b})")
    return bad

# T4: b=4, d=8=2b (f=1): mu_18 in F_19, k=11
p = 19; g = 2; xs = [pow(g, i, p) for i in range(18)]; k = 11; b = 4; f = 1
mu3 = [pow(g, 6*i, p) for i in range(3)]
blocks = []; used = set()
for i in range(18):
    if xs[i] in used: continue
    cos = [(xs[i] * h) % p for h in mu3]
    blocks.append(tuple(xs.index(c) for c in cos)); used.update(cos)
cubes = {pow(x, 3, p) for x in range(1, p)}
beta = next(c for c in range(1, p) if c not in {(-cc) % p for cc in cubes})
run_f("T4 b=4 d=8=2b", p, xs, k, b, f, blocks, [1, 0, 0, beta])

# T5: b=4, d=7=2b-1 (f=0): k=12
run_f("T5 b=4 d=7=2b-1", p, xs, 12, b, 0, blocks, [1, 0, 0, beta])

# T6: (17,8,4) band 3, d=5=2b-1 (f=0): settles the running band-3 sweep question
p = 17; g = 2; xs = [pow(g, i, p) for i in range(8)]; k = 4; b = 3; f = 0
blocks = []; used = set()
for i in range(8):
    j = (i + 4) % 8
    if i not in used and j not in used:
        blocks.append((i, j)); used.update((i, j))
mu4 = {pow(g, 2*i, p) for i in range(4)}
beta = next(c for c in range(1, p) if c not in {(-x) % p for x in mu4})
run_f("T6 (17,8,4) band3 d=5", p, xs, k, b, f, blocks, [1, 0, beta])
