#!/usr/bin/env python3
"""WB window pencil: the kernel-family law  #bad <= n*deg_gamma(Z)/w  (#371).

Discovery under test (from probe_wb_window_pencil_extremal_class.py): ALL window
extremals are DEGENERATE pencils with generic kernel dim 1.  For those, the kernel
is a polynomial family (Z(gamma), Q(gamma), h(gamma)) and

    gamma bad  <=>  Z(gamma, .) is D-split  (squarefree deg w, all roots in dom)

so the count obeys the bidegree-curve incidence bound  n * deg_gamma(Z) / w.
PREDICTION: at (13,6,1,2): 6*1/2 = 3 (= the observed extremal count, coincidentally
w+1); at (13,12,1,4): 12*e/4 = 3 at e=1 (NOT w+1=5) — matching the recorded
renormalization-probe max of 3.

This probe:
1. extracts the kernel family at extremal pairs (interpolating ker(M(gamma)) over
   all gamma), reports deg_gamma of each component, verifies bad == split set;
2. scans for generic kernel dim >= 2 pairs among genuine rational pairs;
3. adversarial search at (13,12,1,4) classifying max-bad pairs (law says 3, not 5).
"""
import random
from collections import Counter
from itertools import combinations, product
import os

exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))

random.seed(99)

def kernel_family(inst, M0, M1, dims):
    """For a generically-kerdim-1 pencil, interpolate the kernel line over gamma.
    Returns dict gamma -> normalized kernel vector, plus the interpolated
    polynomial family (list of gamma-coeff vectors) if consistent."""
    q = inst.q
    ncol = sum(dims)
    kers = {}
    for gam in range(q):
        M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)]
             for i in range(len(M0))]
        rk, ker = rank_and_kernel(M, q, want_kernel=True)
        kers[gam] = ker
    return kers

def normalize_family(inst, kers, dims):
    """Interpolate a polynomial vector family v(gamma) spanning ker at generic
    gamma: take gammas with kerdim 1, scale kernel vectors to a consistent
    projective normalization, interpolate each coordinate (deg <= #points-1),
    minimize gamma-degree over scalings by trying each coordinate as the 'monic'
    normalizer... simplest robust approach: treat v(gamma) up to scalar; compute
    the gamma-degree of the family via cross-ratios. Here: pick coordinate c* with
    kernel entry nonzero at most gammas; scale so that coordinate = 1; coordinates
    become rational functions in gamma; their common denominator is the gamma-poly
    of c*-entry; recover polynomial family by clearing. We just need deg_gamma(Z),
    so: compute for each pair of coords (i,j) the deg of the polynomial
    v_i(g)*mu_j - v_j(g)*mu_i ... overkill. Practical: interpolate the UNSCALED
    kernel using Cramer: kernel of M(gamma) with kerdim 1 = vector of (ncol-1)-minors
    with signs, polynomial in gamma of bounded degree. Implement via adjugate-like
    construction: choose ncol-1 rows R with generic rank ncol-1; kernel_j =
    (-1)^j det(M_R without column j). Interpolate det as poly from evaluations."""
    q = inst.q
    ncol = sum(dims)
    # find row subset of size ncol-1 with rank ncol-1 at some gamma
    import itertools
    best = None
    for gam in range(q):
        if len(kers[gam]) == 1:
            best = gam
            break
    if best is None:
        return None
    return best  # placeholder (full Cramer below in caller)

def family_split_law(inst, l0, r0, l1, r1, verbose=True):
    q, n, k, w = inst.q, inst.n, inst.k, inst.w
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims)
    nz = dims[0]
    kers = kernel_family(inst, M0, M1, dims)
    dimstats = Counter(len(v) for v in kers.values())
    # Cramer kernel: choose ncol-1 rows making rank ncol-1 at a generic gamma
    gen_g = next((g for g in range(q) if len(kers[g]) == 1), None)
    if gen_g is None:
        return None
    Mg = [[(M0[i][j] + gen_g * M1[i][j]) % q for j in range(ncol)]
          for i in range(len(M0))]
    rows = None
    import itertools
    # greedy row selection: eliminate to find ncol-1 independent rows
    idx = []
    R = []
    for i, row in enumerate(Mg):
        cand = R + [row]
        rk, _ = rank_and_kernel(cand, q)
        if rk == len(cand):
            R.append(row)
            idx.append(i)
        if len(R) == ncol - 1:
            break
    if len(R) < ncol - 1:
        return None
    # kernel_j(gamma) = (-1)^j * det(M(gamma)[idx, cols != j]); interpolate from
    # evaluations at gamma = 0..ncol (degree <= ncol-1 but Z-cols only -> <= nz)
    def kernel_vec_at(gam):
        M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)] for i in idx]
        out = []
        for j in range(ncol):
            sub = [[row[c] for c in range(ncol) if c != j] for row in M]
            # det mod q
            d = det_mod(sub, q)
            out.append((d if j % 2 == 0 else (-d) % q))
        return out
    pts = list(range(min(q, nz + 3)))
    evals = [kernel_vec_at(g) for g in pts]
    # interpolate each coordinate (Lagrange)
    def lagrange(pts, vals):
        m = len(pts)
        poly = [0] * m
        for i, (xi, yi) in enumerate(zip(pts, vals)):
            num = [1]
            den = 1
            for j, xj in enumerate(pts):
                if i == j:
                    continue
                num = pmul(num, [(-xj) % q, 1], q)
                den = den * ((xi - xj) % q) % q
            c = yi * pow(den, q - 2, q) % q
            t = psmul(c, num, q)
            for d_, cc in enumerate(t):
                poly[d_] = (poly[d_] + cc) % q
        return pnorm(poly)
    fam = [lagrange(pts, [evals[t][j] for t in range(len(pts))])
           for j in range(ncol)]
    # remove common gamma-content
    from functools import reduce
    nzfam = [f for f in fam if f]
    if not nzfam:
        return ("CRAMER_ZERO", dimstats)
    gco = reduce(lambda a, b: pgcd(a, b, q), nzfam)
    fam = [pdivmod(f, gco, q)[0] if f else [] for f in fam]
    degZ = max((len(fam[j]) - 1) for j in range(nz) if fam[j]) if any(fam[j] for j in range(nz)) else -1
    # verify: bad gammas == { g : Z(g,.) D-split }
    u0 = inst.ratword(l0, r0)
    u1 = inst.ratword(l1, r1)
    B = bad_set(inst, u0, u1)
    splitg = set()
    for gam in range(q):
        zc = [peval(fam[j], gam, q) for j in range(nz)]
        if is_dsplit(inst, zc):
            splitg.add(gam)
    law = inst.n * max(degZ, 0) // inst.w
    if verbose:
        print(f"  kerdims={dict(dimstats)} deg_gamma(Z-family)={degZ} "
              f"bad={sorted(B)} splitfam={sorted(splitg)} law=n*e/w={law}")
    return (degZ, sorted(B), sorted(splitg), law, dimstats)

def det_mod(M, q):
    M = [r[:] for r in M]
    nn = len(M)
    det = 1
    for c in range(nn):
        piv = next((i for i in range(c, nn) if M[i][c] % q), None)
        if piv is None:
            return 0
        if piv != c:
            M[c], M[piv] = M[piv], M[c]
            det = (-det) % q
        det = det * M[c][c] % q
        inv = pow(M[c][c], q - 2, q)
        for i in range(c + 1, nn):
            if M[i][c]:
                f = M[i][c] * inv % q
                for j in range(c, nn):
                    M[i][j] = (M[i][j] - f * M[c][j]) % q
    return det % q

# ---- part 1: extremal pairs at (13,6,1,2) ----
inst = Inst(13, 6, 1, 2, 4)
print("=== part 1: kernel family at known extremal pairs (13,6,1,2) ===")
extremal_pairs = [
    ([12, 10, 1], [9, 12, 4], [12, 9, 1], [6, 4, 7]),
    ([12, 10, 1], [9, 12, 4], [0, 1], [2, 4, 11]),
    ([12, 10, 1], [9, 12, 4], [12, 1, 1], [10, 8, 3]),
    ([6, 4, 7], [8, 5, 5], [4, 3, 9], [12, 2, 1]),
]
agree = 0
for p in extremal_pairs:
    r = family_split_law(inst, *p)
    if r and r[1] == r[2]:
        agree += 1
print(f"extremal family-law agreement: {agree}/{len(extremal_pairs)}")

# ---- part 2: scan for kerdim >= 2 among genuine pairs ----
print("\n=== part 2: generic kerdim >= 2 scan (13,6,1,2), 4000 samples ===")
found2 = 0
for _ in range(4000):
    l0 = [random.randrange(13) for _ in range(3)]
    r0 = [random.randrange(13) for _ in range(3)]
    l1 = [random.randrange(13) for _ in range(3)]
    r1 = [random.randrange(13) for _ in range(3)]
    if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
        continue
    if inst.ratword(l0, r0) is None or inst.ratword(l1, r1) is None:
        continue
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims)
    maxrank = 0
    for gam in range(13):
        M = [[(M0[i][j] + gam * M1[i][j]) % 13 for j in range(ncol)]
             for i in range(len(M0))]
        rk, _ = rank_and_kernel(M, 13)
        maxrank = max(maxrank, rk)
    if ncol - maxrank >= 2:
        found2 += 1
        u0, u1 = inst.ratword(l0, r0), inst.ratword(l1, r1)
        B = bad_set(inst, u0, u1)
        print(f"  kerdim>=2 pair: |BAD|={len(B)} ({l0},{r0},{l1},{r1})")
print(f"kerdim>=2 pairs found: {found2}")

# ---- part 3: scale 2 (13,12,1,4) — the law says max bad = n*e/w = 3, NOT w+1=5 ----
print("\n=== part 3: adversarial scale-2 (13,12,1,4): law predicts cap 3*e ===")
inst2 = Inst(13, 12, 1, 2, 2)   # careful: w=4 here, set below
class Inst2(Inst):
    pass
inst2 = Inst(13, 12, 1, 4, 2)
best = 0
bestrec = None
degen_max = Counter()
for trial in range(1200):
    l0 = [random.randrange(13) for _ in range(5)]
    r0 = [random.randrange(13) for _ in range(5)]
    l1 = [random.randrange(13) for _ in range(5)]
    r1 = [random.randrange(13) for _ in range(5)]
    if not (genuine_reduced(inst2, l0, r0) and genuine_reduced(inst2, l1, r1)):
        continue
    u0, u1 = inst2.ratword(l0, r0), inst2.ratword(l1, r1)
    if u0 is None or u1 is None:
        continue
    B = bad_set(inst2, u0, u1)
    if len(B) > best:
        best = len(B)
        bestrec = (l0, r0, l1, r1, sorted(B))
        M0, M1, dims = pencil_matrices(inst2, l0, r0, l1, r1)
        ncol = sum(dims)
        mr = 0
        for gam in range(13):
            M = [[(M0[i][j] + gam * M1[i][j]) % 13 for j in range(ncol)]
                 for i in range(len(M0))]
            rk, _ = rank_and_kernel(M, 13)
            mr = max(mr, rk)
        print(f"  new max |BAD|={best} class={'DEGEN' if mr < ncol else 'nondeg'} "
              f"kerdim={ncol - mr} bad={sorted(B)}", flush=True)
print(f"scale-2 max |BAD| over random genuine pairs = {best} "
      f"(law n*e/w with e=1: {12 // 4}; old w+1 reading: {4 + 1})")
