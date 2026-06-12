#!/usr/bin/env python3
"""Explainer geometry of the below-UDR window adversary (#371, WB lane).

Pre-registered predictions (Fable round 4, before running):
  P1. The (13,6,1,2) extremal (u0=(6,8,8,6,7,7), u1=(10,9,9,10,4,4)) is a PURE TRIANGLE:
      3 bad scalars with pairwise-DISTINCT secant slopes Q_ab, and the pairwise joint
      agreement sets A_ab form a PERFECT PARTITION of the domain into 3 pairs
      (= the Mobius sigma-orbits). It is NOT an affine family (not collinear).
  P2. At (13,12,1,4): u1 = x^4 (mu_4-coset fibers), u0 = even combination, engineered from
      3 non-collinear points (gamma_i, P_i) realizes t = 3 bad scalars (the probe-observed
      scale-2 max) by the same triangle mechanism with A-sets = mu_4-cosets.
  P3. At (13,12,1,5) (deeper window, n-2w = 2): the ANTIPODAL construction u1 = x^2,
      u0 = even poly, can realize t = 4 > 3 bad scalars (triangle capacity
      C(t,2)*(n-2w) <= n allows t=4) -- i.e. the per-scale cap is NOT always w+1, and
      NOT always 3; it is governed by the triangle capacity / per-family max.
  P4. Per-family (collinear) configurations cap at 1 + w/(sigma+2) for genuinely rational
      stacks (J-cap |J| <= w+k-1).

Method: exact enumeration. Below UDR the line explainer is unique; badness(gamma) iff
|Agr(gamma)| >= n-w and no joint pair on the FULL agreement set Agr (monotonicity:
no-joint is upward monotone, any witness S lives inside Agr of the unique explainer).
"""
from itertools import combinations, product

def run_instance(q, n, k, w, gen, u0, u1, label, verbose=True):
    dom = [pow(gen, i, q) for i in range(n)]
    assert len(set(dom)) == n and all(x % q != 0 for x in dom)
    assert n >= 2*w + k + 1 - 1, "below-UDR-ish"
    tmin = n - w
    # Vandermonde rank helpers (deg < k interpolation on a subset)
    def interpolable(vals, idxs):
        # exists deg<k poly through (dom[i], vals[i]) for i in idxs: gaussian elim
        rows = [[pow(dom[i], j, q) for j in range(k)] + [vals[i] % q] for i in idxs]
        m, cols = len(rows), k + 1
        r = 0
        for c in range(k):
            piv = next((i for i in range(r, m) if rows[i][c] % q), None)
            if piv is None: continue
            rows[r], rows[piv] = rows[piv], rows[r]
            inv = pow(rows[r][c], q - 2, q)
            rows[r] = [(v * inv) % q for v in rows[r]]
            for i in range(m):
                if i != r and rows[i][c] % q:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
            r += 1
        return all(rows[i][k] % q == 0 for i in range(r, m))
    def explain_poly(vals, idxs):
        # unique deg<k poly through points (assumes consistent); returns coeff tuple
        rows = [[pow(dom[i], j, q) for j in range(k)] + [vals[i] % q] for i in idxs[:k]]
        # solve k x k
        for c in range(k):
            piv = next((i for i in range(c, k) if rows[i][c] % q), None)
            rows[c], rows[piv] = rows[piv], rows[c]
            inv = pow(rows[c][c], q - 2, q)
            rows[c] = [(v * inv) % q for v in rows[c]]
            for i in range(k):
                if i != c and rows[i][c] % q:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[c])]
        return tuple(rows[i][k] % q for i in range(k))
    def evalpoly(co, x):
        a = 0
        for c in reversed(co): a = (a * x + c) % q
        return a
    bads = []
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        # find a size-(n-w) subset S with line|_S in code; unique explainer below UDR
        expl = None
        for S in combinations(range(n), tmin):
            if interpolable(line, S):
                # candidate; extend to full agreement set of its explainer
                P = explain_poly(line, list(S))
                A = [i for i in range(n) if evalpoly(P, dom[i]) == line[i]]
                if len(A) >= tmin:
                    expl = (P, tuple(A)); break
        if expl is None: continue
        P, A = expl
        joint = interpolable(u0, A) and interpolable(u1, A)
        if not joint:
            bads.append((gam, P, A))
    t = len(bads)
    print(f"[{label}] (q,n,k,w)=({q},{n},{k},{w})  bad count t = {t}")
    if verbose and t:
        for gam, P, A in bads:
            print(f"   gamma={gam:3d}  P={P}  |Agr|={len(A)}  Agr={A}")
        # secant structure
        if t >= 2:
            print("   secants:")
            for (g1, P1, A1), (g2, P2, A2) in combinations(bads, 2):
                dg = (g1 - g2) % q
                Q = tuple((x - y) * pow(dg, q - 2, q) % q for x, y in zip(P1, P2))
                I = tuple(sorted(set(A1) & set(A2)))
                print(f"     ({g1},{g2}): Q={Q}  A_ab={I}  |A_ab|={len(I)}")
        if t >= 3:
            # collinearity check of (gamma, P) points: all secant slopes equal?
            slopes = set()
            for (g1, P1, _), (g2, P2, _) in combinations(bads, 2):
                dg = (g1 - g2) % q
                slopes.add(tuple((x - y) * pow(dg, q - 2, q) % q for x, y in zip(P1, P2)))
            kind = "IN-FAMILY (collinear)" if len(slopes) == 1 else \
                   f"OFF-FAMILY ({len(slopes)} distinct slopes)"
            print(f"   structure: {kind}")
    return t, bads

print("=" * 72)
print("P1: the (13,6,1,2) extremal -- structure")
q, n, k, w = 13, 6, 1, 2
run_instance(q, n, k, w, 4, (6, 8, 8, 6, 7, 7), (10, 9, 9, 10, 4, 4), "toy extremal")

print("=" * 72)
print("P2: scale 2 (13,12,1,4) -- engineered mu_4-coset triangle, u1 = a*x^4+b form")
q, n, k, w = 13, 12, 1, 4
g = 2  # F_13^* = <2>, mu_12 = all of it
dom = [pow(g, i, q) for i in range(n)]
# three non-collinear points (gamma_i, P_i): (1,0), (2,1), (4,0) -- check non-collinear
pts = [(1, 0), (2, 1), (4, 0)]
# pair data: Q_ab = (P_a-P_b)/(g_a-g_b), p*_ab = P_a - g_a Q_ab
pairs = {}
for (a, b) in combinations(range(3), 2):
    ga, Pa = pts[a]; gb, Pb = pts[b]
    Q = (Pa - Pb) * pow(ga - gb, q - 2, q) % q
    Pst = (Pa - ga * Q) % q
    pairs[(a, b)] = (Pst, Q)
print("pair (p*,Q):", pairs)
# A-sets: the three mu_4 cosets {x: x^4 = zeta} for zeta in mu_3
cosets = {}
for i, x in enumerate(dom):
    z = pow(x, 4, q)
    cosets.setdefault(z, []).append(i)
print("mu_4 cosets by x^4:", cosets)
zs = list(cosets)
u0 = [0] * n; u1 = [0] * n
for (ab, z) in zip([(0, 1), (0, 2), (1, 2)], zs):
    Pst, Q = pairs[ab]
    for i in cosets[z]:
        u0[i] = Pst; u1[i] = Q
print("engineered u0:", u0, " u1:", u1)
run_instance(q, n, k, w, g, tuple(u0), tuple(u1), "engineered scale-2 triangle")

print("=" * 72)
print("P3: (13,12,1,5) antipodal construction aiming t=4 (n-2w=2, capacity C(t,2)*2<=12)")
q, n, k, w = 13, 12, 1, 5
# 6 antipodal pairs {x,-x} = fibers of x^2; need 4 points (gamma_i,P_i) in general position
# (no 3 collinear), assign the 6 secant data to the 6 pairs; each Agr_i = union of its 3
# pairs (6 pts) + need >= n-w = 7 -> rely on accidental 7th agreements OR tune the spare
# value. Strategy: exhaustive over small sets of 4 points in general position (first found),
# then brute-force the assignment of pair-classes and run; also hill-climb if needed.
dom = [pow(2, i, q) for i in range(n)]
pairsq = {}
for i, x in enumerate(dom):
    z = pow(x, 2, q)
    pairsq.setdefault(z, []).append(i)
classes = list(pairsq.values())
assert len(classes) == 6
def attempt(pts4, perm):
    secs = list(combinations(range(4), 2))
    u0 = [0] * n; u1 = [0] * n
    for (ab, ci) in zip(secs, perm):
        ga, Pa = pts4[ab[0]]; gb, Pb = pts4[ab[1]]
        Q = (Pa - Pb) * pow(ga - gb, q - 2, q) % q
        Pst = (Pa - ga * Q) % q
        for i in classes[ci]:
            u0[i] = Pst; u1[i] = Q
    return tuple(u0), tuple(u1)
from itertools import permutations
best = (0, None)
pts_candidates = [
    [(1, 0), (2, 1), (3, 5), (4, 2)],
    [(1, 1), (2, 3), (5, 2), (7, 6)],
    [(0, 2), (1, 0), (3, 1), (9, 4)],
]
for pts4 in pts_candidates:
    # require no 3 collinear
    ok = True
    for tri in combinations(pts4, 3):
        (x1, y1), (x2, y2), (x3, y3) = tri
        if ((y2 - y1) * (x3 - x1) - (y3 - y1) * (x2 - x1)) % q == 0: ok = False
    if not ok: continue
    for perm in permutations(range(6)):
        u0, u1 = attempt(pts4, perm)
        t, _ = run_instance(q, n, k, w, 2, u0, u1, "antipodal t4 try", verbose=False)
        if t > best[0]:
            best = (t, (pts4, perm, u0, u1))
            if t >= 4: break
    if best[0] >= 4: break
print("P3 best t =", best[0])
if best[1]:
    pts4, perm, u0, u1 = best[1]
    print("  pts:", pts4, "perm:", perm)
    print("  u0:", u0, "\n  u1:", u1)
    run_instance(q, n, k, w, 2, u0, u1, "P3 best, detail")
