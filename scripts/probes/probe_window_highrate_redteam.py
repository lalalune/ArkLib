#!/usr/bin/env python3
"""HIGH-RATE red team of WindowRationalBounded (#371, WB lane, Fable round 4).

The named Prop asserts: every doubly-WB-solvable stack has <= w+3 bad scalars at
slack-w radii.  All prior probes tested k in {1,2}.  The explainer-geometry analysis
says the two low-rate counting laws (Bonferroni slope capacity; the pure-triangle
quota t <= 2n/(n-w) < 4) acquire (k-1)-sized correction terms, so HIGH RATE is the
untested danger zone.  j = 0 instances (n = 3w+k-1, sigma = 0, w = 2):

    (17, 8, 3, 2)   mu_8 in F_17  (2-power, the production shape)
    (11, 10, 5, 2)  mu_10 = F_11^*
    (13, 12, 7, 2)  mu_12 = F_13^*
    (29, 14, 9, 2)  mu_14 in F_29
    (25=5^2 skipped: prime fields only here)

Pre-registered question: does any doubly-rational stack at these instances exceed
w+3 = 5 bad scalars?  (>= 4 would already beat every observed window count.)

Method per stack: exact badness via the unique-explainer reduction (below UDR):
gamma bad <=> exists S, |S| = n-w, line|_S in RS_k|_S; extend to full agreement set A
of the unique explainer; bad <=> |A| >= n-w and NOT (u0|_A and u1|_A both interpolable
by deg<k polys).  Search: (a) random genuine rational pairs; (b) engineered triangle
stacks from t target points (gamma_i, P_i) with greedy class assignment; (c) hill
climbing from the best find, mutating one coordinate of (l0,R0,l1,R1) at a time.
"""
import random
from itertools import combinations

random.seed(20260612)

def make_tools(q, n, k, dom):
    pw = [[pow(x, j, q) for j in range(k)] for x in dom]
    def solve(idxs, vals):
        # returns coeffs of deg<k poly through (dom[i], vals[i]) or None
        rows = [pw[i][:] + [vals[i] % q] for i in idxs]
        m = len(rows); r = 0; piv_cols = []
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
            piv_cols.append(c); r += 1
        if any(rows[i][k] % q for i in range(r, m)): return None
        co = [0] * k
        for ri, c in enumerate(piv_cols): co[c] = rows[ri][k]
        return co
    def evalpoly(co, x):
        a = 0
        for cf in reversed(co): a = (a * x + cf) % q
        return a
    return solve, evalpoly

def bad_set(q, n, k, w, dom, u0, u1, solve, evalpoly):
    tmin = n - w
    bads = []
    subs = list(combinations(range(n), tmin))
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        expl = None
        for S in subs:
            co = solve(list(S), line)
            if co is not None:
                A = [i for i in range(n) if evalpoly(co, dom[i]) == line[i]]
                if len(A) >= tmin: expl = (co, A); break
        if expl is None: continue
        co, A = expl
        if solve(A, u0) is None or solve(A, u1) is None:
            bads.append((gam, tuple(co), tuple(A)))
    return bads

def ratword(q, dom, l, r):
    out = []
    for x in dom:
        lv = 0
        for cf in reversed(l): lv = (lv * x + cf) % q
        if lv == 0: return None
        rv = 0
        for cf in reversed(r): rv = (rv * x + cf) % q
        out.append(rv * pow(lv, q - 2, q) % q)
    return tuple(out)

def genuine(q, l, r):
    ll = [c % q for c in l]
    while ll and ll[-1] == 0: ll.pop()
    if len(ll) <= 1: return True  # poly row: WB-solvable trivially; allowed in Prop
    inv = pow(ll[-1], q - 2, q); ll = [(c * inv) % q for c in ll]
    rr = [c % q for c in r]
    while len(rr) >= len(ll):
        f = rr[-1]
        for i in range(len(ll)):
            rr[len(rr) - len(ll) + i] = (rr[len(rr) - len(ll) + i] - f * ll[i]) % q
        rr.pop()
    return any(rr)

def find_gen(q, n):
    for g in range(2, q):
        if pow(g, n, q) == 1 and all(pow(g, n // p, q) != 1
                for p in {2, 3, 5, 7, 11, 13} if n % p == 0):
            xs = {pow(g, i, q) for i in range(n)}
            if len(xs) == n: return g
    return None

INSTANCES = [(17, 8, 3, 2), (11, 10, 5, 2), (13, 12, 7, 2), (29, 14, 9, 2)]

for (q, n, k, w) in INSTANCES:
    g = find_gen(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    solve, evalpoly = make_tools(q, n, k, dom)
    assert n == 3 * w + k - 1 and n >= 2 * w + k + 1
    best = (0, None)
    NS = 1500 if n <= 10 else 700
    # (a) random rational pairs
    for _ in range(NS):
        l0 = [random.randrange(q) for _ in range(w + 1)]
        l1 = [random.randrange(q) for _ in range(w + 1)]
        r0 = [random.randrange(q) for _ in range(w + k)]
        r1 = [random.randrange(q) for _ in range(w + k)]
        u0 = ratword(q, dom, l0, r0); u1 = ratword(q, dom, l1, r1)
        if u0 is None or u1 is None: continue
        b = bad_set(q, n, k, w, dom, u0, u1, solve, evalpoly)
        if len(b) > best[0]: best = (len(b), (u0, u1, b))
    print(f"({q},{n},{k},{w}) random: max bad = {best[0]}  (w+3 = {w+3})")
    # (b) engineered triangles: t target points, greedy domain-class assignment
    for t in (3, 4, 5):
        for trial in range(400):
            pts = []
            gs = random.sample(range(1, q), t)
            for gm in gs:
                pts.append((gm, [random.randrange(q) for _ in range(k)]))
            classes = list(combinations(range(t), 2))
            # random partition of D into C(t,2) classes, sizes as equal as possible
            idx = list(range(n)); random.shuffle(idx)
            asg = {}
            for ci, chunk_start in enumerate(range(0, n, max(1, n // len(classes)))):
                for i in idx[chunk_start:chunk_start + max(1, n // len(classes))]:
                    asg[i] = classes[min(ci, len(classes) - 1)]
            u0 = [0] * n; u1 = [0] * n
            ok = True
            for i in range(n):
                a, b = asg[i]
                ga, Pa = pts[a]; gb, Pb = pts[b]
                dg = (ga - gb) % q
                Qx = (evalpoly(Pa, dom[i]) - evalpoly(Pb, dom[i])) * pow(dg, q - 2, q) % q
                Px = (evalpoly(Pa, dom[i]) - ga * Qx) % q
                u0[i] = Px; u1[i] = Qx
            b = bad_set(q, n, k, w, dom, tuple(u0), tuple(u1), solve, evalpoly)
            if len(b) > best[0]:
                best = (len(b), (tuple(u0), tuple(u1), b))
    print(f"({q},{n},{k},{w}) +engineered: max bad = {best[0]}")
    # (c) hill climb from best (on raw word values -- explores beyond rational family,
    #     then verify WB-solvability of the survivors)
    if best[1]:
        u0, u1, _ = best[1]
        u0, u1 = list(u0), list(u1)
        cur = best[0]
        for step in range(2500):
            i = random.randrange(n); which = random.randrange(2)
            old0, old1 = u0[i], u1[i]
            if which == 0: u0[i] = random.randrange(q)
            else: u1[i] = random.randrange(q)
            b = bad_set(q, n, k, w, dom, tuple(u0), tuple(u1), solve, evalpoly)
            if len(b) >= cur: cur = len(b)
            else: u0[i], u1[i] = old0, old1
        # WB-solvability check of the climbed stack: exists (l,R), l != 0, deg l <= w,
        # deg R <= w+k-1 with l(x)u(x) = R(x) on D: linear system in coeffs
        def wbsolv(u):
            # unknowns: l (w+1), R (w+k); equations: n
            rows = []
            for i in range(n):
                x = dom[i]
                row = [(pow(x, j, q) * u[i]) % q for j in range(w + 1)]
                row += [(-pow(x, j, q)) % q for j in range(w + k)]
                rows.append(row + [0])
            # nontrivial kernel iff rank < 2w+k+1
            m = len(rows); cols = 2 * w + k + 1; r = 0
            for c in range(cols):
                piv = next((i2 for i2 in range(r, m) if rows[i2][c] % q), None)
                if piv is None: continue
                rows[r], rows[piv] = rows[piv], rows[r]
                inv = pow(rows[r][c], q - 2, q)
                rows[r] = [(v * inv) % q for v in rows[r]]
                for i2 in range(m):
                    if i2 != r and rows[i2][c] % q:
                        f = rows[i2][c]
                        rows[i2] = [(a2 - f * b2) % q for a2, b2 in zip(rows[i2], rows[r])]
                r += 1
            return r < cols
        b = bad_set(q, n, k, w, dom, tuple(u0), tuple(u1), solve, evalpoly)
        s0, s1 = wbsolv(u0), wbsolv(u1)
        print(f"({q},{n},{k},{w}) hill-climbed: bad = {len(b)}  "
              f"WBsolv(u0)={s0} WBsolv(u1)={s1}  {'<<< PROP-RELEVANT' if (s0 and s1) else '(outside Prop)'}")
        if len(b) > w + 3 and s0 and s1:
            print("  !!! WindowRationalBounded VIOLATION CANDIDATE !!!")
            print("  u0 =", tuple(u0)); print("  u1 =", tuple(u1))
            for gam, co, A in b: print(f"    gamma={gam} P={co} |A|={len(A)}")
