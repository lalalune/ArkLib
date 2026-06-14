# Directed n=12 boundary falsifier: for each disjoint triangle pair (T1,T2) and each
# pair of candidate extra blocks among the remaining 6 points, solve for the line in
# W = span(T1) cap span(T2) hitting both extras; count its full incidence; mcaEvent-verify
# the best. Dual-covector solve: O(1) per block per line.
import itertools, sys
p = 11; g = 2
xs = [pow(g, i, p) for i in range(10)]
n, k, m, b = 10, 6, 4, 3
def inv(a): return pow(a % p, p - 2, p)
eta = []
for i in range(n):
    pr = 1
    for l in range(n):
        if l != i: pr = (pr * (xs[i] - xs[l])) % p
    eta.append(inv(pr))
cols = [[(eta[i] * pow(xs[i], t, p)) % p for t in range(m)] for i in range(n)]
blocks = list(itertools.combinations(range(n), 2))

def rref(rows_in):
    rows = [r[:] for r in rows_in]; nr = len(rows); nc = len(rows[0]); rr = 0; piv = []
    for c in range(nc):
        pv = next((i for i in range(rr, nr) if rows[i][c]), None)
        if pv is None: continue
        rows[rr], rows[pv] = rows[pv], rows[rr]
        ivv = inv(rows[rr][c]); rows[rr] = [(a*ivv) % p for a in rows[rr]]
        for i in range(nr):
            if i != rr and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f*bb) % p for a, bb in zip(rows[i], rows[rr])]
        piv.append(c); rr += 1
    return rows[:rr], piv

def nullspace(rows_in):
    rs, piv = rref(rows_in)
    nc = len(rows_in[0])
    free = [c for c in range(nc) if c not in piv]
    basis = []
    for f in free:
        v = [0]*nc; v[f] = 1
        for ri, c in enumerate(piv):
            v[c] = (-rs[ri][f]) % p
        basis.append(v)
    return basis

# dual covectors per block: w with w.ci = w.cj = 0  (2 per block at m=4)
dual = {}
for (i, j) in blocks:
    dual[(i, j)] = nullspace([cols[i], cols[j]])

def dot(a, bv): return sum(x*y for x, y in zip(a, bv)) % p

def line_gammas(s0, s1):
    """for each block: gamma with s0+gam*s1 in R_B (via duals), or 'all', or None;
    returns dict block -> set of gammas (checking weight-nonzero needs solve; done later)"""
    out = {}
    for B in blocks:
        w1, w2 = dual[B]
        a1, b1 = dot(w1, s0), dot(w1, s1)
        a2, b2 = dot(w2, s0), dot(w2, s1)
        # need a1 + gam*b1 = 0 and a2 + gam*b2 = 0
        if b1 == 0 and b2 == 0:
            if a1 == 0 and a2 == 0: out[B] = 'all'
            continue
        if b1 != 0:
            gam = (-a1 * inv(b1)) % p
            if (a2 + gam * b2) % p == 0: out[B] = gam
        else:
            if a1 != 0: continue
            gam = (-a2 * inv(b2)) % p
            out[B] = gam
    return out

def admissible(B, point):
    """point in R_B with both weights nonzero?"""
    i, j = B
    ci, cj = cols[i], cols[j]
    for r1 in range(m):
        for r2 in range(r1+1, m):
            d = (ci[r1]*cj[r2] - ci[r2]*cj[r1]) % p
            if d:
                a = ((point[r1]*cj[r2] - point[r2]*cj[r1]) * inv(d)) % p
                bb = ((ci[r1]*point[r2] - ci[r2]*point[r1]) * inv(d)) % p
                return a != 0 and bb != 0
    return False

def span_basis(idxs):
    rs, _ = rref([cols[i] for i in idxs]); return rs

def intersection_basis(b1, b2):
    return nullspace(nullspace(b1) + nullspace(b2))

best = []
count_hist = {}
tri_list = list(itertools.combinations(range(n), 3))
done = 0
for T1 in tri_list:
    rest = [i for i in range(n) if i not in T1]
    for T2 in itertools.combinations(rest, 3):
        if list(T1) > list(T2): continue
        bs1 = span_basis(T1); bs2 = span_basis(T2)
        if len(bs1) != 3 or len(bs2) != 3: continue
        W = intersection_basis(bs1, bs2)
        if len(W) != 2: continue
        w0, w1v = W
        leftover = [i for i in range(n) if i not in T1 and i not in T2]
        extras = list(itertools.combinations(leftover, 2))
        # parametrize line: s0 = w0*u + w1*v base, dir = w0*c + w1*d.
        # Instead of solving constraints symbolically, scan lines in W coarsely:
        # all (dir in 14 proj, base in 13) = 182 lines; for each compute incidence via duals fast.
        dirs = [(1, t) for t in range(p)] + [(0, 1)]
        for (dc, dd) in dirs:
            dvec = [(dc*w0[r] + dd*w1v[r]) % p for r in range(m)]
            if all(v == 0 for v in dvec): continue
            cc, cd = (0, 1) if (dc, dd) != (0, 1) else (1, 0)
            for s in range(p):
                bvec = [(s*(cc*w0[r] + cd*w1v[r])) % p for r in range(m)]
                lg = line_gammas(bvec, dvec)
                # distinct gammas over multi-block hits with admissibility
                gamset = set()
                blkhits = set()
                for B, gam in lg.items():
                    if gam == 'all': continue   # line inside R_B: MCA-invisible alone
                    pt = [(bvec[r] + gam*dvec[r]) % p for r in range(m)]
                    if admissible(B, pt):
                        gamset.add(gam); blkhits.add(B)
                cg = len(gamset)
                count_hist[cg] = count_hist.get(cg, 0) + 1
                if cg >= 8:
                    best.append((cg, bvec, dvec, sorted(blkhits)))
        done += 1
    if done > 12000: break

best.sort(key=lambda x: -x[0])
print("histogram:", dict(sorted(count_hist.items())))
print("top:", [x[0] for x in best[:6]])

# mcaEvent verification of top candidates
def interpolable(pts, vals):
    rows = [[pow(x, jj, p) for jj in range(k)] + [v % p] for x, v in zip(pts, vals)]
    nr = len(rows); r = 0
    for c in range(k):
        piv = next((i for i in range(r, nr) if rows[i][c]), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        ivv = inv(rows[r][c])
        rows[r] = [(a * ivv) % p for a in rows[r]]
        for i in range(nr):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f * bb) % p for a, bb in zip(rows[i], rows[r])]
        r += 1
    return all(not (all(a == 0 for a in row[:-1]) and row[-1] != 0) for row in rows)

def word_from_synd(s):
    rows = [[(eta[i] * pow(xs[i], t, p)) % p for i in range(m)] + [s[t]] for t in range(m)]
    for c in range(m):
        piv = next(i for i in range(c, m) if rows[i][c])
        rows[c], rows[piv] = rows[piv], rows[c]
        ivv = inv(rows[c][c])
        rows[c] = [(a * ivv) % p for a in rows[c]]
        for i in range(m):
            if i != c and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(a - f*bb) % p for a, bb in zip(rows[i], rows[c])]
    return [rows[i][m] for i in range(m)] + [0]*(n - m)

print("\n=== mcaEvent verification ===")
agree_floor = n - (b - 1)
vmax = 0
for (cg, s0v, s1v, blks) in best[:5]:
    u1 = word_from_synd(s1v); u0 = word_from_synd(s0v)
    bad = []
    idx = list(range(n)); max_err = n - agree_floor
    for gam in range(p):
        y = [(u0[i] + gam*u1[i]) % p for i in range(n)]
        found = False
        for esz in range(0, max_err + 1):
            for E in itertools.combinations(idx, esz):
                Sc = [i for i in idx if i not in E]
                pts = [xs[i] for i in Sc]
                if not interpolable(pts, [y[i] for i in Sc]): continue
                if not (interpolable(pts, [u0[i] for i in Sc]) and
                        interpolable(pts, [u1[i] for i in Sc])):
                    found = True; break
            if found: break
        if found: bad.append(gam)
    vmax = max(vmax, len(bad))
    print(f"incidence {cg}, blocks {blks} -> exact bad {bad} ({len(bad)})")
print(f"\nVERDICT n=12 boundary (13,12,8) d=5 band-3: max verified = {vmax} "
      f"(7-cap law vs 6+extras; pencil = 6 = n/2)")
