# Stratum scan with end-to-end mcaEvent verification of every candidate >= 7.
import itertools
p = 17; g = 2
xs = [pow(g, i, p) for i in range(8)]
n, k, m, b = 8, 4, 4, 3
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

def span_basis(idxs):
    rs, _ = rref([cols[i] for i in idxs]); return rs

def intersection(b1, b2):
    W1 = nullspace(b1); W2 = nullspace(b2)
    return nullspace(W1 + W2)

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

def exact_bad_count(s0v, s1v):
    u1 = word_from_synd(s1v); u0 = word_from_synd(s0v)
    agree_floor = n - (b - 1)
    bad = 0
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
        if found: bad += 1
    return bad

def incidence_count(s0, s1):
    gams = set(); blkset = set()
    for (i, j) in blocks:
        ci, cj = cols[i], cols[j]
        for gam in range(p):
            t = [(s0[r] + gam*s1[r]) % p for r in range(m)]
            sol = None
            for r1 in range(m):
                done = False
                for r2 in range(r1+1, m):
                    d = (ci[r1]*cj[r2] - ci[r2]*cj[r1]) % p
                    if d:
                        a = ((t[r1]*cj[r2] - t[r2]*cj[r1]) * inv(d)) % p
                        bb = ((ci[r1]*t[r2] - ci[r2]*t[r1]) * inv(d)) % p
                        if all((a*ci[r] + bb*cj[r] - t[r]) % p == 0 for r in range(m)):
                            sol = (a, bb)
                        done = True; break
                if done: break
            if sol and sol[0] and sol[1]:
                gams.add(gam); blkset.add((i, j))
    return len(gams), len(blkset)

best_mca = 0; checked = 0
for T1 in itertools.combinations(range(n), 3):
    rest = [i for i in range(n) if i not in T1]
    for T2 in itertools.combinations(rest, 3):
        if list(T1) > list(T2): continue
        b1 = span_basis(T1); b2 = span_basis(T2)
        if len(b1) != 3 or len(b2) != 3: continue
        W = intersection(b1, b2)
        if len(W) != 2: continue
        w0, w1 = W
        dirs = [(1, t) for t in range(p)] + [(0, 1)]
        for (dc, dd) in dirs:
            dvec = [(dc*w0[r] + dd*w1[r]) % p for r in range(m)]
            if all(v == 0 for v in dvec): continue
            cc, cd = (0, 1) if (dc, dd) != (0, 1) else (1, 0)
            for s in range(p):
                bvec = [(s*(cc*w0[r] + cd*w1[r])) % p for r in range(m)]
                cg, nb = incidence_count(bvec, dvec)
                if cg >= 7 and nb >= 3:   # multi-block candidates only
                    cnt = exact_bad_count(bvec, dvec)
                    checked += 1
                    if cnt > best_mca:
                        best_mca = cnt
                        print("new MCA best:", cnt, "T1,T2:", T1, T2, "(incidence", cg, "blocks", nb, ")")
print("candidates mca-checked:", checked)
print("EXACT two-triangle-stratum MCA max:", best_mca)
