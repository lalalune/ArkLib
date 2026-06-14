# Band-4 boundary falsifier at (13, mu_12, k=6), d = 7 = 2b-1, m = 6.
# Cliques = 4-subsets (span dim 4, codim 2 in F^6). Generic: only 2 cliques share a line
# -> 8 scalars. Coset question: do the THREE mu_4-coset cliques {0,3,6,9},{1,4,7,10},
# {2,5,8,11} share a 2-plane (-> 12 = n scalars)?
import itertools
p = 13; g = 2
xs = [pow(g, i, p) for i in range(12)]
n, k, m, b = 12, 6, 6, 4
def inv(a): return pow(a % p, p - 2, p)
eta = []
for i in range(n):
    pr = 1
    for l in range(n):
        if l != i: pr = (pr * (xs[i] - xs[l])) % p
    eta.append(inv(pr))
cols = [[(eta[i] * pow(xs[i], t, p)) % p for t in range(m)] for i in range(n)]

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

cosets = [(0,3,6,9), (1,4,7,10), (2,5,8,11)]
spans = []
for T in cosets:
    bs, _ = rref([cols[i] for i in T])
    spans.append(bs)
    print("coset", T, "span dim", len(bs))

# pairwise and triple intersections
duals = [nullspace(s) for s in spans]
for (a, bb) in itertools.combinations(range(3), 2):
    W = nullspace(duals[a] + duals[bb])
    print(f"dim(span{a} ∩ span{bb}) =", len(W))
W3 = nullspace(duals[0] + duals[1] + duals[2])
print("dim(triple intersection) =", len(W3))

if len(W3) >= 2:
    print("NON-GENERIC ALIGNMENT: triple intersection carries lines — scanning...")
    blocks = list(itertools.combinations(range(n), 3))
    bduals = {B: nullspace([cols[i] for i in B]) for B in blocks}
    def line_gammas(s0, s1):
        out = {}
        for B, ws in bduals.items():
            consistent_gam = None; ok = True; free_all = True
            for w in ws:
                a1 = sum(x*y for x, y in zip(w, s0)) % p
                b1 = sum(x*y for x, y in zip(w, s1)) % p
                if b1 == 0:
                    if a1 != 0: ok = False; break
                else:
                    free_all = False
                    gam = (-a1 * inv(b1)) % p
                    if consistent_gam is None: consistent_gam = gam
                    elif consistent_gam != gam: ok = False; break
            if ok and not free_all and consistent_gam is not None:
                out[B] = consistent_gam
        return out
    w0, w1 = W3[0], W3[1]
    best = 0; bestdata = None
    dirs = [(1, t) for t in range(p)] + [(0, 1)]
    for (dc, dd) in dirs:
        dvec = [(dc*w0[r] + dd*w1[r]) % p for r in range(m)]
        if all(v == 0 for v in dvec): continue
        cc, cd = (0, 1) if (dc, dd) != (0, 1) else (1, 0)
        for s in range(p):
            bvec = [(s*(cc*w0[r] + cd*w1[r])) % p for r in range(m)]
            lg = line_gammas(bvec, dvec)
            gams = set(lg.values())
            if len(gams) > best:
                best = len(gams); bestdata = (bvec, dvec, lg)
    print("max distinct-gamma incidence on triple-intersection lines:", best)
    if bestdata and best >= 9:
        bvec, dvec, lg = bestdata
        # mcaEvent verification
        def interpolable(pts, vals):
            rows = [[pow(x, jj, p) for jj in range(k)] + [v % p] for x, v in zip(pts, vals)]
            nr = len(rows); r = 0
            for c in range(k):
                piv = next((i for i in range(r, nr) if rows[i][c]), None)
                if piv is None: continue
                rows[r], rows[piv] = rows[piv], rows[r]
                ivv = inv(rows[r][c])
                rows[r] = [(a*ivv) % p for a in rows[r]]
                for i in range(nr):
                    if i != r and rows[i][c]:
                        f = rows[i][c]
                        rows[i] = [(a - f*bb2) % p for a, bb2 in zip(rows[i], rows[r])]
                r += 1
            return all(not (all(a == 0 for a in row[:-1]) and row[-1] != 0) for row in rows)
        def word_from_synd(sv):
            rows = [[(eta[i] * pow(xs[i], t, p)) % p for i in range(m)] + [sv[t]] for t in range(m)]
            for c in range(m):
                piv = next(i for i in range(c, m) if rows[i][c])
                rows[c], rows[piv] = rows[piv], rows[c]
                ivv = inv(rows[c][c])
                rows[c] = [(a*ivv) % p for a in rows[c]]
                for i in range(m):
                    if i != c and rows[i][c]:
                        f = rows[i][c]
                        rows[i] = [(a - f*bb2) % p for a, bb2 in zip(rows[i], rows[c])]
            return [rows[i][m] for i in range(m)] + [0]*(n - m)
        u1 = word_from_synd(dvec); u0 = word_from_synd(bvec)
        agree_floor = n - (b - 1)   # 9
        bad = []
        for gam in range(p):
            y = [(u0[i] + gam*u1[i]) % p for i in range(n)]
            found = False
            for esz in range(0, n - agree_floor + 1):
                for E in itertools.combinations(range(n), esz):
                    Sc = [i for i in range(n) if i not in E]
                    pts = [xs[i] for i in Sc]
                    if not interpolable(pts, [y[i] for i in Sc]): continue
                    if not (interpolable(pts, [u0[i] for i in Sc]) and
                            interpolable(pts, [u1[i] for i in Sc])):
                        found = True; break
                if found: break
            if found: bad.append(gam)
        print("EXACT mcaEvent bad set:", bad, "count", len(bad))
else:
    print("generic alignment only — band-4 boundary capped at ~2b = 8 by cliques")
