#!/usr/bin/env python3
"""probe_counting_gap.py — the TRUE max badCount in the unpinned window left by O84
(#232; exact arithmetic over GF(p); follows probe_ud_affine_extraction.py).

In e-units (e = n - t, t = ceil((1-delta)n)) the unpinned window (d/(3n), (d-1)/(2n)]
is: 3e >= d (the O84 affine-subtraction proof is unavailable) AND 2e <= d-1 (unique
decoding still holds, so badness reduces to: the unique decode w of u0+gamma*u1 has
agreement >= t and its full agreement set A fails joint row interpolation).  O84
observed max badCount 3 <= 2e+1 there and left the conjecture
"badCount <= 2(n-t)+1 in the gap" open as a pure counting question.

STRUCTURE INSIGHT DRIVING THE HUNT (then verified machine-exactly): two bad scalars
whose decodes lie on a common affine codeword family pin that family (O84); DISTINCT
families differ by an m=2-interleaved codeword whose column support is contained in
the union of the family error supports.  Families of support e+1 contribute up to e+1
bad scalars each (one cancellation per scalar, Mobius-distinct ratios), and two such
families can coexist iff 2(e+1) >= d -- i.e. exactly on the TOP SLICE of the gap
(2e in {d-2, d-1}).  Strictly inside (d >= 2e+3) every pair of (e+1)-families is
forced equal by the minimum distance.  Hence:

C1 (CONSTRUCTION, the falsifier): the multi-family Mobius construction.
    e := (h restricted to T1) for codeword pairs h_j vanishing off T1 u T_j and
    agreeing with e on T1 (kernel solve).  Predicted badCount ~ L*(e+1) > 2e+1 on the
    top slice.  Points: A1 (7,6,2) e=2 L=2; A2 (11,10,6) e=2 L=3; A3 (13,13,9) e=2
    L=4-shape; A4 (97,16,8) e=4 L=2 (the O84 hunt code!); A5 (13,11,6) d=6 EVEN top
    e=2 L=3; A6 (13,12,4) d=9 e=4 L=2.
C2 (EXHAUSTIVE ground truth): q=7 RS(6,2) and RS(7,3) (d=5, e=2): every coset-pair
    class (affine-class reduction, proven invariances, spot-checked): the TRUE max
    badCount + histogram.  2e+1 = 5 < q = 7, so the bound is falsifiable.
C3 (INTERIOR of the gap, d >= 2e+3): adversarial hunts where the construction
    provably collapses: (97,16,8) e=3; (13,12,4) e=3; (13,12,2) d=11 e=4.
    g-planting (O84), 2-g nesting, two-cancel, random, structured-interior.
C4 (NON-RS): random non-MDS [8,3,5] over F_7 (d < n-k+1, so not GRS): attack search
    over low-joint-support codeword pairs + random stacks.
C5 (CEILINGS on record stacks): Lambda2 = m=2-interleaved list size at column radius
    2e; check the PROVEN O74/O85 ceiling badCount <= 1 + 2e*Lambda2 and the sharper
    candidate badCount <= (e+1)*Lambda2.

Exit-0 gates are measurement-integrity only (exhaustive coverage accounting,
invariance spot checks, decoder cross-check, proven-ceiling consistency); the
refutation/survival findings are reported from data.
"""

import itertools
import random
import sys
from collections import Counter

random.seed(232087)


# ---------------------------------------------------------------- field / poly
def inv(a, p):
    return pow(a % p, p - 2, p)


def poly_eval(c, x, p):
    r = 0
    for cc in reversed(c):
        r = (r * x + cc) % p
    return r


def poly_mul_linear(num, root, p):
    out = [0] * (len(num) + 1)
    for a in range(len(num)):
        out[a] = (out[a] - root * num[a]) % p
        out[a + 1] = (out[a + 1] + num[a]) % p
    return out


def poly_deg(c, p):
    for i in range(len(c) - 1, -1, -1):
        if c[i] % p:
            return i
    return -1


def poly_div_exact(Q, E, p):
    Q = [x % p for x in Q]
    dq, de = poly_deg(Q, p), poly_deg(E, p)
    if de < 0:
        return None
    if dq < 0:
        return [0]
    if dq < de:
        return None
    out = [0] * (dq - de + 1)
    lead = inv(E[de], p)
    for i in range(dq - de, -1, -1):
        c = (Q[i + de] * lead) % p
        out[i] = c
        if c:
            for j in range(de + 1):
                Q[i + j] = (Q[i + j] - c * E[j]) % p
    if any(x % p for x in Q):
        return None
    return out


def rref(M, ncols, p):
    M = [row[:] for row in M]
    piv = []
    r = 0
    for c in range(ncols):
        pr = None
        for rr in range(r, len(M)):
            if M[rr][c] % p:
                pr = rr
                break
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        iv = inv(M[r][c], p)
        M[r] = [x * iv % p for x in M[r]]
        for rr in range(len(M)):
            if rr != r and M[rr][c] % p:
                f = M[rr][c]
                Mr = M[r]
                M[rr] = [(M[rr][j] - f * Mr[j]) % p for j in range(ncols)]
        piv.append((r, c))
        r += 1
        if r == len(M):
            break
    return M, piv


def kernel_basis(M, ncols, p):
    Mr, piv = rref(M, ncols, p)
    pcols = {c for _, c in piv}
    basis = []
    for f in range(ncols):
        if f in pcols:
            continue
        v = [0] * ncols
        v[f] = 1
        for (r, c) in piv:
            v[c] = (-Mr[r][f]) % p
        basis.append(v)
    return basis


def solvable(rows, rhs, p):
    """exists x with rows.x = rhs?"""
    if not rows:
        return True
    k = len(rows[0])
    aug = [rows[i][:] + [rhs[i]] for i in range(len(rows))]
    _, piv = rref(aug, k + 1, p)
    return all(c != k for _, c in piv)


def solve_one(rows, rhs, p):
    ncols = len(rows[0])
    aug = [rows[i][:] + [rhs[i]] for i in range(len(rows))]
    Mr, piv = rref(aug, ncols + 1, p)
    if any(c == ncols for _, c in piv):
        return None
    v = [0] * ncols
    for (r, c) in piv:
        v[c] = Mr[r][ncols]
    return v


# ---------------------------------------------------------------- codes
class LinearCode:
    def __init__(self, p, G):
        self.p = p
        self.G = G
        self.k = len(G)
        self.n = len(G[0])
        self.cols = [[G[j][i] for j in range(self.k)] for i in range(self.n)]

    def encode(self, x):
        p, n = self.p, self.n
        return [sum(x[j] * self.G[j][i] for j in range(self.k)) % p
                for i in range(n)]

    def codewords(self):
        for x in itertools.product(range(self.p), repeat=self.k):
            yield self.encode(x)

    def min_distance(self):
        d = self.n
        for w in self.codewords():
            wt = sum(1 for v in w if v)
            if 0 < wt < d:
                d = wt
        return d

    def row_ok(self, u, A):
        """exists codeword agreeing with u on every index of A?"""
        return solvable([self.cols[i] for i in A], [u[i] % self.p for i in A],
                        self.p)

    def random_codeword(self):
        return self.encode([random.randrange(self.p) for _ in range(self.k)])


class RSCode(LinearCode):
    def __init__(self, p, n, k, xs=None):
        if xs is None:
            xs = list(range(n)) if n < p else None
        assert xs is not None and len(set(xs)) == n
        self.xs = xs
        G = [[pow(x, j, p) for x in xs] for j in range(k)]
        super().__init__(p, G)
        self.d = n - k + 1
        self.powmat = [[pow(x, j, p) for j in range(n)] for x in xs]

    def bw_decode(self, y, e):
        """unique codeword within distance e (needs 2e <= n-k), else None."""
        n, k, p = self.n, self.k, self.p
        assert 2 * e <= n - k
        ncols = (k + e) + (e + 1)
        M = []
        for i in range(n):
            row = self.powmat[i][:k + e] + \
                [(-y[i] * self.powmat[i][j]) % p for j in range(e + 1)]
            M.append(row)
        basis = kernel_basis(M, ncols, p)
        if not basis:
            return None
        v = basis[0]
        Q, E = v[:k + e], v[k + e:]
        quot = poly_div_exact(Q, E, p)
        if quot is None or poly_deg(quot, p) >= k:
            return None
        w = self.encode((quot + [0] * k)[:k])
        if sum(1 for i in range(n) if w[i] != y[i]) <= e:
            return w
        return None


def exhaustive_decode(code, cwlist, y, e):
    n = code.n
    for w in cwlist:
        if sum(1 for i in range(n) if w[i] != y[i]) <= e:
            return list(w)
    return None


def bad_set(code, u0, u1, e, decoder):
    """[(gamma, w)] of mcaEvent-bad scalars at floor t = n - e (UD regime).
    gamma bad <=> unique decode w of u0+gamma*u1 exists within distance e and the
    full agreement set A fails joint row interpolation (witness-set monotonicity +
    UD uniqueness, as in the O78/O84 probes)."""
    p, n = code.p, code.n
    out = []
    for g in range(p):
        y = [(u0[i] + g * u1[i]) % p for i in range(n)]
        w = decoder(y, e)
        if w is None:
            continue
        A = [i for i in range(n) if y[i] == w[i]]
        assert len(A) >= n - e
        if not (code.row_ok(u0, A) and code.row_ok(u1, A)):
            out.append((g, tuple(w)))
    return out


def lambda2(code, cwlist, u0, u1, radius):
    """m=2 interleaved list size at column radius `radius` (small codes only)."""
    n = code.n
    cnt = 0
    for c0 in cwlist:
        # prune: column distance counts i with (c0 or c1 mismatch); a c0 mismatch
        # alone already costs, so require |{i: c0_i != u0_i}| <= radius first.
        if sum(1 for i in range(n) if c0[i] != u0[i]) > radius:
            continue
        for c1 in cwlist:
            dist = sum(1 for i in range(n)
                       if c0[i] != u0[i] or c1[i] != u1[i])
            if dist <= radius:
                cnt += 1
    return cnt


# ---------------------------------------------------------------- C1 construction
def build_multifamily(code, e, T1, Tjs, tries=400):
    """e := (h restricted to T1); families j: codeword pairs h_j with rows vanishing
    off T1 u T_j and h_j = e on T1 (homogeneous kernel solve, per row).
    Returns ((u0,u1), predicted_gammas) or None."""
    p, n, k, xs = code.p, code.n, code.k, code.xs
    a = len(T1)
    fams = []
    for Tj in Tjs:
        comp = [i for i in range(n) if i not in T1 and i not in Tj]
        if len(comp) > k - 1:
            return None
        v = [1]
        for i in comp:
            v = poly_mul_linear(v, xs[i], p)
        D = k - len(comp)
        fams.append((Tj, v, D))
    ncols = a + sum(D for _, _, D in fams)
    rows = []
    off = a
    for (Tj, v, D) in fams:
        for ii, i in enumerate(T1):
            row = [0] * ncols
            row[ii] = p - 1
            vi = poly_eval(v, xs[i], p)
            for t in range(D):
                row[off + t] = vi * pow(xs[i], t, p) % p
            rows.append(row)
        off += D
    basis = kernel_basis(rows, ncols, p)
    if len(basis) < 2:
        # dim < 2 forces the two rows proportional => constant ratios => collapse
        print(f"   [multifamily kernel dim {len(basis)} < 2: rigid, collapses]")
        return None

    def combo():
        while True:
            sol = [0] * ncols
            for b in basis:
                c = random.randrange(p)
                for j in range(ncols):
                    sol[j] = (sol[j] + c * b[j]) % p
            if any(sol):
                return sol

    def realize(sol):
        evec = [0] * n
        for ii, i in enumerate(T1):
            evec[i] = sol[ii]
        hvecs = []
        off = a
        for (Tj, v, D) in fams:
            l = sol[off:off + D]
            off += D
            hvecs.append([poly_eval(v, x, p) * poly_eval(l, x, p) % p
                          for x in xs])
        return evec, hvecs

    for _ in range(tries):
        e0, h0s = realize(combo())
        e1, h1s = realize(combo())
        rats = []
        ok = True
        for i in T1:
            if e1[i] == 0:
                ok = False
                break
            rats.append((-e0[i] * inv(e1[i], p)) % p)
        if ok:
            for (Tj, _, _), h0, h1 in zip(fams, h0s, h1s):
                for i in Tj:
                    if h1[i] == 0:
                        ok = False
                        break
                    rats.append((-h0[i] * inv(h1[i], p)) % p)
                if not ok:
                    break
        if ok and len(set(rats)) == len(rats):
            return (e0, e1), sorted(set(rats))
    return None


def run_construction(label, p, n, k, e, T1, Tjs, xs=None, family_one_counts=True):
    code = RSCode(p, n, k, xs=xs)
    d = code.d
    in_gap = (3 * e >= d) and (2 * e <= d - 1)
    res = build_multifamily(code, e, T1, Tjs)
    if res is None:
        print(f"C1 {label} (q={p},n={n},k={k},d={d},e={e}): construction BLOCKED "
              f"(no kernel / structure)")
        return None
    (u0, u1), predicted = res
    bads = bad_set(code, u0, u1, e, lambda y, ee: code.bw_decode(y, ee))
    bc = len(bads)
    bound = 2 * e + 1
    print(f"C1 {label} (q={p},n={n},k={k},d={d},e={e}, in-gap={in_gap}, "
          f"3e>=d:{3*e >= d}, 2e<=d-1:{2*e <= d-1}): badCount={bc} vs 2e+1={bound} "
          f"-> {'EXCEEDS' if bc > bound else 'within'}; predicted set size "
          f"{len(predicted)}, bad gammas {sorted(g for g, _ in bads)}")
    return code, u0, u1, bc, bads


# ---------------------------------------------------------------- C2 exhaustive
def run_exhaustive(label, p, n, k, e, xs=None):
    """Exhaustive over affine-class representatives of coset pairs.
    Invariances used (each proven; spot-checked below):
      (u0,u1) -> (u0+c0, u1+c1) codeword shifts;
      (u0,u1) -> (lam*(u0+alpha*u1), mu*u1)  (badness reparametrizes gamma).
    Classes: scaling reps r1 of nonzero u1-syndromes x orbits of s0 under
    s0 -> lam*s0 + beta*r1; plus the s1=0 stratum (provably badCount 0)."""
    code = RSCode(p, n, k, xs=xs)
    d = code.d
    nk = n - k
    assert 3 * e >= d and 2 * e <= d - 1, "must be in the gap window"
    # dual matrix H (rows: kernel of G acting on coordinates)
    H = kernel_basis(code.G, n, p)
    assert len(H) == nk

    def synd(v):
        return tuple(sum(H[r][i] * v[i] for i in range(n)) % p
                     for r in range(nk))

    # right inverse: rep vectors for unit syndromes
    R = []
    for j in range(nk):
        unit = [1 if r == j else 0 for r in range(nk)]
        sol = solve_one([[H[r][i] for i in range(n)] for r in range(nk)],
                        unit, p)
        assert sol is not None
        R.append(sol)

    def rep_vec(s):
        v = [0] * n
        for j in range(nk):
            if s[j]:
                for i in range(n):
                    v[i] = (v[i] + s[j] * R[j][i]) % p
        return v

    # decode table: syndrome -> error vector of weight <= e (unique by 2e <= d-1)
    table = {}
    for wt in range(e + 1):
        for supp in itertools.combinations(range(n), wt):
            for vals in itertools.product(range(1, p), repeat=wt):
                err = [0] * n
                for i, v in zip(supp, vals):
                    err[i] = v
                s = synd(err)
                assert s not in table, "UD violated: syndrome collision"
                table[s] = err

    def badcount(u0, u1, s0, s1):
        cnt = 0
        gam = []
        for g in range(p):
            s = tuple((s0[j] + g * s1[j]) % p for j in range(nk))
            err = table.get(s)
            if err is None:
                continue
            A = [i for i in range(n) if err[i] == 0]
            if not (code.row_ok(u0, A) and code.row_ok(u1, A)):
                cnt += 1
                gam.append(g)
        return cnt, gam

    synds = list(itertools.product(range(p), repeat=nk))
    sidx = {s: i for i, s in enumerate(synds)}
    S = len(synds)
    zero = tuple([0] * nk)

    # scaling classes of nonzero syndromes
    seen = bytearray(S)
    seen[sidx[zero]] = 1
    r1_reps = []
    for s in synds:
        if seen[sidx[s]]:
            continue
        r1_reps.append(s)
        for lam in range(1, p):
            seen[sidx[tuple(lam * x % p for x in s)]] = 1
    assert len(r1_reps) == (S - 1) // (p - 1)

    hist = Counter()
    records = []
    total_classes = 0
    bound = 2 * e + 1
    over = 0
    for r1 in r1_reps:
        u1 = rep_vec(r1)
        seen0 = bytearray(S)
        for s0 in synds:
            if seen0[sidx[s0]]:
                continue
            # mark orbit {lam*s0 + beta*r1}
            for lam in range(1, p):
                base = tuple(lam * x % p for x in s0)
                for beta in range(p):
                    seen0[sidx[tuple((base[j] + beta * r1[j]) % p
                                     for j in range(nk))]] = 1
            total_classes += 1
            u0 = rep_vec(s0)
            bc, gam = badcount(u0, u1, s0, r1)
            hist[bc] += 1
            if bc > bound:
                over += 1
            if bc >= bound:
                records.append((bc, s0, r1, gam))
        assert all(seen0), "orbit coverage incomplete"
    # s1 = 0 stratum: u1 in C -> never bad (row1 trivially interpolates and the
    # decode w minus gamma*c1 re-interpolates row0); verify by running it.
    z = [0] * n
    for s0 in synds[::max(1, S // 50)]:
        bc, _ = badcount(rep_vec(s0), z, s0, zero)
        assert bc == 0, "s1=0 stratum must have badCount 0"

    records.sort(reverse=True)
    mx = max(hist)
    print(f"C2 EXHAUSTIVE (q={p},n={n},k={k},d={d},e={e}): {total_classes} classes "
          f"(x{(p-1)*p} affine orbit x codeword shifts = all stacks); "
          f"TRUE max badCount = {mx}; classes with badCount>2e+1={bound}: {over}")
    print(f"   histogram {dict(sorted(hist.items()))}")

    # invariance spot-check: random transforms + codeword shifts preserve badCount
    decoder = lambda y, ee: code.bw_decode(y, ee)
    for trial in range(6):
        bc0, s0, r1, _ = records[trial % len(records)]
        u0, u1 = rep_vec(s0), rep_vec(r1)
        lam, mu = random.randrange(1, p), random.randrange(1, p)
        alpha = random.randrange(p)
        c0, c1 = code.random_codeword(), code.random_codeword()
        U0 = [(lam * (u0[i] + alpha * u1[i]) + c0[i]) % p for i in range(n)]
        U1 = [(mu * u1[i] + c1[i]) % p for i in range(n)]
        bads = bad_set(code, U0, U1, e, decoder)
        assert len(bads) == bc0, f"invariance violated: {len(bads)} != {bc0}"
    print(f"   invariance spot-checks (6 random affine transforms + shifts): OK")

    # BW cross-check on one record stack (decoder port integrity)
    cwlist = [tuple(w) for w in code.codewords()] if p ** k <= 3000 else None
    if cwlist:
        bc0, s0, r1, _ = records[0]
        u0, u1 = rep_vec(s0), rep_vec(r1)
        b1 = bad_set(code, u0, u1, e, decoder)
        b2 = bad_set(code, u0, u1, e,
                     lambda y, ee: exhaustive_decode(code, cwlist, y, ee))
        assert b1 == b2, "BW decoder disagrees with exhaustive decoder"
        print(f"   BW vs exhaustive decoder on record stack: identical "
              f"({len(b1)} bad)")

    # ceilings on the top record stacks
    if cwlist:
        for bc0, s0, r1, gam in records[:3]:
            u0, u1 = rep_vec(s0), rep_vec(r1)
            L2 = lambda2(code, cwlist, u0, u1, 2 * e)
            proven = 1 + 2 * e * L2
            cand = (e + 1) * L2
            print(f"   record bc={bc0} gammas={gam}: Lambda2(2e)={L2}; "
                  f"proven 1+2e*L2={proven} ({'OK' if bc0 <= proven else 'VIOLATED'}); "
                  f"candidate (e+1)*L2={cand} "
                  f"({'OK' if bc0 <= cand else 'VIOLATED'})")
            assert bc0 <= proven, "PROVEN ceiling violated -- harness bug"
    return mx, over, records


# ---------------------------------------------------------------- C3 hunts
def plant_two_cancel(code, e):
    p, n = code.p, code.n
    c0, c1 = code.random_codeword(), code.random_codeword()
    g1, g2 = random.sample(range(1, p), 2)
    E = random.sample(range(n), 2 * e)
    e0, e1 = [0] * n, [0] * n
    for j, i in enumerate(E):
        e1[i] = random.randrange(1, p)
        gt = g1 if j < e else g2
        e0[i] = (-gt * e1[i]) % p
    return ([(c0[i] + e0[i]) % p for i in range(n)],
            [(c1[i] + e1[i]) % p for i in range(n)])


def plant_g_attack(code, e, gcount=1):
    """O84-style g-planting, generalized: gcount weight-d codewords g; error support
    split among them so extra scalars decode off the affine family."""
    p, n, k, xs = code.p, code.n, code.k, code.xs
    gs = []
    for _ in range(gcount):
        roots = random.sample(range(n), k - 1)
        coeffs = [1]
        for i in roots:
            coeffs = poly_mul_linear(coeffs, xs[i], p)
        lead = random.randrange(1, p)
        gs.append([poly_eval(coeffs, x, p) * lead % p for x in xs])
    e0, e1 = [0] * n, [0] * n
    used = set()
    scal = random.sample(range(1, p), 2 * gcount + 1)
    g3 = scal[-1]
    per = (2 * e) // gcount
    for gi, g in enumerate(gs):
        supp = [i for i in range(n) if g[i] % p and i not in used][:per]
        used.update(supp)
        ga, gb = scal[2 * gi], scal[2 * gi + 1]
        for j, i in enumerate(supp):
            gc = ga if j < per // 2 else gb
            e1[i] = g[i] * inv((g3 - gc) % p, p) % p
            e0[i] = (g[i] - g3 * e1[i]) % p
    c0, c1 = code.random_codeword(), code.random_codeword()
    return ([(c0[i] + e0[i]) % p for i in range(n)],
            [(c1[i] + e1[i]) % p for i in range(n)])


def random_error_stack(code, suppsize):
    p, n = code.p, code.n
    c0, c1 = code.random_codeword(), code.random_codeword()
    E = random.sample(range(n), suppsize)
    e0, e1 = [0] * n, [0] * n
    for i in E:
        e0[i] = random.randrange(p)
        e1[i] = random.randrange(1, p)
    return ([(c0[i] + e0[i]) % p for i in range(n)],
            [(c1[i] + e1[i]) % p for i in range(n)])


def run_interior(label, p, n, k, e, ntrials, xs=None, structured=None,
                 interior=True):
    code = RSCode(p, n, k, xs=xs)
    d = code.d
    assert 3 * e >= d and 2 * e <= d - 1, "must be in the gap"
    if interior:
        assert d >= 2 * e + 3, "interior means d >= 2e+3"
    decoder = lambda y, ee: code.bw_decode(y, ee)
    bound = 2 * e + 1
    mx, over = 0, 0
    stacks = []
    for _ in range(ntrials):
        stacks.append(plant_g_attack(code, e, gcount=1))
    for _ in range(ntrials // 2):
        stacks.append(plant_g_attack(code, e, gcount=2))
    for _ in range(ntrials // 2):
        stacks.append(plant_two_cancel(code, e))
    for _ in range(ntrials // 2):
        stacks.append(random_error_stack(code, 2 * e))
        stacks.append(random_error_stack(code, e + 1))
    if structured:
        for (T1, Tjs) in structured:
            res = build_multifamily(code, e, T1, Tjs)
            if res is not None:
                stacks.append(res[0])
    for (u0, u1) in stacks:
        bc = len(bad_set(code, u0, u1, e, decoder))
        mx = max(mx, bc)
        if bc > bound:
            over += 1
    print(f"C3 INTERIOR {label} (q={p},n={n},k={k},d={d},e={e}, d>=2e+3): "
          f"{len(stacks)} adversarial stacks, max badCount {mx} vs 2e+1={bound}, "
          f"violations {over}")
    return mx, over


# ---------------------------------------------------------------- C4 non-RS
def run_nonRS(p, n, k, target_d, e):
    code = None
    for _ in range(4000):
        G = [[random.randrange(p) for _ in range(n)] for _ in range(k)]
        c = LinearCode(p, G)
        # full rank?
        _, piv = rref([row[:] for row in G], n, p)
        if len(piv) < k:
            continue
        if c.min_distance() == target_d:
            code = c
            break
    if code is None:
        print(f"C4 non-RS: no [({n},{k},{target_d})]_{p} code found in budget; SKIP")
        return None
    d = target_d
    assert d < n - k + 1, "want strictly non-MDS (hence not GRS)"
    assert 3 * e >= d and 2 * e <= d - 1
    cwlist = [tuple(w) for w in code.codewords()]
    decoder = lambda y, ee: exhaustive_decode(code, cwlist, y, ee)
    bound = 2 * e + 1
    mx, over = 0, 0
    # attack search: codeword pairs with small joint support
    tried = 0
    for c0 in cwlist:
        if not any(c0):
            continue
        for c1 in cwlist:
            if not any(c1):
                continue
            U = [i for i in range(n) if c0[i] or c1[i]]
            if len(U) > 2 * (e + 1):
                continue
            tried += 1
            if tried > 400:
                break
            # all splits of U into T1 of size e+1 (rest is the second family)
            for T1 in itertools.combinations(U, e + 1):
                e0 = [c0[i] if i in T1 else 0 for i in range(n)]
                e1 = [c1[i] if i in T1 else 0 for i in range(n)]
                bc = len(bad_set(code, e0, e1, e, decoder))
                mx = max(mx, bc)
                if bc > bound:
                    over += 1
        if tried > 400:
            break
    # random stacks
    for _ in range(150):
        u0, u1 = random_error_stack(code, random.choice([e + 1, 2 * e]))
        bc = len(bad_set(code, u0, u1, e, decoder))
        mx = max(mx, bc)
        if bc > bound:
            over += 1
    print(f"C4 NON-RS [({n},{k},{d})]_{p} (non-MDS, e={e}): attack pairs tried "
          f"{tried}, max badCount {mx} vs 2e+1={bound}, stacks over: {over}")
    return mx, over


# ---------------------------------------------------------------- main
def main():
    print("=" * 78)
    print("C1: multi-family Mobius construction (the falsifier) -- top slice")
    print("=" * 78)
    results = {}
    # A1: smallest odd-d top point; q=7 > 2e+2=6
    results['A1'] = run_construction(
        "A1 top-odd L=2", 7, 6, 2, 2, [0, 1, 2], [[3, 4, 5]], xs=list(range(1, 7)))
    # A2: three families
    results['A2'] = run_construction(
        "A2 top-odd L=3", 11, 10, 6, 2, [0, 1, 2], [[3, 4, 5], [6, 7, 8]],
        xs=list(range(10)))
    # A3: T1 of size e+2 plus three (e+1)-families
    results['A3'] = run_construction(
        "A3 top-odd L=4-shape", 13, 13, 9, 2, [0, 1, 2, 3],
        [[4, 5, 6], [7, 8, 9], [10, 11, 12]], xs=list(range(13)))
    # A4: the O84 hunt code (97,16,8), top of its gap e=4
    results['A4'] = run_construction(
        "A4 top-odd L=2 (O84 code)", 97, 16, 8, 4, [0, 1, 2, 3, 4],
        [[5, 6, 7, 8, 9]], xs=list(range(16)))
    # A5: EVEN d top slice (d=6, 2e+2=6=d) -- needs |T1| > e+1 for linear freedom
    results['A5'] = run_construction(
        "A5 top-EVEN L=3", 13, 11, 6, 2, [0, 1, 2, 3, 4],
        [[5, 6, 7], [8, 9, 10]], xs=list(range(11)))
    # A6: small-field odd-d top at d=9
    results['A6'] = run_construction(
        "A6 top-odd L=2 small-q", 13, 12, 4, 4, [0, 1, 2, 3, 4],
        [[5, 6, 7, 8, 9]], xs=list(range(1, 13)))
    # A7: e=1 (d=3) -- kernel dim per extra family is 3-e=2, so L is UNBOUNDED:
    # six size-2 families predict badCount ~ n >> 2e+2.  Kills any f(e)-only law.
    results['A7'] = run_construction(
        "A7 top-odd e=1 L=6", 13, 12, 10, 1, [0, 1],
        [[2, 3], [4, 5], [6, 7], [8, 9], [10, 11]], xs=list(range(1, 13)))

    # ceilings on the A1 stack (code small enough for exact Lambda2)
    if results['A1']:
        code, u0, u1, bc, _ = results['A1']
        cwlist = [tuple(w) for w in code.codewords()]
        L2 = lambda2(code, cwlist, u0, u1, 4)
        print(f"C5 ceilings on A1 stack: badCount={bc}, Lambda2(2e)={L2}, "
              f"proven 1+2e*L2={1+4*L2} ({'OK' if bc <= 1+4*L2 else 'VIOLATED'}), "
              f"candidate (e+1)*L2={3*L2} ({'OK' if bc <= 3*L2 else 'VIOLATED'})")
        assert bc <= 1 + 4 * L2

    print()
    print("=" * 78)
    print("C2: exhaustive ground truth at q=7, d=5, e=2 (2e+1=5 falsifiable, q=7)")
    print("=" * 78)
    ex1 = run_exhaustive("RS(6,2)", 7, 6, 2, 2, xs=list(range(1, 7)))
    ex2 = run_exhaustive("RS(7,3)", 7, 7, 3, 2, xs=list(range(7)))

    print()
    print("=" * 78)
    print("C3: the interior of the gap (d >= 2e+3): does 2e+1 survive?")
    print("=" * 78)
    i1 = run_interior("(97,16,8) e=3", 97, 16, 8, 3, 30, xs=list(range(16)),
                      structured=[([0, 1, 2, 3], [[4, 5, 6, 7, 8, 9]]),
                                  ([0, 1, 2, 3], [[4, 5, 6, 7, 8]])])
    i2 = run_interior("(13,12,4) e=3", 13, 12, 4, 3, 120, xs=list(range(1, 13)),
                      structured=[([0, 1, 2, 3], [[4, 5, 6, 7, 8]])])
    i3 = run_interior("(13,12,2) d=11 e=4", 13, 12, 2, 4, 120,
                      xs=list(range(1, 13)))
    # even-d top slice (d = 2e+2): the RS construction is provably rigid there
    # (|T1 u Tj| <= 2e+2 = d forces 1-dim rows); hunt adversarially instead.
    i4 = run_interior("(13,9,4) d=6 e=2 EVEN-TOP", 13, 9, 4, 2, 150,
                      xs=list(range(9)), interior=False,
                      structured=[([0, 1, 2], [[3, 4, 5]]),
                                  ([0, 1, 2, 3], [[4, 5, 6]]),
                                  ([0, 1, 2, 3, 4], [[5, 6, 7]])])

    print()
    print("=" * 78)
    print("C4: non-RS (non-MDS) control")
    print("=" * 78)
    nr = run_nonRS(7, 8, 3, 5, 2)

    # ---------------------------------------------------------------- summary
    print()
    print("=" * 78)
    print("SUMMARY")
    print("=" * 78)
    built = [k for k, v in results.items() if v is not None]
    evals = {'A1': 2, 'A2': 2, 'A3': 2, 'A4': 4, 'A5': 2, 'A6': 4, 'A7': 1}
    top_exceed = [(k, v[3]) for k, v in results.items() if v is not None
                  and v[3] > 2 * evals[k] + 1]
    print(f"constructions built: {built}; exceeding 2e+1: {top_exceed}")
    print(f"exhaustive true max (6,2): {ex1[0]} (classes over 2e+1: {ex1[1]}); "
          f"(7,3): {ex2[0]} (over: {ex2[1]})")
    print(f"interior maxima: (97,16,8)e=3: {i1[0]} (viol {i1[1]}); "
          f"(13,12,4)e=3: {i2[0]} (viol {i2[1]}); "
          f"(13,12,2)e=4: {i3[0]} (viol {i3[1]})")
    print(f"even-d top (13,9,4)e=2: max {i4[0]} (viol {i4[1]})")
    if nr:
        print(f"non-RS [8,3,5]_7 max: {nr[0]} (over: {nr[1]})")

    gates = []
    gates.append(("A1 built", results['A1'] is not None))
    gates.append(("A4 built", results['A4'] is not None))
    gates.append(("exhaustive (6,2) done", ex1 is not None))
    gates.append(("exhaustive (7,3) done", ex2 is not None))
    gates.append(("interior measured", i1 is not None and i2 is not None))
    ok = all(g for _, g in gates)
    print(f"integrity gates: {[(nm, bool(g)) for nm, g in gates]}")
    if not ok:
        sys.exit(1)
    print("exit 0")


if __name__ == "__main__":
    main()
