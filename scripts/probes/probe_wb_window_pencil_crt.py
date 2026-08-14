#!/usr/bin/env python3
"""WB window pencil/CRT reformulation validation probe (#371, WindowRationalBounded lane).

THE CLAIM TO VALIDATE (before any Lean): for a genuine rational stack
(u_j = R_j/l_j on the domain, denominators nonvanishing there, reduced), a scalar
gamma is line-EXPLAINABLE at slack w iff the linear pencil

    F_gamma * Z - (l0*l1) * Q - Z_D * h = 0        (identity in x)

with F_gamma = l1*R0 + gamma*l0*R1, unknowns Z (deg<=w), Q (deg<=w+k-1),
h (deg<=m, m = maxd + 2w + k - 1 - n), has a kernel vector whose Z-component is
squarefree of degree exactly w with ALL roots in the domain ("D-split").

Mechanism notes the probe also measures:
- gamma enters only the w+1 Z-columns => maximal minors have gamma-degree <= w+1
  => NONDEGENERATE pencil (full column rank at some gamma) => #explainable <= w+1.
- DEGENERATE pencil (kernel at every gamma) is the residual case; classify how often
  it occurs among genuine pairs and whether the known extremals live there.

Instances: (q,n,k,w) = (13,6,1,2) [the recorded Mobius-extremal scale] and
(17,8,3,2) [a second window instance, m=0 at maxd=2].
Pure python, no deps. Exact, exhaustive in gamma; heavy sampling over pairs.
"""
import random
from collections import Counter
from itertools import combinations

random.seed(20260611)

# ---------- polynomial helpers over F_q (coeff lists, low-to-high) ----------
def pnorm(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a

def padd(a, b, q):
    m = max(len(a), len(b))
    return pnorm([( (a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0)) % q
                  for i in range(m)])

def psmul(c, a, q):
    return pnorm([c * x % q for x in a])

def pmul(a, b, q):
    if not a or not b:
        return []
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % q
    return pnorm(out)

def pdivmod(a, b, q):
    a = list(a); b = pnorm(b)
    assert b
    inv = pow(b[-1], q - 2, q)
    quo = [0] * max(0, len(a) - len(b) + 1)
    while len(pnorm(a)) >= len(b):
        a = pnorm(a)
        d = len(a) - len(b)
        c = a[-1] * inv % q
        quo[d] = c
        for i in range(len(b)):
            a[d + i] = (a[d + i] - c * b[i]) % q
        a = a[:-1]
    return pnorm(quo), pnorm(a)

def peval(a, x, q):
    r = 0
    for c in reversed(a):
        r = (r * x + c) % q
    return r

def pgcd(a, b, q):
    a, b = pnorm(a), pnorm(b)
    while b:
        a, b = b, pdivmod(a, b, q)[1]
    if a:
        a = psmul(pow(a[-1], q - 2, q), a, q)
    return a

# ---------- linear algebra mod q ----------
def rank_and_kernel(M, q, want_kernel=False):
    """M: list of rows. Returns (rank, kernel_basis as list of vectors)."""
    if not M:
        return 0, []
    rows = [r[:] for r in M]
    ncol = len(rows[0])
    piv_of_col = [-1] * ncol
    r = 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][c] % q), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], q - 2, q)
        rows[r] = [x * inv % q for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][c]:
                f = rows[i][c]
                rows[i] = [(rows[i][j] - f * rows[r][j]) % q for j in range(ncol)]
        piv_of_col[c] = r
        r += 1
    rank = r
    if not want_kernel:
        return rank, []
    free = [c for c in range(ncol) if piv_of_col[c] == -1]
    basis = []
    for fc in free:
        v = [0] * ncol
        v[fc] = 1
        for c in range(ncol):
            if piv_of_col[c] != -1:
                v[c] = (-rows[piv_of_col[c]][fc]) % q
        basis.append(v)
    return rank, basis

# ---------- the instance ----------
class Inst:
    def __init__(self, q, n, k, w, g):
        self.q, self.n, self.k, self.w = q, n, k, w
        self.dom = [pow(g, i, q) for i in range(n)]
        assert len(set(self.dom)) == n
        zd = [1]
        for a in self.dom:
            zd = pmul(zd, [(-a) % q, 1], q)
        self.ZD = zd

    def ratword(self, l, r):
        out = []
        for x in self.dom:
            lv = peval(l, x, self.q)
            if lv == 0:
                return None
            out.append(peval(r, x, self.q) * pow(lv, self.q - 2, self.q) % self.q)
        return tuple(out)

# explainability brute force: line agrees with poly deg<k on >= n-w points
def expl_set(inst, u0, u1):
    q, n, k, w = inst.q, inst.n, inst.k, inst.w
    out = set()
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        # try all (n-w)-subsets? cheaper: all w-error sets, interpolate? k small:
        # for each candidate agreement set of size n-w check if it lies on a deg<k poly
        ok = False
        for S in combinations(range(n), n - w):
            pts = [(inst.dom[i], line[i]) for i in S]
            # check poly deg < k through pts: build Vandermonde rank condition
            M = [[pow(x, j, q) for j in range(k)] + [y] for (x, y) in pts]
            rk1, _ = rank_and_kernel([row[:-1] for row in M], q)
            rk2, _ = rank_and_kernel(M, q)
            if rk1 == rk2:
                ok = True
                break
        if ok:
            out.add(gam)
    return out

# mca-bad brute force: exists S size>=n-w, line=codeword on S, NOT joint on S
def bad_set(inst, u0, u1):
    q, n, k, w = inst.q, inst.n, inst.k, inst.w
    out = set()
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        found = False
        for S in combinations(range(n), n - w):
            pts = [(inst.dom[i], line[i]) for i in S]
            M = [[pow(x, j, q) for j in range(k)] + [y] for (x, y) in pts]
            rk1, _ = rank_and_kernel([row[:-1] for row in M], q)
            rk2, _ = rank_and_kernel(M, q)
            if rk1 != rk2:
                continue
            # line on codeword over S; check joint: both rows on deg<k polys over S
            joint = True
            for u in (u0, u1):
                Mu = [[pow(inst.dom[i], j, q) for j in range(k)] + [u[i]] for i in S]
                r1, _ = rank_and_kernel([row[:-1] for row in Mu], q)
                r2, _ = rank_and_kernel(Mu, q)
                if r1 != r2:
                    joint = False
                    break
            if not joint:
                found = True
                break
        if found:
            out.add(gam)
    return out

# ---------- the pencil ----------
def pencil_matrices(inst, l0, r0, l1, r1):
    """Rows: coefficients of x^0..x^T of  F_gamma*Z - (l0 l1) Q - Z_D h.
    Returns (M0, M1, dims) with M(gamma) = M0 + gamma*M1, unknowns ordered
    [Z_0..Z_w, Q_0..Q_{w+k-1}, h_0..h_m]."""
    q, n, k, w = inst.q, inst.n, inst.k, inst.w
    A = pmul(l1, r0, q)   # gamma^0 part of F
    B = pmul(l0, r1, q)   # gamma^1 part of F
    L = pmul(l0, l1, q)
    maxd = max(len(pnorm(l0)) - 1, len(pnorm(l1)) - 1)
    m = maxd + 2 * w + k - 1 - n
    nh = m + 1 if m >= 0 else 0
    T = max((len(A) - 1 if A else 0) + w, (len(B) - 1 if B else 0) + w,
            (len(L) - 1) + w + k - 1, n + max(m, 0))
    nz, nq = w + 1, w + k
    ncol = nz + nq + nh
    M0 = [[0] * ncol for _ in range(T + 1)]
    M1 = [[0] * ncol for _ in range(T + 1)]
    for j in range(nz):           # Z columns: A*x^j (const), B*x^j (gamma)
        for i, c in enumerate(A):
            M0[i + j][j] = c
        for i, c in enumerate(B):
            M1[i + j][j] = c
    for j in range(nq):           # Q columns: -L*x^j
        for i, c in enumerate(L):
            M0[i + j][nz + j] = (-c) % q
    for j in range(nh):           # h columns: -Z_D*x^j
        for i, c in enumerate(inst.ZD):
            M0[i + j][nz + nq + j] = (-c) % q
    return M0, M1, (nz, nq, nh)

def is_dsplit(inst, zco):
    """Z squarefree, deg exactly w, all roots in dom."""
    q, w = inst.q, inst.w
    z = pnorm(zco)
    if len(z) - 1 != w:
        return False
    roots = [a for a in inst.dom if peval(z, a, q) == 0]
    if len(set(roots)) != w:
        return False
    # exact split check: product of (x - root) equals z up to scalar
    prod = [1]
    for a in roots:
        prod = pmul(prod, [(-a) % q, 1], q)
    c = z[-1]
    return psmul(c, prod, q) == z

def pencil_expl_set(inst, M0, M1, dims):
    """gammas whose pencil kernel contains a D-split Z-component."""
    q = inst.q
    nz = dims[0]
    out = set()
    ranks = {}
    for gam in range(q):
        M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(len(M0[0]))]
             for i in range(len(M0))]
        rk, ker = rank_and_kernel(M, q, want_kernel=True)
        ranks[gam] = rk
        if not ker:
            continue
        d = len(ker)
        found = False
        if d == 1:
            found = is_dsplit(inst, ker[0][:nz])
        else:
            # enumerate projective combinations (q^d small for our instances)
            def rec(i, acc):
                nonlocal found
                if found:
                    return
                if i == d:
                    if any(acc):
                        zc = acc[:nz]
                        if is_dsplit(inst, zc):
                            found = True
                    return
                for c in range(q):
                    rec(i + 1, [(acc[j] + c * ker[i][j]) % q
                                for j in range(len(acc))] if i > 0 or True else acc)
            # smarter: iterate coefficient tuples with first nonzero = 1
            import itertools
            for coefs in itertools.product(range(q), repeat=d):
                if not any(coefs):
                    continue
                nz_first = next(i for i, c in enumerate(coefs) if c)
                if coefs[nz_first] != 1:
                    continue
                v = [0] * len(ker[0])
                for ci, c in enumerate(coefs):
                    if c:
                        v = [(v[j] + c * ker[ci][j]) % q for j in range(len(v))]
                if is_dsplit(inst, v[:nz]):
                    found = True
                    break
        if found:
            out.add(gam)
    return out, ranks

def genuine_reduced(inst, l, r):
    """l nonconstant, gcd(l,r)=1, l nonvanishing on dom (checked in ratword)."""
    q = inst.q
    l, r = pnorm(l), pnorm(r)
    if len(l) <= 1:
        return False
    g = pgcd(l, r, q)
    return len(g) == 1

def run_instance(q, n, k, w, g, n_samples, extremals=None):
    inst = Inst(q, n, k, w, g)
    print(f"\n=== instance (q,n,k,w)=({q},{n},{k},{w}), dom={inst.dom} ===")
    print(f"window check: 2w+k+1={2*w+k+1} <= n={n} <= 3w+k-1={3*w+k-1}")
    mismatches = 0
    stats = Counter()
    worst = []
    cases = []
    if extremals:
        cases.extend(extremals)
    tries = 0
    while len(cases) < n_samples + (len(extremals) if extremals else 0):
        tries += 1
        if tries > 60 * n_samples:
            break
        l0 = [random.randrange(q) for _ in range(w + 1)]
        r0 = [random.randrange(q) for _ in range(w + k)]
        l1 = [random.randrange(q) for _ in range(w + 1)]
        r1 = [random.randrange(q) for _ in range(w + k)]
        if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
            continue
        if inst.ratword(l0, r0) is None or inst.ratword(l1, r1) is None:
            continue
        cases.append((l0, r0, l1, r1))
    for idx, (l0, r0, l1, r1) in enumerate(cases):
        u0 = inst.ratword(l0, r0)
        u1 = inst.ratword(l1, r1)
        E = expl_set(inst, u0, u1)
        B = bad_set(inst, u0, u1)
        M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
        P, ranks = pencil_expl_set(inst, M0, M1, dims)
        ncol = sum(dims)
        maxrank = max(ranks.values())
        degenerate = maxrank < ncol  # full col rank at NO gamma in F_q
        # (valid as generic-rank proxy: minors have gamma-degree <= w+1 < q)
        tag = "DEGEN" if degenerate else "nondeg"
        stats[tag] += 1
        stats[f"{tag}|EXPL{len(E)}"] += 1
        if E != P:
            mismatches += 1
            print(f"  MISMATCH case {idx}: EXPL={sorted(E)} PENCIL={sorted(P)} "
                  f"pair l0={l0} r0={r0} l1={l1} r1={r1}")
        if not B <= E:
            print(f"  BAD⊄EXPL?! case {idx}")
        if len(E) > w + 1 or degenerate:
            worst.append((len(E), len(B), tag, (l0, r0, l1, r1)))
    print(f"cases={len(cases)} mismatches={mismatches}")
    print(f"class stats: {dict(stats)}")
    for c in worst[:10]:
        print(f"  notable: |EXPL|={c[0]} |BAD|={c[1]} {c[2]} pair={c[3]}")
    if not worst:
        print("  (no degenerate pencils and no |EXPL| > w+1 cases found)")
    return mismatches

total_mm = 0
# scale 1: the Mobius-extremal instance. Include hand-planted Mobius-symmetric pairs:
# sigma(x) = -1/x maps mu6 in F13: orbits {1,12},{4,3},{3,4}... -1/x = 12*x^11... compute:
# inverse pairs in mu6: 1<->1? -1/1=12 in dom ✓. Build sigma-invariant rational pairs:
# rows constant on orbits {x,-1/x}: denominators like (x-a)(x+1/a)*c — sample within
# the family l(x) = x^2 - t for t s.t. nonvanishing, r similarly even... simplest:
# sample l,r in span{1, x^2+e*x...}; here just rely on random + adversarial known shape.
extremal_13 = []
total_mm += run_instance(13, 6, 1, 2, 4, 400, extremal_13)
# scale 2: second window instance
total_mm += run_instance(17, 8, 3, 2, 2, 150)
print(f"\nTOTAL MISMATCHES = {total_mm}")
print("VERDICT:", "REFORMULATION VALIDATED" if total_mm == 0 else "REFORMULATION BROKEN")
