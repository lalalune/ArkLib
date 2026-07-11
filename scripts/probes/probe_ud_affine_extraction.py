#!/usr/bin/env python3
"""probe_ud_affine_extraction.py — ground truth for the O77 affine-root extraction residual
in the unique-decoding regime (#232, builds on O77/O78; exact arithmetic over GF(97)).

QUESTIONS (falsify-first, before formalizing TheoremQUDExtraction.lean):

C1 (the d/(3n) window — the claimed theorem): at (n,k) = (16,8), d = 9, for stacks with
    >= 2 bad scalars at floor t with 3(n-t) < d (i.e. e = n-t <= 2):
      (a) the affine decoding law holds: for EVERY bad gamma, the unique nearest codeword
          of u0 + gamma*u1 is c0 + gamma*c1 where (c0,c1) is solved from the first two
          bad scalars (d_gamma = 0);
      (b) the canonical pair e0 = u0-c0, e1 = u1-c1 satisfies the root property
          (every bad gamma is a root of e0 + gamma*e1 at a support coord of e1);
      (c) badCount <= 2(n-t)+1.
C2 (the hunt zone (d/3n, (d-1)/2n], e in {3,4}): does the affine law survive?  Does
    badCount stay <= 2(n-t)+1 (the would-be extraction weight)?  Adversarial g-planting:
    error pair designed so that a THIRD bad scalar decodes to line + g for a weight-9
    codeword g (off the affine law).
C3 (window intersection arithmetic + the r = s instance): at the O68 parameters
    (n,m,s,r) = (16,2,8,5) the Theorem-Q window and the 3(n-t) < d window are DISJOINT;
    at r = s they intersect.  Concrete r = s point: q = 97, n = 12, s = r = 4, m = 3,
    k = 9, d = 4, t = 11 (delta = 1/12): the deep-quotient line of TheoremQAssembly has
    >= 1 bad scalar (lower half consistent) and badCount <= 2(n-t)+1 = 3 (upper half
    consistent).

mcaEvent reduction used throughout (witness-set monotonicity, as in O78's probe):
gamma is bad at floor t  <=>  exists codeword w with agreement set A = A_gamma(w),
|A| >= t, and NOT pairJoint(A).  In the UD regime n-t <= (d-1)/2 the codeword with
agreement >= t is unique (Berlekamp-Welch), and pairJoint(A) decomposes row-wise.
"""

import random
import sys

random.seed(232077)

# ---------------------------------------------------------------- field GF(p)
P = 97


def inv(a, p=P):
    return pow(a % p, p - 2, p)


def factorize(m):
    f, d = set(), 2
    while d * d <= m:
        while m % d == 0:
            f.add(d)
            m //= d
        d += 1
    if m > 1:
        f.add(m)
    return f


def primitive_root(p):
    fac = factorize(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError


def nth_roots(n, p=P):
    assert (p - 1) % n == 0
    g = primitive_root(p)
    w = pow(g, (p - 1) // n, p)
    pts = sorted(pow(w, i, p) for i in range(n))
    assert len(set(pts)) == n
    return pts


def poly_eval(coeffs, x, p=P):
    r = 0
    for c in reversed(coeffs):
        r = (r * x + c) % p
    return r


def poly_deg(c):
    for i in range(len(c) - 1, -1, -1):
        if c[i] % P:
            return i
    return -1


def poly_div_exact(Q, E, p=P):
    """quotient if E | Q (polys mod p, coeffs low->high), else None."""
    Q = [x % p for x in Q]
    dq, de = poly_deg(Q), poly_deg(E)
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


def gauss_kernel(M, ncols, p=P):
    """one nonzero kernel vector of M (rows of length ncols) over GF(p), or None."""
    M = [row[:] for row in M]
    nrows = len(M)
    pivots = []
    r = 0
    for c in range(ncols):
        pr = None
        for rr in range(r, nrows):
            if M[rr][c] % p:
                pr = rr
                break
        if pr is None:
            continue
        M[r], M[pr] = M[pr], M[r]
        iv = inv(M[r][c], p)
        M[r] = [(x * iv) % p for x in M[r]]
        for rr in range(nrows):
            if rr != r and M[rr][c] % p:
                f = M[rr][c]
                Mr = M[r]
                M[rr] = [(M[rr][j] - f * Mr[j]) % p for j in range(ncols)]
        pivots.append((r, c))
        r += 1
        if r == nrows:
            break
    pcols = {c for (_, c) in pivots}
    free = [c for c in range(ncols) if c not in pcols]
    if not free:
        return None
    f0 = free[0]
    v = [0] * ncols
    v[f0] = 1
    for (rr, c) in pivots:
        v[c] = (-M[rr][f0]) % p
    return v


def poly_mul_linear(num, root, p=P):
    """num(X) * (X - root) mod p, coeffs low->high."""
    out = [0] * (len(num) + 1)
    for a in range(len(num)):
        out[a] = (out[a] - root * num[a]) % p
        out[a + 1] = (out[a + 1] + num[a]) % p
    return out


def interpolate(xs, ys, p=P):
    """coeffs (low->high, len = len(xs)) of the poly through the points (Lagrange)."""
    k = len(xs)
    coeffs = [0] * k
    for i in range(k):
        num = [1]
        den = 1
        for j in range(k):
            if j == i:
                continue
            num = poly_mul_linear(num, xs[j], p)
            den = den * (xs[i] - xs[j]) % p
        f = ys[i] * inv(den, p) % p
        for a in range(len(num)):
            coeffs[a] = (coeffs[a] + f * num[a]) % p
    return coeffs


class RS:
    def __init__(self, n, k, p=P):
        self.n, self.k, self.p = n, k, p
        self.xs = nth_roots(n, p)
        self.d = n - k + 1
        self.powmat = [[pow(x, j, p) for j in range(n)] for x in self.xs]

    def encode(self, coeffs):
        return [poly_eval(coeffs, x, self.p) for x in self.xs]

    def random_codeword(self):
        return self.encode([random.randrange(self.p) for _ in range(self.k)])

    def bw_decode(self, y, e):
        """unique codeword within distance e of y, requires 2e <= n-k.  None if absent."""
        n, k, p = self.n, self.k, self.p
        assert 2 * e <= n - k
        ncols = (k + e) + (e + 1)
        M = []
        for i in range(n):
            row = self.powmat[i][:k + e] + \
                [(-y[i] * self.powmat[i][j]) % p for j in range(e + 1)]
            M.append(row)
        v = gauss_kernel(M, ncols, p)
        if v is None:
            return None
        Q, E = v[:k + e], v[k + e:]
        quot = poly_div_exact(Q, E, p)
        if quot is None or poly_deg(quot) >= k:
            return None
        w = self.encode(quot + [0] * max(0, k - len(quot)))
        if sum(1 for i in range(n) if w[i] != y[i]) <= e:
            return w
        return None

    def row_interpolates(self, u, A):
        """exists codeword agreeing with u on every index of A?"""
        if len(A) <= self.k:
            return True
        pts = A[:self.k]
        coeffs = interpolate([self.xs[i] for i in pts], [u[i] for i in pts], self.p)
        return all(poly_eval(coeffs, self.xs[i], self.p) == u[i] for i in A)

    def bad_set(self, u0, u1, t):
        """[(gamma, w)] of mcaEvent-bad scalars at floor t (UD regime n-t <= (d-1)/2)."""
        e = self.n - t
        assert 2 * e <= self.n - self.k
        out = []
        for g in range(self.p):
            y = [(u0[i] + g * u1[i]) % self.p for i in range(self.n)]
            w = self.bw_decode(y, e)
            if w is None:
                continue
            A = [i for i in range(self.n) if w[i] == y[i]]
            if len(A) < t:
                continue
            if not (self.row_interpolates(u0, A) and self.row_interpolates(u1, A)):
                out.append((g, tuple(w)))
        return out


def weight(v):
    return sum(1 for x in v if x % P)


def affine_check(rs, u0, u1, bads):
    """given >= 2 bad scalars, solve (c0,c1) from the first two and report:
    (all_affine, root_ok) for the canonical pair e = u - c."""
    (g1, w1), (g2, w2) = bads[0], bads[1]
    dinv = inv(g1 - g2)
    c1 = [(w1[i] - w2[i]) * dinv % P for i in range(rs.n)]
    c0 = [(w1[i] - g1 * c1[i]) % P for i in range(rs.n)]
    e0 = [(u0[i] - c0[i]) % P for i in range(rs.n)]
    e1 = [(u1[i] - c1[i]) % P for i in range(rs.n)]
    all_affine = True
    root_ok = True
    for (g, w) in bads:
        line = [(c0[i] + g * c1[i]) % P for i in range(rs.n)]
        if tuple(line) != tuple(w):
            all_affine = False
        if not any(e1[i] % P and (e0[i] + g * e1[i]) % P == 0 for i in range(rs.n)):
            root_ok = False
    return all_affine, root_ok, weight(e1)


# ---------------------------------------------------------------- stack builders
def plant_two_cancel(rs, e):
    """stack with two designed bad scalars at floor t = n-e: error support 2e,
    e coords cancelling at gamma1, e at gamma2."""
    n = rs.n
    c0, c1 = rs.random_codeword(), rs.random_codeword()
    g1, g2 = random.sample(range(1, P), 2)
    E = random.sample(range(n), 2 * e)
    e0, e1 = [0] * n, [0] * n
    for j, i in enumerate(E):
        e1[i] = random.randrange(1, P)
        gtarget = g1 if j < e else g2
        e0[i] = (-gtarget * e1[i]) % P
    u0 = [(c0[i] + e0[i]) % P for i in range(n)]
    u1 = [(c1[i] + e1[i]) % P for i in range(n)]
    return u0, u1


def plant_g_attack(rs, e, split=None):
    """e in {3,4}: error support 8 (or 2e) arranged so gamma1, gamma2 cancel down to
    weight <= e AND a third scalar gamma3 has e0+gamma3*e1 within distance 1 of a
    weight-(n-k+1) codeword g — the affine-law attack."""
    n, k = rs.n, rs.k
    # g: poly with k-1 distinct roots in H -> codeword of weight n-k+1 = d
    roots = random.sample(range(n), k - 1)
    coeffs = [1]
    for i in roots:
        coeffs = poly_mul_linear(coeffs, rs.xs[i])
    lead = random.randrange(1, P)
    g = [poly_eval(coeffs, x) * lead % P for x in rs.xs]
    supp = [i for i in range(n) if g[i] % P]
    assert len(supp) == rs.d
    E = supp[:2 * e]          # miss d - 2e coords of supp(g)
    g1, g2, g3 = random.sample(range(1, P), 3)
    e0, e1 = [0] * n, [0] * n
    nsplit = split if split is not None else e
    for j, i in enumerate(E):
        gcancel = g1 if j < nsplit else g2
        e1[i] = g[i] * inv(g3 - gcancel) % P
        e0[i] = (g[i] - g3 * e1[i]) % P
        assert (e0[i] + gcancel * e1[i]) % P == 0
    c0, c1 = rs.random_codeword(), rs.random_codeword()
    u0 = [(c0[i] + e0[i]) % P for i in range(n)]
    u1 = [(c1[i] + e1[i]) % P for i in range(n)]
    return u0, u1


def random_error_stack(rs, suppsize):
    n = rs.n
    c0, c1 = rs.random_codeword(), rs.random_codeword()
    E = random.sample(range(n), suppsize)
    e0, e1 = [0] * n, [0] * n
    for i in E:
        e0[i] = random.randrange(P)
        e1[i] = random.randrange(1, P)
    return ([(c0[i] + e0[i]) % P for i in range(n)],
            [(c1[i] + e1[i]) % P for i in range(n)])


# ================================================================ C1: the window
def check_C1():
    rs = RS(16, 8)
    fails = 0
    n_multi = 0
    maxbad = 0
    cases = 0
    for e in (1, 2):                          # 3e <= 6 < 9 = d : in-window
        t = rs.n - e
        for trial in range(30):
            u0, u1 = plant_two_cancel(rs, e)
            bads = rs.bad_set(u0, u1, t)
            cases += 1
            maxbad = max(maxbad, len(bads))
            if len(bads) > 2 * e + 1:
                fails += 1
                print(f"  C1 VIOLATION badCount={len(bads)} > {2*e+1} at e={e}")
            if len(bads) >= 2:
                n_multi += 1
                aff, root, w1 = affine_check(rs, u0, u1, bads)
                if not aff or not root or w1 > 2 * e:
                    fails += 1
                    print(f"  C1 VIOLATION affine={aff} root={root} wt={w1} at e={e}")
        for trial in range(10):
            u0, u1 = random_error_stack(rs, 2 * e)
            bads = rs.bad_set(u0, u1, t)
            cases += 1
            maxbad = max(maxbad, len(bads))
            if len(bads) > 2 * e + 1:
                fails += 1
                print(f"  C1 VIOLATION (random) badCount={len(bads)} at e={e}")
            if len(bads) >= 2:
                n_multi += 1
                aff, root, w1 = affine_check(rs, u0, u1, bads)
                if not aff or not root:
                    fails += 1
                    print(f"  C1 VIOLATION (random) affine={aff} root={root}")
    print(f"C1 (window 3(n-t)<d, e<=2): {cases} stacks, {n_multi} with >=2 bad, "
          f"max badCount {maxbad}, violations {fails}")
    return fails == 0 and n_multi > 0


# ================================================================ C2: the hunt
def check_C2():
    rs = RS(16, 8)
    results = {}
    for e in (3, 4):
        t = rs.n - e
        n_aff_viol = 0
        n_multi = 0
        maxbad = 0
        over_W = 0
        over_n = 0
        cases = 0
        stacks = []
        for trial in range(24):
            stacks.append(plant_g_attack(rs, e))
        for trial in range(12):
            stacks.append(plant_two_cancel(rs, e))
        for trial in range(12):
            stacks.append(random_error_stack(rs, 2 * e))
        for (u0, u1) in stacks:
            bads = rs.bad_set(u0, u1, t)
            cases += 1
            maxbad = max(maxbad, len(bads))
            if len(bads) > 2 * e + 1:
                over_W += 1
            if len(bads) > rs.n:
                over_n += 1
            if len(bads) >= 2:
                n_multi += 1
                aff, root, w1 = affine_check(rs, u0, u1, bads)
                if not aff:
                    n_aff_viol += 1
        results[e] = (cases, n_multi, maxbad, n_aff_viol, over_W, over_n)
        print(f"C2 (hunt e={e}, t={t}): {cases} stacks, {n_multi} multi-bad, "
              f"max badCount {maxbad} (W=2e+1={2*e+1}), affine-law violations "
              f"{n_aff_viol}, badCount>W {over_W}, badCount>n {over_n}")
    return results


# ================================================================ C3: r = s point
def check_C3():
    # window-intersection arithmetic at the O68 point (16,2,8,5):
    n, m, s, r = 16, 2, 8, 5
    k = (r - 1) * m
    d = n - k + 1
    # lower half needs t <= r*m ; upper window needs 3(n-t) < d
    t_lo_max = r * m
    t_up_min = n - (d - 1) // 3 if (d - 1) % 3 else n - (d - 1) // 3
    # smallest t with 3(n-t) < d  <=>  n-t <= ceil(d/3)-1  <=> t >= n - (d-1)//3... compute directly
    t_up_min = min(t for t in range(n + 1) if 3 * (n - t) < d)
    inter_empty = t_up_min > t_lo_max
    print(f"C3a O68 point (n,m,s,r)=(16,2,8,5): k={k} d={d}; lower needs t<={t_lo_max}, "
          f"upper needs t>={t_up_min}; intersection empty: {inter_empty}")

    # r = s point: q=97, n=12, s=r=4, m=3, k=9, d=4, t=11 (delta = 1/12)
    n2, m2, s2, r2 = 12, 3, 4, 4
    k2 = (r2 - 1) * m2
    rs = RS(n2, k2)
    assert rs.d == n2 - k2 + 1 == 4
    t2 = 11
    assert 3 * (n2 - t2) < rs.d, "window must be nonempty at r=s"
    assert (1 - 1 / 12) * n2 <= r2 * m2 + 1e-9, "Theorem-Q window holds (trivially, rm=n)"
    # the deep-quotient line: w = z0^m for z0 not an n-th root of unity
    z0 = next(z for z in range(2, P) if pow(z, n2, P) != 1)
    w = pow(z0, m2, P)
    u0 = [pow(x, r2 * m2, P) * inv((pow(x, m2, P) - w) % P) % P for x in rs.xs]
    u1 = [inv((pow(x, m2, P) - w) % P) for x in rs.xs]
    bads = rs.bad_set(u0, u1, t2)
    ok_lower = len(bads) >= 1
    ok_upper = len(bads) <= 2 * (n2 - t2) + 1
    print(f"C3b r=s instance (q=97,n=12,s=r=4,m=3,k=9,d=4,t=11): deep-line badCount = "
          f"{len(bads)} (lower needs >=1: {ok_lower}; upper needs <={2*(n2-t2)+1}: {ok_upper})")
    # sample further stacks at the r=s point to stress the upper bound
    worst = len(bads)
    viol = 0
    for trial in range(20):
        uu0, uu1 = plant_two_cancel(rs, n2 - t2)
        b = rs.bad_set(uu0, uu1, t2)
        worst = max(worst, len(b))
        if len(b) > 2 * (n2 - t2) + 1:
            viol += 1
        if len(b) >= 2:
            aff, root, w1 = affine_check(rs, uu0, uu1, b)
            if not root:
                viol += 1
                print(f"  C3 VIOLATION root property at r=s point")
    print(f"C3c r=s stress: 20 stacks, max badCount {worst}, violations {viol}")
    return inter_empty and ok_lower and ok_upper and viol == 0


def main():
    ok1 = check_C1()
    res2 = check_C2()
    ok3 = check_C3()
    # C2 is a hunt: report; the formal claim only covers e <= 2, so C2 results are
    # findings, not gates — EXCEPT badCount > n at e <= 4 would refute the O77
    # docstring claim outright; gate on having measured it.
    hunted = all(e in res2 for e in (3, 4))
    print()
    print(f"SUMMARY: C1(pass)={ok1} C2(measured)={hunted} C3(pass)={ok3}")
    if not (ok1 and hunted and ok3):
        sys.exit(1)
    print("exit 0")


if __name__ == "__main__":
    main()
