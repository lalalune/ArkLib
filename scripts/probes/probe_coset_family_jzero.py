#!/usr/bin/env python3
"""The mu_w-coset family at the j=0 slice: verifying SHARPNESS of the packing law.

The window packing law (WindowPackingLaw.lean) gives #bad <= C(n,1)/C(w,1) = n/w at
j = 0 (n = 3w+k-1) for genuine coprime rational stacks.  The coset family
(l_i = X^w - e_i, T = t*mu_w, Z_T = X^w - t^w == e_i - t^w const mod l_i) predicts
EXACTLY n/w distinct bad scalars (gamma(T) is a Mobius function of t^w).

Pre-registered: at (37,12,1,4) [n/w = 3] and (61,20,6,5) [n/w = 4] the construction
achieves the packing bound (minus possible 1-scalar degeneracies).
"""
from itertools import combinations

def find_gen(q, n):
    if (q - 1) % n: return None
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        if len({pow(x, i, q) for i in range(n)}) == n: return x
    return None

def evalp(co, x, q):
    a = 0
    for cf in reversed(co): a = (a * x + cf) % q
    return a

def make_solver(q, n, k, dom):
    pw = [[pow(x, j, q) for j in range(k)] for x in dom]
    def consistent(idxs, vals):
        rows = [pw[i][:] + [vals[i] % q] for i in idxs]
        m_, r = len(rows), 0
        for c in range(k):
            p = next((i for i in range(r, m_) if rows[i][c] % q), None)
            if p is None: continue
            rows[r], rows[p] = rows[p], rows[r]
            inv = pow(rows[r][c], q - 2, q)
            rows[r] = [(v * inv) % q for v in rows[r]]
            for i in range(m_):
                if i != r and rows[i][c] % q:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
            r += 1
        return not any(rows[i][k] % q for i in range(r, m_))
    return consistent

def bad_count(q, n, k, w, dom, u0, u1):
    consistent = make_solver(q, n, k, dom)
    tmin = n - w
    subs = list(combinations(range(n), tmin))
    bads = []
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        isbad = False
        for S in subs:
            S = list(S)
            if not consistent(S, line): continue
            if consistent(S, list(u0)) and consistent(S, list(u1)): continue
            isbad = True; break
        if isbad: bads.append(gam)
    return bads

def coset_family(q, n, k, w):
    assert n == 3 * w + k - 1 and n % w == 0
    g = find_gen(q, n)
    if g is None: return None
    dom = [pow(g, i, q) for i in range(n)]
    # mu_{n/w} = (mu_n)^w; pick e0, e1 NOT in mu_{n/w} so X^w - e has no domain roots
    munw = {pow(x, w, q) for x in dom}
    es = [e for e in range(2, q) if e not in munw]
    if len(es) < 2: return None
    e0, e1 = es[0], es[1]
    l0 = [(-e0) % q] + [0] * (w - 1) + [1]
    l1 = [(-e1) % q] + [0] * (w - 1) + [1]
    # alignment: pick base coset T0 = mu_w itself (t0 = 1): Z_T0 = X^w - 1
    # need R0 with l1*R0 == (X^n-1)/Z_T0 mod l0; everything is constant mod l0:
    #   X^n-1 == e0^{n/w} - 1;  Z_T0 == e0 - 1;  l1 == e0 - e1 (all constants!)
    # so R0 := const = (e0^{n/w}-1) / ((e0-1)(e0-e1)) works (deg 0 <= w+k-1).
    c0 = (pow(e0, n // w, q) - 1) * pow((e0 - 1) * (e0 - e1) % q, q - 2, q) % q
    c1 = (pow(e1, n // w, q) - 1) * pow((e1 - 1) * (e1 - e0) % q, q - 2, q) % q
    R0 = [c0]; R1 = [c1]
    # genuineness: l ∤ R trivially (R nonzero constant, deg l = w >= 1) -- but note
    # R constant means u_i = c_i / l_i(x): still genuinely rational.
    u0 = tuple(c0 * pow(evalp(l0, x, q), q - 2, q) % q for x in dom)
    u1 = tuple(c1 * pow(evalp(l1, x, q), q - 2, q) % q for x in dom)
    bads = bad_count(q, n, k, w, dom, u0, u1)
    print(f"({q},{n},{k},{w}) coset family: bad = {len(bads)}  "
          f"packing bound n/w = {n // w}  gammas = {bads}")
    return len(bads)

coset_family(37, 12, 1, 4)
coset_family(61, 20, 6, 5)
coset_family(97, 16, 5, 4)
