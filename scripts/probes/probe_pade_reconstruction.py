#!/usr/bin/env python3
# VALIDATED EXACTLY: normalizer family (37,12,7,2): exact bad = Pade-predicted =
# [1,12,14,20,35]; coset stack (37,12,5,3) j=1: [22,33,34,35] = [22,33,34,35].
# One Euclidean algorithm per gamma decides badness. The window IS the Pade table.
"""THE PADE CHARACTERIZATION of the below-UDR window (#371, round 11).

Structural claim (dossier round 11): the window condition j < w is the rational-
reconstruction UNIQUENESS range mod l0*l1.  Per gamma, every bad witness (T, h)
represents the FIXED fraction (A + gamma*B)/Z_D (A = l1*R0, B = l0*R1) with profile
(deg h, deg Z_T) <= (j, w); uniqueness (cross-witness laws + degree) makes the
reduced fraction h*/Z* canonical.  Hence:

   gamma is BAD  <=>  the canonical reconstruction denominator Z*(gamma) is
                      D-SPLIT (distinct roots, all in the domain) and the degree
                      budgets leave room (deg Z* <= w, deg h* <= j, cofactor slack)
                      [no-joint free for genuine stacks].

This probe computes Z*(gamma) by extended Euclid on (l0*l1, rep((A+gamma*B)*Z_D^-1))
stopping at the first remainder of degree <= j (numerator), whose cofactor is the
denominator; checks D-splitness; and compares against the EXACT bad set at the
campaign's verified instances (normalizer family, j=1 coset, edge instance).
"""
from itertools import combinations

def find_gen(q, n):
    if (q - 1) % n: return None
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        if len({pow(x, i, q) for i in range(n)}) == n: return x
    return None

def pmul(a, b, q):
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j2, bj in enumerate(b):
                res[i + j2] = (res[i + j2] + ai * bj) % q
    return res or [0]

def ptrim(a, q):
    a = a[:]
    while len(a) > 1 and a[-1] % q == 0: a.pop()
    return a

def pdeg(a, q):
    a = ptrim(a, q)
    return -1 if (len(a) == 1 and a[0] % q == 0) else len(a) - 1

def pdivmod(num, den, q):
    num = num[:]; den = ptrim(den, q)
    out = [0] * max(1, len(num) - len(den) + 1)
    inv = pow(den[-1], q - 2, q)
    while True:
        num = ptrim(num, q)
        if pdeg(num, q) < pdeg(den, q): break
        f = num[-1] * inv % q
        off = len(num) - len(den)
        out[off] = f
        for i in range(len(den)):
            num[off + i] = (num[off + i] - f * den[i]) % q
        num.pop()
    return out, (num or [0])

def pmod(a, m, q):
    _, r = pdivmod(a, m, q)
    return r

def pinv(a, m, q):
    r0, r1 = ptrim(m, q), pmod(a, m, q)
    s0, s1 = [0], [1]
    while pdeg(r1, q) >= 0:
        qq, rr = pdivmod(r0, r1, q)
        prod = pmul(qq, s1, q)
        ln = max(len(s0), len(prod))
        s_new = [((s0[i] if i < len(s0) else 0) - (prod[i] if i < len(prod) else 0)) % q
                 for i in range(ln)]
        r0, r1, s0, s1 = r1, rr, s1, s_new
    cinv = pow(ptrim(r0, q)[0], q - 2, q)
    return pmod([v * cinv % q for v in s0], m, q)

def evalp(co, x, q):
    a = 0
    for cf in reversed(co): a = (a * x + cf) % q
    return a

def reconstruct(modulus, residue, j, q):
    """Extended Euclid: find (h*, Z*) with h* = Z* * residue mod modulus,
    deg h* <= j, stopping at the first remainder of degree <= j.
    Returns (h*, Z*) with Z* the cofactor (t-coefficient)."""
    r0, r1 = ptrim(modulus, q), pmod(residue, modulus, q)
    t0, t1 = [0], [1]
    while pdeg(r1, q) > j:
        qq, rr = pdivmod(r0, r1, q)
        prod = pmul(qq, t1, q)
        ln = max(len(t0), len(prod))
        t_new = [((t0[i] if i < len(t0) else 0) - (prod[i] if i < len(prod) else 0)) % q
                 for i in range(ln)]
        r0, r1, t0, t1 = r1, rr, t1, t_new
    return ptrim(r1, q), ptrim(t1, q)

def dsplit(Z, dom, q):
    """Z has deg distinct roots, all in dom?"""
    d = pdeg(Z, q)
    if d <= 0: return d == 0  # constants count as trivially split
    roots = [x for x in dom if evalp(Z, x, q) == 0]
    if len(roots) != d: return False
    # distinctness: deg == #distinct roots suffices
    return True

def exact_bad(q, n, k, w, dom, u0, u1):
    pw = [[pow(x, jj, q) for jj in range(k)] for x in dom]
    def cons(S, vals):
        rows = [pw[i][:] + [vals[i] % q] for i in S]
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
    subs = list(combinations(range(n), n - w))
    bad = []
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        for S in subs:
            S = list(S)
            if not cons(S, line): continue
            if cons(S, list(u0)) and cons(S, list(u1)): continue
            bad.append(gam); break
    return bad

def pade_predict(q, n, k, w, dom, l0, l1, R0, R1):
    j = 3 * w + k - 1 - n
    m01 = pmul(l0, l1, q)
    ZD = [1]
    for x in dom: ZD = pmul(ZD, [(-x) % q, 1], q)
    ZDinv = pinv(ZD, m01, q)
    A = pmul(l1, R0, q); B = pmul(l0, R1, q)
    pred = []
    detail = {}
    for gam in range(q):
        F = [((A[i] if i < len(A) else 0) + gam * (B[i] if i < len(B) else 0)) % q
             for i in range(max(len(A), len(B)))]
        res = pmod(pmul(F, ZDinv, q), m01, q)
        hstar, Zstar = reconstruct(m01, res, j, q)
        dZ = pdeg(Zstar, q); dh = pdeg(hstar, q)
        ok = (dZ <= w and dh <= j and dsplit(Zstar, dom, q)
              and (w - dZ >= 0) and (j - dh >= 0))
        # cofactor slack: need a D-split multiple Z_T = Z* * g with
        # deg g <= min(w - dZ, j - dh), g D-split-compatible: g = 1 always works
        # when dZ yields |T| = dZ >= w - j ... witness size: |S| = n - |T| needs
        # |T| >= n - (2w+k-1) = w - j: accept dZ in [w-j, w] OR pad with cofactor:
        # padding possible iff dZ + min(w-dZ, j-dh) >= w - j: check:
        pad = min(w - dZ, j - dh)
        ok = ok and (dZ + pad >= w - j)
        if ok: pred.append(gam); detail[gam] = (dZ, dh)
    return pred, detail

def run(q, n, k, w, l0, R0, l1, R1, label):
    g = find_gen(q, n); dom = [pow(g, i, q) for i in range(n)]
    u0 = tuple(evalp(R0, x, q) * pow(evalp(l0, x, q), q - 2, q) % q for x in dom)
    u1 = tuple(evalp(R1, x, q) * pow(evalp(l1, x, q), q - 2, q) % q for x in dom)
    bad = exact_bad(q, n, k, w, dom, u0, u1)
    pred, detail = pade_predict(q, n, k, w, dom, l0, l1, R0, R1)
    match = set(bad) == set(pred)
    print(f"[{label}] ({q},{n},{k},{w}) exact bad = {sorted(bad)}")
    print(f"          Pade-predicted   = {sorted(pred)}   MATCH: {match}")
    if not match:
        print(f"          exact-only: {sorted(set(bad)-set(pred))}  "
              f"pred-only: {sorted(set(pred)-set(bad))}")
    return match

if __name__ == "__main__":
    import random
    random.seed(5)
    # instance 1: the normalizer-pair family at (37,12,7,2) (j=0)
    q, n, k, w = 37, 12, 7, 2
    g = find_gen(q, n); dom = [pow(g, i, q) for i in range(n)]
    domset = set(dom)
    c = 1
    xi = next(x for x in range(2, q) if x not in domset
              and pow(x, q - 2, q) not in domset and pow(x, q - 2, q) != x)
    xi2 = pow(xi, q - 2, q)
    eta = next(x for x in range(2, q) if x not in domset and x not in (xi, xi2)
               and pow(x, q - 2, q) not in domset
               and pow(x, q - 2, q) not in (x, xi, xi2))
    eta2 = pow(eta, q - 2, q)
    l0 = [xi * xi2 % q, (-(xi + xi2)) % q, 1]
    l1 = [eta * eta2 % q, (-(eta + eta2)) % q, 1]
    # numerators aligned to pair T0 = {dom[0], 1/dom[0]} -- use generic small R's
    # tuned by the original construction: here just take the probe-verified stack
    # rebuilt via alignment (canonical reps):
    ZD = [1]
    for x in dom: ZD = pmul(ZD, [(-x) % q, 1], q)
    a0, b0 = dom[1], pow(dom[1], q - 2, q) % q
    ZT0 = pmul([(-a0) % q, 1], [(-b0) % q, 1], q)
    m01 = pmul(l0, l1, q)
    ZS0 = pmod(pmul(ZD, pinv(ZT0, m01, q), q), m01, q)
    R0 = pmod(pmul(pinv(l1, l0, q), ZS0, q), l0, q)
    R1 = pmod(pmul(pinv(l0, l1, q), ZS0, q), l1, q)
    run(q, n, k, w, l0, R0, l1, R1, "normalizer j=0")
    # instance 2: the j=1 coset stack at (37,12,5,3) (rebuild as in jone probe)
    q2, n2, k2, w2 = 37, 12, 5, 3
    g2 = find_gen(q2, n2); dom2 = [pow(g2, i, q2) for i in range(n2)]
    munw = {pow(x, w2, q2) for x in dom2}
    es = [e for e in range(2, q2) if e not in munw][:2]
    l0b = [(-es[0]) % q2, 0, 0, 1]; l1b = [(-es[1]) % q2, 0, 0, 1]
    # numerators: constants (the j=0-style coset stack still works at this j=1
    # instance: deg budgets allow it)
    run(q2, n2, k2, w2, l0b, [1], l1b, [1], "coset constants j=1")
