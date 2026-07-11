#!/usr/bin/env python3
"""THE NORMALIZER-PAIR FAMILY: explicit candidate refutation of WindowRationalBounded.

Construction (Fable round 4, derived from the CRT/circle-group reduction at j = 0,
i.e. n = 3w+k-1, the first beyond-ladder slice):

  choose c in mu_n;  l0 := (X-xi)(X-c/xi),  l1 := (X-eta)(X-c/eta)  with all four
  roots off mu_n and l0 coprime to l1.  KEY IDENTITY (coefficient check):
      (xi - a)(xi - c/a) = (xi/xi') * (xi' - a)(xi' - c/a)   for xi' = c/xi, all a,
  so EVERY involution pair {a, c/a} (a in mu_n) has the same projective class
  [Z_T mod l] in BOTH quotient rings.  Pick one pair T0 and set
      R0 := canonical rep of (l1^{-1} * (X^n-1)/Z_T0) mod l0   (deg <= 1, genuine),
      R1 := canonical rep of (l0^{-1} * (X^n-1)/Z_T0) mod l1.
  Then for every T = union of w/2 involution pairs, M := c_T * Z_{D \\ T} satisfies
  M = A mod l0 and M = gamma(T)*B mod l1 (A := l1*R0, B := l0*R1), i.e. gamma(T) is
  line-explainable with witness D \\ T.  Below UDR, genuine rational rows admit NO
  joint explanation on ANY co-w set (degree forcing), so every gamma(T) is mca-BAD.

  Predicted bad count = #distinct gamma(T) over the C(n/2, w/2) aligned T's.
  If > w+3 at any doubly-WB-solvable instance: WindowRationalBounded is REFUTED.

Verification here is INDEPENDENT of the derivation: bad scalars are recomputed from
scratch by the exact mcaEvent reduction (unique explainer + no-joint on the full
agreement set), and WB-solvability of both rows is checked by rank.
"""
from itertools import combinations

def find_gen(q, n):
    if (q - 1) % n: return None
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        xs = {pow(x, i, q) for i in range(n)}
        if len(xs) == n: return x
    return None

def polymulmod(a, b, m, q):
    # multiply two coeff lists mod (m, q); m monic
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                res[i + j] = (res[i + j] + ai * bj) % q
    # reduce mod m
    dm = len(m) - 1
    while len(res) > dm:
        f = res[-1]
        if f:
            off = len(res) - 1 - dm
            for i in range(dm + 1):
                res[off + i] = (res[off + i] - f * m[i]) % q
        res.pop()
    while len(res) < dm: res.append(0)
    return res

def polyinvmod(a, m, q):
    # inverse of a mod (m, q) via extended Euclid; m monic, gcd = 1
    def polydivmod(num, den):
        num = num[:]
        dd = len(den) - 1
        while len(den) > 1 and den[-1] % q == 0: den = den[:-1]
        inv = pow(den[-1], q - 2, q)
        quo = [0] * max(0, len(num) - len(den) + 1)
        while len(num) >= len(den) and any(v % q for v in num):
            while num and num[-1] % q == 0: num.pop()
            if len(num) < len(den): break
            f = num[-1] * inv % q
            off = len(num) - len(den)
            quo[off] = f
            for i in range(len(den)):
                num[off + i] = (num[off + i] - f * den[i]) % q
            num.pop()
        return quo, num
    r0, r1 = m[:], a[:]
    s0, s1 = [0], [1]
    while any(v % q for v in r1):
        qq, rr = polydivmod(r0, r1)
        r0, r1 = r1, rr
        # s_new = s0 - qq*s1
        prod = [0] * (len(qq) + len(s1) - 1) if qq and s1 else [0]
        for i, ai in enumerate(qq):
            if ai:
                for j, bj in enumerate(s1):
                    prod[i + j] = (prod[i + j] + ai * bj) % q
        ln = max(len(s0), len(prod))
        s_new = [( (s0[i] if i < len(s0) else 0) - (prod[i] if i < len(prod) else 0)) % q
                 for i in range(ln)]
        s0, s1 = s1, s_new
    # r0 = gcd (constant); normalize
    while r0 and r0[-1] % q == 0: r0.pop()
    assert len(r0) == 1, "not coprime"
    cinv = pow(r0[0], q - 2, q)
    res = [v * cinv % q for v in s0]
    return polymulmod(res, [1], m, q)

def evalp(co, x, q):
    a = 0
    for cf in reversed(co): a = (a * x + cf) % q
    return a

def make_tools(q, n, k, dom):
    pw = [[pow(x, j, q) for j in range(k)] for x in dom]
    def solve(idxs, vals):
        rows = [pw[i][:] + [vals[i] % q] for i in idxs]
        m_, r = len(rows), 0
        piv_cols = []
        for c in range(k):
            piv = next((i for i in range(r, m_) if rows[i][c] % q), None)
            if piv is None: continue
            rows[r], rows[piv] = rows[piv], rows[r]
            inv = pow(rows[r][c], q - 2, q)
            rows[r] = [(v * inv) % q for v in rows[r]]
            for i in range(m_):
                if i != r and rows[i][c] % q:
                    f = rows[i][c]
                    rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
            piv_cols.append(c); r += 1
        if any(rows[i][k] % q for i in range(r, m_)): return None
        co = [0] * k
        for ri, c in enumerate(piv_cols): co[c] = rows[ri][k]
        return co
    return solve

def bad_set_exact(q, n, k, w, dom, u0, u1, solve):
    tmin = n - w
    bads = []
    subs = list(combinations(range(n), tmin))
    for gam in range(q):
        line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
        expl = None
        for S in subs:
            co = solve(list(S), line)
            if co is not None:
                A = [i for i in range(n) if evalp(co, dom[i], q) == line[i]]
                if len(A) >= tmin: expl = A; break
        if expl is None: continue
        if solve(expl, u0) is None or solve(expl, u1) is None:
            bads.append(gam)
    return bads

def wbsolv(q, n, k, w, dom, u):
    rows = []
    for i in range(n):
        x = dom[i]
        row = [(pow(x, j, q) * u[i]) % q for j in range(w + 1)]
        row += [(-pow(x, j, q)) % q for j in range(w + k)]
        rows.append(row)
    m_, cols, r = len(rows), 2 * w + k + 1, 0
    for c in range(cols):
        piv = next((i for i in range(r, m_) if rows[i][c] % q), None)
        if piv is None: continue
        rows[r], rows[piv] = rows[piv], rows[r]
        inv = pow(rows[r][c], q - 2, q)
        rows[r] = [(v * inv) % q for v in rows[r]]
        for i in range(m_):
            if i != r and rows[i][c] % q:
                f = rows[i][c]
                rows[i] = [(a - f * b) % q for a, b in zip(rows[i], rows[r])]
        r += 1
    return r < cols

def construct_and_test(q, n, k, w, verbose=True):
    assert w % 2 == 0, "this construction uses unions of involution pairs"
    assert n == 3 * w + k - 1, "j = 0 slice"
    g = find_gen(q, n)
    if g is None: return None
    dom = [pow(g, i, q) for i in range(n)]
    domset = set(dom)
    # choose c in mu_n a square in mu_n s.t. involution a -> c/a is fixed-point-light;
    # any c works for alignment; prefer c with no fixed points in mu_n (c not a square
    # of an element? fixed points: a^2 = c) -- just take any c, drop fixed pairs.
    for c in dom:
        # denominators must have FULL degree w (else deg P >= k): products of w/2
        # involution-quadratics (X-x)(X-c/x), all 2*(w/2)*2 roots off-domain, distinct
        used = set()
        def next_invol_root(avoid):
            for x in range(2, q):
                cx = c * pow(x, q - 2, q) % q
                if (x in domset or cx in domset or x == 0 or cx == x
                        or x in avoid or cx in avoid):
                    continue
                return x, cx
            return None
        quads0, quads1 = [], []
        ok = True
        for _ in range(w // 2):
            r = next_invol_root(used)
            if r is None: ok = False; break
            used |= set(r); quads0.append(r)
        if ok:
            for _ in range(w // 2):
                r = next_invol_root(used)
                if r is None: ok = False; break
                used |= set(r); quads1.append(r)
        if not ok: continue
        def quadprod(quads):
            co = [1]
            for (a, b) in quads:
                co2 = [a * b % q, (-(a + b)) % q, 1]
                res = [0] * (len(co) + 2)
                for i, ai in enumerate(co):
                    for j, bj in enumerate(co2):
                        res[i + j] = (res[i + j] + ai * bj) % q
                co = res
            return co
        l0 = quadprod(quads0)
        l1 = quadprod(quads1)
        # involution pairs {a, c/a}, a in mu_n, a != c/a
        pairs = []
        seen = set()
        for a in dom:
            b = c * pow(a, q - 2, q) % q
            if a == b or a in seen or b in seen: continue
            seen |= {a, b}
            pairs.append((a, b))
        if len(pairs) < w // 2 + 1: continue
        # Z_{T0} for first T0 = first w/2 pairs
        def ZT(pairlist):
            co = [1]
            for (a, b) in pairlist:
                co2 = [a * b % q, (-(a + b)) % q, 1]
                res = [0] * (len(co) + 2)
                for i, ai in enumerate(co):
                    for j, bj in enumerate(co2):
                        res[i + j] = (res[i + j] + ai * bj) % q
                co = res
            return co
        # X^n - 1 coefficients
        Xn1 = [(-1) % q] + [0] * (n - 1) + [1]
        T0 = pairs[: w // 2]
        ZT0 = ZT(T0)
        # residues mod l0: A* = (X^n-1) * ZT0^{-1} mod l0 ; R0 = l1^{-1} A* mod l0
        Astar = polymulmod(polymulmod(Xn1, [1], l0, q), polyinvmod(ZT0, l0, q), l0, q)
        R0 = polymulmod(polyinvmod(l1, l0, q), Astar, l0, q)
        Bstar = polymulmod(polymulmod(Xn1, [1], l1, q), polyinvmod(ZT0, l1, q), l1, q)
        R1 = polymulmod(polyinvmod(l0, l1, q), Bstar, l1, q)
        if not any(R0) or not any(R1): continue
        # words
        u0 = tuple(evalp(R0, x, q) * pow(evalp(l0, x, q), q - 2, q) % q for x in dom)
        u1 = tuple(evalp(R1, x, q) * pow(evalp(l1, x, q), q - 2, q) % q for x in dom)
        # predicted gammas over all unions of w/2 involution pairs
        predicted = set()
        for Tps in combinations(pairs, w // 2):
            ZTc = ZT(list(Tps))
            ZS = polymulmod(polymulmod(Xn1, [1], l0, q), polyinvmod(ZTc, l0, q), l0, q)
            # c_T: ZS = c_T^{-1} * A mod l0 with A = l1*R0 -> c_T = A * ZS^{-1} (scalar?)
            A = polymulmod(l1, R0, l0, q)
            ratio = polymulmod(A, polyinvmod(ZS, l0, q), l0, q)
            if any(v % q for v in ratio[1:]):   # must be scalar
                continue
            cT = ratio[0]
            ZS1 = polymulmod(polymulmod(Xn1, [1], l1, q), polyinvmod(ZTc, l1, q), l1, q)
            B = polymulmod(l0, R1, l1, q)
            ratio1 = polymulmod(polymulmod([cT], ZS1, l1, q), polyinvmod(B, l1, q), l1, q)
            if any(v % q for v in ratio1[1:]):
                continue
            predicted.add(ratio1[0] % q)
        solve = make_tools(q, n, k, dom)
        bads = bad_set_exact(q, n, k, w, dom, u0, u1, solve)
        s0 = wbsolv(q, n, k, w, dom, u0); s1 = wbsolv(q, n, k, w, dom, u1)
        if verbose:
            print(f"({q},{n},{k},{w}) c={c}: pairs={len(pairs)} "
                  f"predicted gammas={len(predicted)} EXACT bad={len(bads)} "
                  f"WBsolv=({s0},{s1}) w+3={w+3}"
                  f"{'  <<< REFUTED' if len(bads) > w + 3 and s0 and s1 else ''}")
            if len(bads) > w + 3 and s0 and s1:
                print(f"   u0={u0}\n   u1={u1}\n   bad gammas={sorted(bads)}"
                      f"\n   predicted ⊆ bad: {predicted <= set(bads)}")
        return (len(bads), len(predicted), s0 and s1, u0, u1, bads)
    return None

print("== the normalizer-pair family across instances ==")
for (q, n, k, w) in [(13, 12, 7, 2), (17, 16, 11, 2), (37, 12, 7, 2),
                     (97, 12, 7, 2), (17, 8, 3, 2), (41, 8, 3, 2),
                     (13, 12, 1, 4), (17, 16, 5, 4)]:
    r = construct_and_test(q, n, k, w)
    if r is None: print(f"({q},{n},{k},{w}): construction not instantiated")

print("== refutation push: instances with off-domain room ==")
for (q, n, k, w) in [(97, 16, 11, 2), (113, 16, 11, 2), (41, 20, 15, 2),
                     (37, 12, 1, 4), (97, 16, 5, 4), (61, 20, 9, 4)]:
    r = construct_and_test(q, n, k, w)
    if r is None: print(f"({q},{n},{k},{w}): construction not instantiated")
