#!/usr/bin/env python3
"""THE COST LAW above UDR: tuned-R alignment and the capacity-explosion interpolation.

(#371 WB lane, Fable round 5, fork experiment.)

Mechanism: above UDR, gamma is explainable with witness D\\T iff the residue
(l1*R0 + gamma*l0*R1) * Z_S^{-1} mod l0*l1 has degree <= j = 3w+k-1-n.  That is
cost := 2w-(j+1) = n-k-w  LINEAR conditions on (R0,R1) per target T (one gamma each).
Tuning (R0,R1) (2(w+k) parameters), the adversary affords

    #targets ~ 2(w+k) / (n-k-w)        [the COST LAW]

which is O(1) in the mid-window, ~n at the second-to-last band (cost 2), ~2n at the
last band before capacity (cost 1, w = n-k-1) -- where the in-tree boundary lower
bound is n (sup side OPEN): the tuned family would be the first ~2n family there.

Pre-registered predictions:
  P-cost: exact bad count of tuned stacks tracks min(2(w+k)/(n-k-w) + O(1), q-ish),
          and most tuned-explainable gammas remain BAD (no-joint rarely fires for
          genuinely rational tuned stacks even above UDR).
  P-mid:  in the mid-window (cost >= 4) the tuned count is O(1) -- no mass production
          without tower amplification.

Method: exact linear algebra for the tuning; exact mcaEvent verification (enumerate
agreement sets; joint = both rows interpolable).
"""
import random
from itertools import combinations

random.seed(55)

def find_gen(q, n):
    if (q - 1) % n: return None
    for g in range(2, q):
        x = pow(g, (q - 1) // n, q)
        if len({pow(x, i, q) for i in range(n)}) == n: return x
    return None

# ---------- polynomial helpers mod (m, q) ----------
def pmul(a, b, q):
    res = [0] * (len(a) + len(b) - 1)
    for i, ai in enumerate(a):
        if ai:
            for j, bj in enumerate(b):
                res[i + j] = (res[i + j] + ai * bj) % q
    return res or [0]

def pmod(a, m, q):
    a = a[:]
    dm = len(m) - 1
    inv = pow(m[-1], q - 2, q)
    while len(a) > dm:
        f = a[-1] * inv % q
        if f:
            off = len(a) - 1 - dm
            for i in range(dm + 1):
                a[off + i] = (a[off + i] - f * m[i]) % q
        a.pop()
    while len(a) < dm: a.append(0)
    return a

def pinv(a, m, q):
    # extended Euclid in F_q[X]
    def divmod_(num, den):
        num = num[:]
        while den and den[-1] % q == 0: den = den[:-1]
        inv = pow(den[-1], q - 2, q)
        quo = [0] * max(1, len(num) - len(den) + 1)
        while True:
            while num and num[-1] % q == 0: num.pop()
            if len(num) < len(den): break
            f = num[-1] * inv % q
            off = len(num) - len(den)
            quo[off] = f
            for i in range(len(den)):
                num[off + i] = (num[off + i] - f * den[i]) % q
            num.pop()
        return quo, (num or [0])
    r0, r1 = m[:], pmod(a, m, q)
    s0, s1 = [0], [1]
    while any(v % q for v in r1):
        qq, rr = divmod_(r0, r1)
        prod = pmul(qq, s1, q)
        ln = max(len(s0), len(prod))
        s_new = [((s0[i] if i < len(s0) else 0) - (prod[i] if i < len(prod) else 0)) % q
                 for i in range(ln)]
        r0, r1, s0, s1 = r1, rr, s1, s_new
    while r0 and r0[-1] % q == 0: r0.pop()
    cinv = pow(r0[0], q - 2, q)
    return pmod([v * cinv % q for v in s0], m, q)

def evalp(co, x, q):
    a = 0
    for cf in reversed(co): a = (a * x + cf) % q
    return a

# ---------- generic F_q linear solver: A x = b, returns one solution or None ----------
def solve_lin(A, b, q):
    m = len(A); ncol = len(A[0]) if m else 0
    M = [row[:] + [bb % q] for row, bb in zip(A, b)]
    r = 0; piv = []
    for c in range(ncol):
        p = next((i for i in range(r, m) if M[i][c] % q), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        inv = pow(M[r][c], q - 2, q)
        M[r] = [(v * inv) % q for v in M[r]]
        for i in range(m):
            if i != r and M[i][c] % q:
                f = M[i][c]
                M[i] = [(a - f * bb) % q for a, bb in zip(M[i], M[r])]
        piv.append(c); r += 1
    if any(M[i][ncol] % q for i in range(r, m)): return None
    x = [0] * ncol
    for ri, c in enumerate(piv): x[c] = M[ri][ncol]
    return x

def make_solver(q, n, k, dom):
    pw = [[pow(x, j, q) for j in range(k)] for x in dom]
    def solve(idxs, vals):
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
        if any(rows[i][k] % q for i in range(r, m_)): return None
        return True
    def explset(idxs, vals, getA=False):
        # returns full agreement set of the interpolant through idxs (if consistent)
        rows = [pw[i][:] + [vals[i] % q] for i in idxs]
        m_, r, piv = len(rows), 0, []
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
            piv.append(c); r += 1
        if any(rows[i][k] % q for i in range(r, m_)): return None
        co = [0] * k
        for ri, c in enumerate(piv): co[c] = rows[ri][k]
        return tuple(i for i in range(n) if evalp(co, dom[i], q) == vals[i] % q)
    return solve, explset

def run(q, n, k, w, n_targets, trials=4):
    g = find_gen(q, n)
    if g is None: return
    dom = [pow(g, i, q) for i in range(n)]
    domset = set(dom)
    j = 3 * w + k - 1 - n
    cost = n - k - w
    tmin = n - w
    # generic degree-w denominators, nonvanishing on D
    def rand_denom():
        while True:
            l = [random.randrange(q) for _ in range(w)] + [1]
            if all(evalp(l, x, q) for x in dom): return l
    best = (0, 0)
    for tr in range(trials):
        l0 = rand_denom(); l1 = rand_denom()
        m01 = pmul(l0, l1, q)
        Xn1 = [(-1) % q] + [0] * (n - 1) + [1]
        # targets
        Ts = [tuple(sorted(random.sample(range(n), w))) for _ in range(n_targets)]
        Ts = list(dict.fromkeys(Ts))
        gammas = random.sample(range(1, q), len(Ts))
        # linear system in (R0 coeffs (w+k), R1 coeffs (w+k)):
        # top cost coeffs of rep((l1*R0 + gamma*l0*R1) * ZS^{-1} mod m01) vanish
        nvar = 2 * (w + k)
        A_rows, b_rows = [], []
        for T, gam in zip(Ts, gammas):
            ZT = [1]
            for i in T: ZT = pmul(ZT, [(-dom[i]) % q, 1], q)
            ZS = pmul(Xn1, pinv(ZT, m01, q), q)   # Z_S mod m01 (as (X^n-1)/Z_T)
            ZSinv = pinv(ZS, m01, q)
            for cidx in range(j + 1, 2 * w):      # coefficients that must vanish
                row = []
                for which, lpoly, scale in ((0, l1, 1), (1, l0, gam)):
                    for d in range(w + k):
                        base = pmod(pmul(pmul([0]*d + [1], lpoly, q), ZSinv, q), m01, q)
                        row.append(base[cidx] * scale % q)
                A_rows.append(row); b_rows.append(0)
        sol = solve_lin(A_rows, b_rows, q)
        # need NONZERO genuine solution: add random affine pin if trivial
        if sol is None or not any(sol):
            # pin one coordinate to 1 by moving it to RHS: brute small retry
            ok = False
            for pin in range(nvar):
                A2 = [r[:pin] + r[pin+1:] for r in A_rows]
                b2 = [(-r[pin]) % q for r in A_rows]
                s2 = solve_lin(A2, b2, q)
                if s2 is not None:
                    sol = s2[:pin] + [1] + s2[pin:]; ok = True; break
            if not ok: continue
        R0 = sol[: w + k]; R1 = sol[w + k:]
        if not any(R0) or not any(R1): continue
        def ratword(l, r):
            out = []
            for x in dom:
                lv = evalp(l, x, q)
                if lv == 0: return None
                out.append(evalp(r, x, q) * pow(lv, q - 2, q) % q)
            return tuple(out)
        u0 = ratword(l0, R0); u1 = ratword(l1, R1)
        if u0 is None or u1 is None: continue
        # exact analysis
        solvek, explset = make_solver(q, n, k, dom)
        subs = list(combinations(range(n), tmin))
        expl = 0; bad = 0
        for gam in range(q):
            line = [(u0[i] + gam * u1[i]) % q for i in range(n)]
            asets = set()
            for S in subs:
                A = explset(list(S), line)
                if A is not None and len(A) >= tmin: asets.add(A)
            if not asets: continue
            expl += 1
            for A in asets:
                if solvek(list(A), list(u0)) is None or solvek(list(A), list(u1)) is None:
                    bad += 1; break
        best = max(best, (bad, expl))
    pred = (2 * (w + k)) // max(cost, 1)
    print(f"({q},{n},{k}) w={w} UDR={(n-k)//2} cost={cost} j={j} "
          f"targets={n_targets} -> best (bad, expl) = {best}  cost-law pred ~{pred}")

print("== mid-window (cost >= 3): expect O(1) ==")
run(37, 12, 6, 4, 8)      # cost 2 actually: n-k-w = 2
run(61, 16, 4, 8, 6)      # cost 4, rate 1/4
run(61, 16, 4, 9, 8)      # cost 3
print("== boundary bands (cost 1-2): expect ~n .. ~2n ==")
run(37, 12, 6, 5, 18)     # cost 1: w = n-k-1: pred ~22 vs known boundary n=12
run(61, 16, 4, 11, 28)    # cost 1: pred ~30 vs n=16
run(61, 16, 4, 10, 14)    # cost 2: pred ~14
