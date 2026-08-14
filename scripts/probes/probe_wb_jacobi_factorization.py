import random, os
from collections import Counter
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
random.seed(31337)
q, n, k, w = 29, 7, 4, 2
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
inst = Inst(q, n, k, w, gen_mu(q, n))

# polynomial matrices over F_q[gamma]: entries as coeff lists
def pol_add(a, b): return padd(a, b, q)
def pol_mul(a, b): return pmul(a, b, q)
def pol_neg(a): return psmul(q - 1, a, q)

def build_B2(l0, r0, l1, r1, J, c0, c0p, cs, csp):
    """The doubly-updated square selection as a matrix of gamma-polynomials.
    Columns: 0..nz-1 (Z), nz..nz+nq-1 (Q), then h-block. Rows selected by J."""
    A = pmul(l1, r0, q); B = pmul(l0, r1, q); L = pmul(l0, l1, q)
    m = 3 * w + k - 1 - n
    nh = m + 1 if m >= 0 else 0
    nz, nq = w + 1, w + k
    N = nz + nq + nh
    rows = 3 * w + k
    # full pencil entries as gamma-polys: M[r][col]
    def entry(r, col):
        if col < nz:
            j = col
            a0 = A[r - j] if 0 <= r - j < len(A) else 0
            b0 = B[r - j] if 0 <= r - j < len(B) else 0
            return pnorm([a0 % q, b0 % q])
        if col < nz + nq:
            j = col - nz
            c = L[r - j] if 0 <= r - j < len(L) else 0
            return pnorm([(-c) % q])
        j = col - nz - nq
        c = inst.ZD[r - j] if 0 <= r - j < len(inst.ZD) else 0
        return pnorm([(-c) % q])
    B2 = [[entry(J[a], b) for b in range(N)] for a in range(N)]
    for b in range(N):
        B2[c0][b] = pnorm([1]) if b == cs else []
        B2[c0p][b] = pnorm([1]) if b == csp else []
    return B2, N, nz

def pol_det(M):
    """Fraction-free-ish determinant of a small poly matrix via expansion (N<=8)."""
    Nn = len(M)
    if Nn == 1: return M[0][0]
    det = []
    for c in range(Nn):
        if not M[0][c]: continue
        sub = [[M[r][cc] for cc in range(Nn) if cc != c] for r in range(1, Nn)]
        t = pol_mul(M[0][c], pol_det(sub))
        det = pol_add(det, t if c % 2 == 0 else pol_neg(t))
    return det

def adj_entry(B2, i, col):
    """adjugate(B2) i col = det(B2 with row col replaced by e_i)."""
    Nn = len(B2)
    M = [row[:] for row in B2]
    M[col] = [pnorm([1]) if b == i else [] for b in range(Nn)]
    return pol_det(M)

def pol_divmod(a, b):
    return pdivmod(a, b, q)

trials = 0; div_ok = 0; div_fail = 0; hdegs = Counter(); hroots = Counter()
while trials < 8:
    l0 = [random.randrange(q) for _ in range(w + 1)]
    r0 = [random.randrange(q) for _ in range(w + k)]
    l1 = [random.randrange(q) for _ in range(w + 1)]
    r1 = [random.randrange(q) for _ in range(w + k)]
    if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)): continue
    if inst.ratword(l0, r0) is None or inst.ratword(l1, r1) is None: continue
    nzq = (w + 1) + (w + k)
    m = 3 * w + k - 1 - n
    N = nzq + (m + 1 if m >= 0 else 0)
    rows = 3 * w + k
    # slots 0,1 are overwritten by singles; remaining N-2 slots carry pencil rows
    if N - 2 > rows: break
    J = [0, 0] + list(range(N - 2))
    c0, c0p, cs, csp = 0, 1, 0, 1   # update rows 0,1 -> singles at cols 0,1
    B2, N, nz = build_B2(l0, r0, l1, r1, J, c0, c0p, cs, csp)
    detB2 = pol_det(B2)
    if not detB2: continue
    trials += 1
    # K^col entries at locator rows, as polys; G^col_i = sum_t adj(inl t, col) x_i^t
    i, j = 0, 5
    def Gpoly(col, idx):
        acc = []
        for t in range(nz):
            e = adj_entry(B2, t, col)   # row index (inl t) = t in our flat layout
            acc = pol_add(acc, psmul(pow(inst.dom[idx], t, q), e, q))
        return acc
    Gi1, Gi2 = Gpoly(c0, i), Gpoly(c0p, i)
    Gj1, Gj2 = Gpoly(c0, j), Gpoly(c0p, j)
    gij = pol_add(pol_mul(Gi1, Gj2), pol_neg(pol_mul(Gj1, Gi2)))
    if not gij:
        print(f"  trial {trials}: g_ij == 0 (twin)"); continue
    quo, rem = pol_divmod(gij, detB2)
    if rem:
        div_fail += 1
        print(f"  trial {trials}: DIVISIBILITY FAILS deg g={len(gij)-1} deg det={len(detB2)-1}")
    else:
        div_ok += 1
        h = quo
        nroots = sum(1 for gam in range(q) if peval(h, gam, q) == 0)
        hdegs[len(h) - 1] += 1; hroots[nroots] += 1
        print(f"  trial {trials}: det | g  ✓  deg det={len(detB2)-1} deg h={len(h)-1} h-roots={nroots}")
print(f"\ndivisibility: ok={div_ok} fail={div_fail}; h degrees={dict(hdegs)} h root counts={dict(hroots)}")
