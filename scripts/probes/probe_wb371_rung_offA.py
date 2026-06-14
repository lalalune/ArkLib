#!/usr/bin/env python3
"""
Verify the two rung census laws at (p, n, k) = (12289, 16, 3), |S| = 7:

LAW 1 (off-A disjointness): for bad gammas attached to agreement set A
(R1 = q_A on A, R1 - q_A = m_A * h1) with a COMMON frame r (R0 = r on S∩A,
P = r + gamma*q_A), the pairwise witness intersections satisfy
S ∩ S' ⊆ A ∪ roots(h1).

LAW 2 (per-frame cap): #attached gammas per frame <= (n - |A|) + deg h1.

Test on the antipodal pencil (A = half-cosets of mu_16, q_A = ±X, h1 linear)
using the exact witness data from the fiber enumeration; then engineered
two-frame stacks.
"""
import itertools

p, n, k = 12289, 16, 3

def mu_n():
    for g in range(2, 300):
        ok = all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3))
        if ok:
            h = pow(g, (p - 1) // n, p)
            return sorted(pow(h, j, p) for j in range(n))
    raise RuntimeError

D = mu_n()

def polmul(a, b):
    out = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                out[i + j] = (out[i + j] + x * y) % p
    return out

def m_of(T):
    out = [1]
    for x in T:
        out = polmul(out, [(-x) % p, 1])
    return out

def polmod(a, b):
    a = [x % p for x in a]
    db = max(i for i in range(len(b)) if b[i] % p)
    inv = pow(b[db], p - 2, p)
    for i in range(len(a) - 1, db - 1, -1):
        c = a[i] % p
        if c:
            f = (c * inv) % p
            for j in range(db + 1):
                a[i - db + j] = (a[i - db + j] - f * b[j]) % p
    out = [x % p for x in a[:db]]
    return out + [0] * (db - len(out))

def solve_affine(M, rhs):
    rows = len(M); cols = len(M[0])
    Aug = [M[r][:] + [rhs[r]] for r in range(rows)]
    piv_cols = []
    r = 0
    for c in range(cols):
        piv = None
        for rr in range(r, rows):
            if Aug[rr][c] % p:
                piv = rr; break
        if piv is None:
            continue
        Aug[r], Aug[piv] = Aug[piv], Aug[r]
        ip = pow(Aug[r][c], p - 2, p)
        Aug[r] = [(x * ip) % p for x in Aug[r]]
        for rr in range(rows):
            if rr != r and Aug[rr][c] % p:
                f = Aug[rr][c]
                Aug[rr] = [(Aug[rr][i] - f * Aug[r][i]) % p for i in range(cols + 1)]
        piv_cols.append(c)
        r += 1
    for rr in range(r, rows):
        if Aug[rr][cols] % p:
            return None
    base = [0] * cols
    for i, c in enumerate(piv_cols):
        base[c] = Aug[i][cols]
    return base, cols - len(piv_cols)

SUBS7 = list(itertools.combinations(range(n), 7))

def all_witnesses(R0, R1):
    """exhaustive: (gamma, Sidx) pairs from the dim-0 fiber."""
    R0p = [(R0[i] if i < len(R0) else 0) % p for i in range(10)]
    out = []
    for Sidx in SUBS7:
        S = [D[i] for i in Sidx]
        mS = m_of(S)
        cols = []
        for gi in range(3):
            cols.append(polmod(polmul([0] * gi + [1], mS), R1))
        for pi in range(3):
            cols.append(polmod([0] * pi + [1], R1))
        rhs_poly = polmod(R0p, R1)
        M = [[cols[c][r] for c in range(6)] for r in range(9)]
        rhs = [rhs_poly[r] for r in range(9)]
        sol = solve_affine(M, rhs)
        if sol is None:
            continue
        base, kdim = sol
        if kdim != 0:
            continue
        tot9 = 0
        for gi in range(3):
            full = polmul([0] * gi + [1], mS)
            if len(full) > 9:
                tot9 = (tot9 + base[gi] * full[9]) % p
        tot9 = (tot9 - (R0p[9] if len(R0p) > 9 else 0)) % p
        if tot9:
            out.append((tot9, Sidx))
    return out

# THE PENCIL
R0 = [0] * 8 + [1]
R1 = [0] * 9 + [1]
wits = all_witnesses(R0, R1)
gammas = sorted(set(g for g, _ in wits))
print(f"pencil: {len(wits)} (gamma, S) witness pairs, {len(gammas)} distinct gammas")

# agreement sets of R1 = X^9 on mu_16: A+ = {x : x^8 = 1} (x^9 = x), A- = (x^9 = -x)
Aplus = [i for i in range(n) if pow(D[i], 8, p) == 1]
Aminus = [i for i in range(n) if pow(D[i], 8, p) == p - 1]
print(f"A+ (x^9=x): {len(Aplus)} pts; A- (x^9=-x): {len(Aminus)} pts")

# h1 for A+: R1 - q = X^9 - X = X(X^8-1) = m_{A+} * h1 -> h1 = X (root 0, off domain)
# attached gammas per A: witness has >= 3 points in A
for A, qname in [(Aplus, "X"), (Aminus, "-X")]:
    Aset = set(A)
    attached = {}
    for g, Sidx in wits:
        inA = set(Sidx) & Aset
        if len(inA) >= 3:
            attached.setdefault(g, []).append(Sidx)
    print(f"\n  A with q={qname}: attached gammas = {len(attached)} "
          f"(law-2 cap = (n-|A|)+deg h1 = {n - len(A)} + 1 = {n - len(A) + 1})")
    # LAW 1: pairwise S∩S' ⊆ A (h1 = X has no domain roots here)
    viol = 0
    pairs = 0
    glist = sorted(attached)
    for i in range(len(glist)):
        for j in range(i + 1, len(glist)):
            for S1 in attached[glist[i]][:3]:
                for S2 in attached[glist[j]][:3]:
                    pairs += 1
                    inter = set(S1) & set(S2)
                    if not inter <= Aset:
                        viol += 1
    print(f"    law-1 (S∩S' ⊆ A) over {pairs} sampled pairs: violations = {viol}")
    # off-A parts disjoint?
    offs = []
    for g in glist:
        offunion = set()
        for S in attached[g]:
            offunion |= (set(S) - Aset)
        offs.append((g, sorted(offunion)))
    print(f"    off-A parts per gamma: {[(g % 1000, o) for g, o in offs[:9]]}")
