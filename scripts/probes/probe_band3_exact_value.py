#!/usr/bin/env python3
"""Band-3 exact upper bound at (17,8,4,<2>), |T|>=6: every bad gamma needs the line's
syndrome to lie in W2 (syndromes of wt<=2 words). So B6 <= max over affine syndrome
lines of |line ∩ W2|. Computed exhaustively over all (direction, offset) pairs."""
import numpy as np
from itertools import combinations

p, n, k, g = 17, 8, 4, 2
dom = [pow(g, i, p) for i in range(n)]

# parity-check: codewords = eval of deg<4 polys; syndrome via dual basis.
# Build generator G (k x n), then nullspace basis H (4 x 8) over F17.
G = np.array([[pow(x, e, p) for x in dom] for e in range(k)], dtype=np.int64)
# RREF of G to find nullspace
M = G.copy() % p
piv_cols = []
r = 0
for c in range(n):
    pr = None
    for i in range(r, k):
        if M[i][c] % p: pr = i; break
    if pr is None: continue
    M[[r, pr]] = M[[pr, r]]
    inv = pow(int(M[r][c]), p-2, p)
    M[r] = (M[r] * inv) % p
    for i in range(k):
        if i != r and M[i][c] % p:
            M[i] = (M[i] - M[i][c] * M[r]) % p
    piv_cols.append(c); r += 1
free_cols = [c for c in range(n) if c not in piv_cols]
Hrows = []
for fc in free_cols:
    v = [0]*n; v[fc] = 1
    for ri, pc in enumerate(piv_cols):
        v[pc] = (-M[ri][fc]) % p
    Hrows.append(v)
H = np.array(Hrows, dtype=np.int64) % p  # 4 x 8, G @ H.T = 0
assert (G @ H.T % p == 0).all()

def syn_idx(w):
    s = (H @ np.array(w, dtype=np.int64)) % p
    return int(s[0] + 17*s[1] + 17**2*s[2] + 17**3*s[3])

Q = 17**4
W2 = np.zeros(Q, dtype=bool)
W2[syn_idx([0]*n)] = True
for i in range(n):
    for v in range(1, p):
        w = [0]*n; w[i] = v; W2[syn_idx(w)] = True
for i, j in combinations(range(n), 2):
    for v1 in range(1, p):
        for v2 in range(1, p):
            w = [0]*n; w[i] = v1; w[j] = v2; W2[syn_idx(w)] = True
print(f"|W2| = {W2.sum()}", flush=True)

# enumerate directions s1 (normalized: first nonzero coord = 1) as 4-tuples
# precompute index arithmetic: idx(s) with s in F17^4 packed base 17.
digits = np.array([(np.arange(Q) // 17**t) % 17 for t in range(4)])  # 4 x Q

best = 0; best_data = None
# directions: iterate over normalized s1
from itertools import product
dirs = []
for lead in range(4):
    for rest in product(range(17), repeat=3-lead):
        s1 = [0]*lead + [1] + list(rest)
        dirs.append(s1)
print(f"directions: {len(dirs)}", flush=True)
all_idx = np.arange(Q)
for di, s1 in enumerate(dirs):
    s1idx = s1[0] + 17*s1[1] + 17**2*s1[2] + 17**3*s1[3]
    # count[s0] = sum_gamma W2[s0 + gamma*s1]
    cnt = np.zeros(Q, dtype=np.int8)
    for gam in range(17):
        # shift index: s0 + gam*s1 componentwise mod 17
        shift = [(gam*s1[t]) % 17 for t in range(4)]
        newd = [(digits[t] + shift[t]) % 17 for t in range(4)]
        nidx = newd[0] + 17*newd[1] + 17**2*newd[2] + 17**3*newd[3]
        cnt += W2[nidx]
    m = int(cnt.max())
    if m > best:
        best = m
        s0 = int(np.argmax(cnt))
        best_data = (s1, s0)
        print(f"NEW MAX {best} at dir={s1} s0={s0}", flush=True)
print(f"\nFINAL: max line-W2 incidence = {best}  => B6 <= {best}", flush=True)

print("REFINED: restrict to directions with coset min-weight >= 3", flush=True)
# coset min-weight <= 2 <=> syndrome in W2. A direction class s1 has min-wt <= 2 iff
# any scalar multiple of s1 is in W2 (coset of t*u1 = t*coset).
W2set = W2.copy()
best2 = 0; bd = None
for di, s1 in enumerate(dirs):
    # check scalar multiples: t*s1 for t in 1..16 — if any in W2, skip (u1 close to wt<=2)
    skip = False
    for t in range(1, 17):
        st = [(t*s1[c]) % 17 for c in range(4)]
        if W2set[st[0] + 17*st[1] + 289*st[2] + 4913*st[3]]:
            skip = True; break
    if skip: continue
    cnt = np.zeros(Q, dtype=np.int8)
    for gam in range(17):
        shift = [(gam*s1[t]) % 17 for t in range(4)]
        newd = [(digits[t] + shift[t]) % 17 for t in range(4)]
        nidx = newd[0] + 17*newd[1] + 289*newd[2] + 4913*newd[3]
        cnt += W2[nidx]
    m = int(cnt.max())
    if m > best2:
        best2 = m; bd = (s1, int(np.argmax(cnt)))
        print(f"  new max {best2} at dir={s1}", flush=True)
print(f"REFINED MAX (u1-coset min-wt >= 3): B6-contribution <= {best2}", flush=True)

print("EXACT wt-2-direction count (s0 outside the C+<S1> classes):", flush=True)
# wt-2 (and wt-1) coset directions: rep = unique wt<=2 word in the coset of u1.
# For each such direction with rep support S1, count line∩W2 max over s0 ∉ synSet(S1).
# synSet(S1) = syndromes of words supported in S1 (289 of them; line-shift invariant).
rep_of = {}
rep_of[0] = tuple()
for i in range(n):
    for v in range(1, p):
        w = [0]*n; w[i] = v; rep_of[syn_idx(w)] = (i,)
for i, j in combinations(range(n), 2):
    for v1 in range(1, p):
        for v2 in range(1, p):
            w = [0]*n; w[i] = v1; w[j] = v2; rep_of[syn_idx(w)] = (i, j)

best3 = 0; bd3 = None
for di, s1 in enumerate(dirs):
    s1i = s1[0] + 17*s1[1] + 289*s1[2] + 4913*s1[3]
    # find if some scalar multiple t*s1 is a wt<=2 syndrome; if so the coset class of u1
    S1 = None
    for t in range(1, 17):
        sti = ((t*s1[0])%17) + 17*((t*s1[1])%17) + 289*((t*s1[2])%17) + 4913*((t*s1[3])%17)
        if sti in rep_of:
            S1 = rep_of[sti]; break
    if S1 is None or len(S1) == 0: continue  # only wt-1/wt-2 directions
    # synSet(S1) as boolean over Q
    synS = np.zeros(Q, dtype=bool)
    if len(S1) == 1:
        i0 = S1[0]
        for v in range(p):
            w = [0]*n; w[i0] = v; synS[syn_idx(w)] = True
    else:
        i0, j0 = S1
        for v1 in range(p):
            for v2 in range(p):
                w = [0]*n; w[i0] = v1; w[j0] = v2; synS[syn_idx(w)] = True
    cnt = np.zeros(Q, dtype=np.int8)
    for gam in range(17):
        shift = [(gam*s1[t]) % 17 for t in range(4)]
        newd = [(digits[t] + shift[t]) % 17 for t in range(4)]
        nidx = newd[0] + 17*newd[1] + 289*newd[2] + 4913*newd[3]
        cnt += W2[nidx]
    cnt[synS] = 0  # exclude s0 in C+<S1> (where the supp=S1 gammas may not be bad)
    m = int(cnt.max())
    if m > best3:
        best3 = m; bd3 = (s1, S1, int(np.argmax(cnt)))
        print(f"  new max {best3} at dir={s1} S1={S1}", flush=True)
print(f"EXACT wt<=2-direction max: {best3}", flush=True)
print(f"\n==> B6 = max({best3} [wt<=2 dirs, ALL explainable bad], 7-ceiling [far dirs])", flush=True)

print("UNIFIED EXACT wt<=2-direction bad count:", flush=True)
# bad_gamma <=> rep exists AND (S1 ⊄ supp(rep) OR s0 ∉ synSet(supp(rep)))
# supp-id tables
supps = [tuple()] + [(i,) for i in range(n)] + list(combinations(range(n), 2))
suppid_of = {s: i for i, s in enumerate(supps)}
suppid = np.full(Q, 37, dtype=np.int8)
for sidx, sp in rep_of.items():
    suppid[sidx] = suppid_of[sp]
# synMem[suppid][s] : s in synSet(supp)
SM = np.zeros((38, Q), dtype=bool)
for sid, sp in enumerate(supps):
    if len(sp) == 0:
        SM[sid][0] = True
    elif len(sp) == 1:
        i0 = sp[0]
        for v in range(p):
            w = [0]*n; w[i0] = v; SM[sid][syn_idx(w)] = True
    else:
        i0, j0 = sp
        for v1 in range(p):
            for v2 in range(p):
                w = [0]*n; w[i0] = v1; w[j0] = v2; SM[sid][syn_idx(w)] = True
# contains[S1-id][suppid] : S1 ⊆ supp
def s1_contains_table(S1):
    t = np.zeros(38, dtype=bool)
    for sid, sp in enumerate(supps):
        t[sid] = set(S1).issubset(set(sp))
    return t

best4 = 0; bd4 = None
idxQ = np.arange(Q)
for di, s1 in enumerate(dirs):
    S1 = None
    for t in range(1, 17):
        sti = ((t*s1[0])%17) + 17*((t*s1[1])%17) + 289*((t*s1[2])%17) + 4913*((t*s1[3])%17)
        if sti in rep_of and len(rep_of[sti]) >= 1:
            S1 = rep_of[sti]; break
        if sti in rep_of and len(rep_of[sti]) == 0:
            S1 = tuple(); break
    if S1 is None or len(S1) == 0: continue  # min-wt >= 3 handled (<=7); u1 ∈ C degenerate
    ctab = s1_contains_table(S1)
    badcnt = np.zeros(Q, dtype=np.int8)
    for gam in range(17):
        shift = [(gam*s1[t]) % 17 for t in range(4)]
        newd = [(digits[t] + shift[t]) % 17 for t in range(4)]
        nidx = newd[0] + 17*newd[1] + 289*newd[2] + 4913*newd[3]
        m1 = W2[nidx]
        sid_g = suppid[nidx]
        contains = ctab[sid_g]
        synm = SM[sid_g, idxQ]
        bad = m1 & (~contains | ~synm)
        badcnt += bad
    m = int(badcnt.max())
    if m > best4:
        best4 = m; bd4 = (s1, S1, int(np.argmax(badcnt)))
        print(f"  new max {best4} at dir={s1} S1={S1}", flush=True)
print(f"UNIFIED wt<=2 exact max: {best4}")
print(f"\n*** B6 EXACT = max({best4}, 7) ***", flush=True)
