#!/usr/bin/env python3
"""WindowPencilAnchored existential check (#371): do corank>=2 stacks admit an
ANCHORED representation pair?

probe_wb_window_corank2.py found corank>=2 pencils throughout class V
(vanishing-denominator representations), all with |BAD| <= 2.  The Prop
WindowPencilAnchored is EXISTENTIAL over WB representations: for each corank>=2
hit, enumerate the full WB solution space of each row (kernel of the n x (2w+k+1)
WB matrix), and search representation pairs for one with pencil corank <= 1.

Output per hit: dimension of each row's WB solution space, number of rep pairs
tried, min corank found, and whether an anchored pair exists.
"""
import random
from collections import Counter
from itertools import combinations, product
import os

exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))

random.seed(31337)

q, n, k, w, g = 13, 6, 1, 2, 4
inst = Inst(q, n, k, w, g)

def wb_solutions(u):
    """All (l, R) with deg l <= w, deg R <= w+k-1, l != 0, l(x_i)u_i = R(x_i)."""
    # matrix: columns l_0..l_w, R_0..R_{w+k-1}; rows: domain points
    ncol = (w + 1) + (w + k)
    M = []
    for i, x in enumerate(inst.dom):
        row = [pow(x, t, q) * u[i] % q for t in range(w + 1)]
        row += [(-pow(x, s, q)) % q for s in range(w + k)]
        M.append(row)
    rk, ker = rank_and_kernel(M, q, want_kernel=True)
    return ker  # basis of solution space

def corank(l0, r0, l1, r1):
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims)
    mr = 0
    for gam in range(q):
        M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)]
             for i in range(len(M0))]
        rk, _ = rank_and_kernel(M, q)
        mr = max(mr, rk)
        if mr == ncol:
            break
    return ncol - mr

def vec_to_rep(v):
    l = pnorm(list(v[:w + 1]))
    r = pnorm(list(v[w + 1:]))
    return l, r

def all_reps(u, cap=400):
    """Enumerate nonzero WB solutions (up to scalar) with l != 0."""
    ker = wb_solutions(u)
    d = len(ker)
    reps = []
    seen = set()
    if d == 0:
        return reps, 0
    for coefs in product(range(q), repeat=d):
        if not any(coefs):
            continue
        first = next(i for i, c in enumerate(coefs) if c)
        if coefs[first] != 1:
            continue   # projective normalization
        v = [0] * len(ker[0])
        for ci, c in enumerate(coefs):
            if c:
                v = [(v[j] + c * ker[ci][j]) % q for j in range(len(v))]
        l, r = vec_to_rep(v)
        if not l:
            continue
        key = (tuple(l), tuple(r))
        if key in seen:
            continue
        seen.add(key)
        reps.append((l, r))
        if len(reps) >= cap:
            break
    return reps, d

# the recorded corank>=2 hits from probe_wb_window_corank2.py (subset incl. corank 3/4 reps)
HITS = [
    ([2, 10, 1], [3, 6, 4], [5, 4, 1], [5, 2, 6], (12, 0, 9, 11, 1, 3), (0, 4, 6, 11, 3, 7)),
    ([5, 7, 1], [1, 0, 12], [7, 12, 1], [7, 5, 12], (2, 5, 2, 0, 4, 3), (9, 4, 0, 3, 10, 8)),
    ([11, 11, 1], [0, 7, 11], [5, 4, 1], [11, 1, 10], (7, 8, 3, 4, 2, 0), (10, 10, 1, 10, 10, 10)),
    ([0, 9, 1], [0, 9, 1], [7, 1, 1], [11, 7, 4], (1, 3, 1, 1, 1, 1), (1, 12, 7, 3, 10, 0)),
    ([9, 2, 0], [1, 10, 0], [9, 2, 0], [1, 10, 0], (1, 7, 9, 8, 0, 12), (1, 7, 9, 8, 0, 12)),
]

print("=== recorded corank>=2 hits: existential anchored-rep search ===")
unanchored_stacks = []
for idx, (l0, r0, l1, r1, u0, u1) in enumerate(HITS):
    u0, u1 = list(u0), list(u1)
    ck_orig = corank(l0, r0, l1, r1)
    reps0, d0 = all_reps(u0)
    reps1, d1 = all_reps(u1)
    best = ck_orig
    tried = 0
    found = None
    for (a0, b0) in reps0:
        for (a1, b1) in reps1:
            tried += 1
            ck = corank(a0, b0, a1, b1)
            if ck < best:
                best = ck
                found = (a0, b0, a1, b1)
            if best <= 1:
                break
        if best <= 1:
            break
    print(f"hit {idx}: orig corank={ck_orig} wbdim=({d0},{d1}) "
          f"reps=({len(reps0)},{len(reps1)}) tried={tried} min corank={best} "
          f"{'ANCHORED via ' + str(found) if best <= 1 else 'NO ANCHORED REP FOUND'}",
          flush=True)
    if best >= 2:
        B = bad_set(inst, u0, u1)
        unanchored_stacks.append((idx, best, len(B)))

# fresh class-V sample for statistics
print("\n=== fresh class-V sample: existential anchored fraction ===", flush=True)
stat = Counter()
worst_unanchored = []
for trial in range(300):
    a0 = inst.dom[random.randrange(n)]
    l0 = pmul([(-a0) % q, 1], [random.randrange(q), 1], q)
    r0 = pmul([(-a0) % q, 1], [random.randrange(q), random.randrange(q)], q)
    u0 = []
    for i, x in enumerate(inst.dom):
        lv = peval(l0, x, q)
        u0.append(random.randrange(q) if lv == 0
                  else peval(r0, x, q) * pow(lv, q - 2, q) % q)
    if not all(peval(l0, x, q) * u0[i] % q == peval(r0, x, q)
               for i, x in enumerate(inst.dom)):
        continue
    a1 = inst.dom[random.randrange(n)]
    l1 = pmul([(-a1) % q, 1], [random.randrange(q), 1], q)
    r1 = pmul([(-a1) % q, 1], [random.randrange(q), random.randrange(q)], q)
    u1 = []
    for i, x in enumerate(inst.dom):
        lv = peval(l1, x, q)
        u1.append(random.randrange(q) if lv == 0
                  else peval(r1, x, q) * pow(lv, q - 2, q) % q)
    if not all(peval(l1, x, q) * u1[i] % q == peval(r1, x, q)
               for i, x in enumerate(inst.dom)):
        continue
    if corank(l0, r0, l1, r1) <= 1:
        stat["orig_anchored"] += 1
        continue
    reps0, _ = all_reps(u0, cap=60)
    reps1, _ = all_reps(u1, cap=60)
    best = 99
    for (a0_, b0_) in reps0:
        for (a1_, b1_) in reps1:
            ck = corank(a0_, b0_, a1_, b1_)
            best = min(best, ck)
            if best <= 1:
                break
        if best <= 1:
            break
    if best <= 1:
        stat["rescued"] += 1
    else:
        stat["UNANCHORED"] += 1
        B = bad_set(inst, u0, u1)
        worst_unanchored.append((len(B), l0, r0, l1, r1, u0, u1))
        print(f"  UNANCHORED stack |BAD|={len(B)} u0={u0} u1={u1}", flush=True)
print(f"fresh class-V stats: {dict(stat)}")
if worst_unanchored:
    print(f"max |BAD| among unanchored: {max(b for b, *_ in worst_unanchored)}")
print("\nVERDICT:", "Prop survives (existential rescue)" if not worst_unanchored and not unanchored_stacks
      else "Prop needs weakening — unanchored stacks exist (but check |BAD| scale)")
