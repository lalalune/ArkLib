#!/usr/bin/env python3
"""For each of the 80 kill-rule-surviving E5 relation triples: is the linear
system U a == (32,32,32) (mod 64) satisfiable with pairwise-distinct fibers
(a_i mod 32 distinct)?  WLOG a_1 = 0 (translation) => parity-pure even branch;
odd branch is its translate.  1M grid per triple via numpy."""
import itertools, collections
import numpy as np

idx = list(range(5))
V = []
for omit in idx:
    rest = [i for i in idx if i != omit]
    a = rest[0]
    for b in rest[1:]:
        c, d = [x for x in rest[1:] if x != b]
        u = np.zeros(5, dtype=np.int64)
        u[a] = u[b] = 1; u[c] = u[d] = -1
        V.append((omit, u))
assert len(V) == 15

def killed(us):
    for eps in itertools.product((-1, 0, 1), repeat=len(us)):
        Tp = sum(1 for e in eps if e)
        if Tp == 0: continue
        c = sum(e * u for e, u in zip(eps, us))
        nz = c[c != 0]
        if len(nz) == 0:
            if Tp % 2: return True
        elif len(nz) == 2 and sorted(nz) == [-1, 1]:
            return True
        elif len(nz) == 2 and sorted(nz) == [-2, 2] and Tp % 2 == 0:
            return True
    return False

# grid of even a_2..a_5 (a_1 = 0): 32^4
g = np.arange(0, 64, 2, dtype=np.int64)
A2, A3, A4, A5 = np.meshgrid(g, g, g, g, indexing='ij')
A = np.stack([np.zeros_like(A2), A2, A3, A4, A5]).reshape(5, -1)   # 5 x 1M
F = (A % 32)
distinct = np.ones(A.shape[1], dtype=bool)
for i in range(5):
    for j in range(i + 1, 5):
        distinct &= (F[i] != F[j])
print(f"distinct-fiber grid points: {distinct.sum()} of {A.shape[1]}")

surv_sat = 0; surv_unsat = 0
sat_examples = []
for t in itertools.combinations(V, 3):
    us = [u for _, u in t]
    if killed(us): continue
    ok = distinct.copy()
    for u in us:
        ok &= ((u @ A) % 64 == 32)
    nsol = int(ok.sum())
    if nsol:
        surv_sat += 1
        if len(sat_examples) < 3:
            w = np.where(ok)[0][0]
            sat_examples.append((tuple(o for o, _ in t), A[:, w].tolist()))
    else:
        surv_unsat += 1
print(f"surviving triples: satisfiable={surv_sat}, unsatisfiable={surv_unsat}")
for om, a in sat_examples:
    print(f"  e.g. omits {om}: a = {a}  (fibers {[x % 32 for x in a]})")
