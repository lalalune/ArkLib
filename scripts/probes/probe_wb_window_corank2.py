#!/usr/bin/env python3
"""Falsification probe for WindowPencilAnchored (#371): hunt pencil corank >= 2.

The window law (WBPencilWindowLaw.lean) is conditional on ONE Prop: every
doubly-WB-solvable stack admits WB representations whose window pencil has
corank <= 1 over F(gamma) (some adjugate entry of some square row-selection is
a nonzero polynomial).  Random genuine rational pairs gave 0/4000 violations.

This probe attacks the Prop where the theory predicts it is weakest:
1. RANDOM extended scan (rational pairs, exact corank distribution);
2. CLASS V — rows that are rational-with-exception: u = R/l off the zero set of
   l (l vanishing at some domain points, R forced to vanish there too, u free at
   those points).  These rows are WBSolvable but may admit NO nonvanishing-
   denominator representation, and the cyclic-kernel structure argument
   (which forces corank <= 1) needs gcd(l0*l1, Z_D) = 1 — exactly what fails here.
3. STRUCTURED: shared denominators, proportional numerators, row repeats.

For every corank>=2 hit: record |BAD| (mca-bad count) and whether the stack is
jointly explainable (which would make the hit harmless: 0 bad scalars).

Instance: (q,n,k,w) = (13,6,1,2) — square pencil (rows 3w+k = 7 = N cols).
Corank over F(gamma) = N - max_{gamma in F_q} rank (valid: minors have
gamma-degree <= w+1 = 3 < q).
"""
import random
from collections import Counter
from itertools import combinations
import os

exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))

random.seed(424242)

q, n, k, w, g = 13, 6, 1, 2, 4
inst = Inst(q, n, k, w, g)

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

def jointly_explainable(u0, u1):
    # exists S size >= n-w with BOTH rows constant on S (k=1)
    for S in combinations(range(n), n - w):
        if len(set(u0[i] for i in S)) == 1 and len(set(u1[i] for i in S)) == 1:
            return True
    return False

def wb_relations_ok(l, r, u):
    return all(peval(l, x, q) * u[i] % q == peval(r, x, q) % q
               for i, x in enumerate(inst.dom))

hits = []

def report(tag, l0, r0, l1, r1, u0, u1):
    ck = corank(l0, r0, l1, r1)
    if ck >= 2:
        B = bad_set(inst, u0, u1)
        je = jointly_explainable(u0, u1)
        hits.append((tag, ck, len(B), je))
        print(f"  CORANK {ck} [{tag}] |BAD|={len(B)} joint={je} "
              f"l0={l0} r0={r0} l1={l1} r1={r1} u0={u0} u1={u1}", flush=True)
    return ck

# ---- 1. random scan ----
print("=== part 1: random rational pairs, corank distribution ===", flush=True)
dist = Counter()
for _ in range(20000):
    l0 = [random.randrange(q) for _ in range(3)]
    r0 = [random.randrange(q) for _ in range(3)]
    l1 = [random.randrange(q) for _ in range(3)]
    r1 = [random.randrange(q) for _ in range(3)]
    if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
        continue
    u0, u1 = inst.ratword(l0, r0), inst.ratword(l1, r1)
    if u0 is None or u1 is None:
        continue
    dist[report("random", l0, r0, l1, r1, u0, u1)] += 1
print(f"random corank dist: {dict(dist)}")

# ---- 2. class V: rational-with-exception rows ----
print("=== part 2: CLASS V (vanishing-denominator reps) ===", flush=True)
distV = Counter()
tried = 0
for _ in range(20000):
    # l vanishes at a domain point a; R = (x-a)*r1deg<=1; u = R/l off a, free at a
    a_idx0 = random.randrange(n)
    a0 = inst.dom[a_idx0]
    lq = [random.randrange(q), 1]          # monic linear cofactor (may vanish on dom too)
    l0 = pmul([(-a0) % q, 1], lq, q)
    rq = [random.randrange(q), random.randrange(q)]
    r0 = pmul([(-a0) % q, 1], rq, q)
    # u0: R/l where l != 0, free elsewhere
    u0 = []
    ok = True
    for i, x in enumerate(inst.dom):
        lv = peval(l0, x, q)
        if lv == 0:
            u0.append(random.randrange(q))
        else:
            u0.append(peval(r0, x, q) * pow(lv, q - 2, q) % q)
    # check WB relations actually hold (l*u = R on all of dom)
    if not wb_relations_ok(l0, r0, u0):
        continue
    # second row: same construction or genuine rational
    if random.random() < 0.5:
        a_idx1 = random.randrange(n)
        a1 = inst.dom[a_idx1]
        lq1 = [random.randrange(q), 1]
        l1 = pmul([(-a1) % q, 1], lq1, q)
        rq1 = [random.randrange(q), random.randrange(q)]
        r1 = pmul([(-a1) % q, 1], rq1, q)
        u1 = []
        for i, x in enumerate(inst.dom):
            lv = peval(l1, x, q)
            if lv == 0:
                u1.append(random.randrange(q))
            else:
                u1.append(peval(r1, x, q) * pow(lv, q - 2, q) % q)
        if not wb_relations_ok(l1, r1, u1):
            continue
    else:
        l1 = [random.randrange(q) for _ in range(3)]
        r1 = [random.randrange(q) for _ in range(3)]
        if not genuine_reduced(inst, l1, r1):
            continue
        u1 = inst.ratword(l1, r1)
        if u1 is None:
            continue
        u1 = list(u1)
    tried += 1
    distV[report("classV", l0, r0, l1, r1, tuple(u0), tuple(u1))] += 1
print(f"class V tried={tried} corank dist: {dict(distV)}")

# ---- 3. structured ----
print("=== part 3: structured (shared denom / proportional / repeat) ===", flush=True)
distS = Counter()
for _ in range(6000):
    mode = random.randrange(3)
    l0 = [random.randrange(q) for _ in range(3)]
    r0 = [random.randrange(q) for _ in range(3)]
    if not genuine_reduced(inst, l0, r0):
        continue
    u0 = inst.ratword(l0, r0)
    if u0 is None:
        continue
    if mode == 0:      # shared denominator
        l1 = l0[:]
        r1 = [random.randrange(q) for _ in range(3)]
        if not genuine_reduced(inst, l1, r1):
            continue
    elif mode == 1:    # proportional numerator, different denom
        c = random.randrange(1, q)
        r1 = psmul(c, r0, q)
        l1 = [random.randrange(q) for _ in range(3)]
        if not genuine_reduced(inst, l1, r1):
            continue
    else:              # repeat row
        l1, r1 = l0[:], r0[:]
    u1 = inst.ratword(l1, r1)
    if u1 is None:
        continue
    distS[report(f"struct{mode}", l0, r0, l1, r1, u0, u1)] += 1
print(f"structured corank dist: {dict(distS)}")

print(f"\nTOTAL corank>=2 hits: {len(hits)}")
if hits:
    cc = Counter((t, ck, je) for t, ck, b, je in hits)
    print(f"hit classes (tag, corank, jointly-explainable): {dict(cc)}")
    print(f"max |BAD| among hits: {max(b for _, _, b, _ in hits)}")
else:
    print("WindowPencilAnchored survives all attack classes at this instance")
