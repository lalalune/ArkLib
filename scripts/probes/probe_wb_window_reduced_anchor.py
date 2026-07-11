#!/usr/bin/env python3
"""Reduced-pencil anchor check (#371): class-V corank inflation is a common-factor
artifact.

When l_j vanishes at domain points, the WB relation forces R_j to vanish there
too, so T_j := prod (x-b) over those points divides l_j, R_j — and T_0*T_1
divides ALL FOUR pencil data polys (l1*R0, l0*R1, l0*l1, Z_D).  The REDUCED
pencil (data divided by T_0*T_1, Z_D -> vanishing poly of the punctured domain)
carries the same kernel vectors for every bad scalar.

Test: for class-V stacks whose every representation pair is unanchored
(probe_wb_window_anchor_existential.py found 103/130), compute the corank of the
REDUCED pencil.  Prediction: corank <= 1 (anchored) after reduction.
"""
import random
from collections import Counter
from itertools import combinations
import os

exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))

random.seed(31337)
q, n, k, w, g = 13, 6, 1, 2, 4
inst = Inst(q, n, k, w, g)

def reduced_data(l0, r0, l1, r1):
    """Divide out the forced common domain-root factors; return
    (lt0, rt0, lt1, rt1, ZDt, punctured_count) or None if multiplicity strands."""
    lt = [pnorm(l0), pnorm(l1)]
    rt = [pnorm(r0), pnorm(r1)]
    punct = []
    for j in (0, 1):
        for x in inst.dom:
            while lt[j] and peval(lt[j], x, q) == 0:
                if peval(rt[j], x, q) != 0:
                    return None  # WB relation would fail; shouldn't happen
                lt[j], rem1 = pdivmod(lt[j], [(-x) % q, 1], q)
                rt[j], rem2 = pdivmod(rt[j], [(-x) % q, 1], q)
                assert not rem1 and not rem2
                punct.append(x)
    zdt = [1]
    from collections import Counter as Cnt
    pc = Cnt(punct)
    if any(v > 1 for v in pc.values()):
        # a domain point punctured twice (once per row, or multiplicity):
        # divide Z_D only once per available root — strand if exceeded
        if any(v > 1 for v in pc.values()):
            return None
    for x in inst.dom:
        if x not in pc:
            zdt = pmul(zdt, [(-x) % q, 1], q)
    return lt[0], rt[0], lt[1], rt[1], zdt, len(punct)

def pencil_matrices_zd(l0, r0, l1, r1, ZD):
    A = pmul(l1, r0, q)
    B = pmul(l0, r1, q)
    L = pmul(l0, l1, q)
    maxd = max(len(pnorm(l0)) - 1 if pnorm(l0) else 0,
               len(pnorm(l1)) - 1 if pnorm(l1) else 0)
    m = 3 * w + k - 1 - n   # uniform Lean cap
    nh = m + 1 if m >= 0 else 0
    T = 3 * w + k - 1
    nz, nq = w + 1, w + k
    ncol = nz + nq + nh
    M0 = [[0] * ncol for _ in range(T + 1)]
    M1 = [[0] * ncol for _ in range(T + 1)]
    for j in range(nz):
        for i, c in enumerate(A):
            if i + j <= T:
                M0[i + j][j] = c
        for i, c in enumerate(B):
            if i + j <= T:
                M1[i + j][j] = c
    for j in range(nq):
        for i, c in enumerate(L):
            if i + j <= T:
                M0[i + j][nz + j] = (-c) % q
    for j in range(nh):
        for i, c in enumerate(ZD):
            if i + j <= T:
                M0[i + j][nz + nq + j] = (-c) % q
    return M0, M1, (nz, nq, nh)

def corank_zd(l0, r0, l1, r1, ZD):
    M0, M1, dims = pencil_matrices_zd(l0, r0, l1, r1, ZD)
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

stats = Counter()
strands = 0
mismatch = 0
for trial in range(2000):
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
    # original corank
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims)
    mr = 0
    for gam in range(q):
        M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)]
             for i in range(len(M0))]
        rk, _ = rank_and_kernel(M, q)
        mr = max(mr, rk)
    ck_orig = ncol - mr
    red = reduced_data(l0, r0, l1, r1)
    if red is None:
        strands += 1
        continue
    lt0, rt0, lt1, rt1, zdt, np_ = red
    ck_red = corank_zd(lt0, rt0, lt1, rt1, zdt)
    stats[(ck_orig, ck_red)] += 1
    if ck_orig >= 2 and ck_red >= 2:
        B = bad_set(inst, u0, u1)
        mismatch += 1
        if mismatch <= 8:
            print(f"  REDUCED STILL CORANK {ck_red} (orig {ck_orig}) |BAD|={len(B)} "
                  f"lt0={lt0} rt0={rt0} lt1={lt1} rt1={rt1} punct={np_}", flush=True)

print(f"(orig corank, reduced corank) distribution: {dict(sorted(stats.items()))}")
print(f"strands={strands}  reduced-still-degenerate={mismatch}")
print("VERDICT:", "reduction rescues the anchor" if mismatch == 0
      else "reduction insufficient — analyze residual degeneracies")
