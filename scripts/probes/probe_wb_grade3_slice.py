#!/usr/bin/env python3
"""Grade-3 validation of the graded pencil ladder (#371, WB-6).

Second slice above the boundary: n = 2w+k-2. Predictions from the ladder:
- generic pencil corank = 3 (grade-3 anchor exists, grade-2 dies);
- bad counts stay poly(n) and q-stable, near the witness-rigidity ceiling
  shape sum_{j<=w} C(n,j) when w <= c-1... at w=2 < c=3 EVERY error set has
  |E| <= 2 < c: the count should be governed by the |E| <= c-1 rigidity class
  alone: <= C(n,2)+C(n,1)+1 - i.e. THE SAME C(n,2) saturation as grade 2(!);
- the grade-3 coincidence class only activates when w >= c = 3.
Instances: (q, 6, 2, 2) n=2w+k-2=6, q in {31, 127} (mu6: 6 | q-1).
Also (q, 9, 5, 3): n = 2*3+5-2 = 9, w=3=c: the coincidence class activates;
mu9 | q-1: q in {19, 127}.
"""
import random, os
from collections import Counter
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
random.seed(31415)

def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None

def run(q, n, k, w, trials):
    g = gen_mu(q, n)
    if g is None:
        print(f"q={q} n={n}: no mu_{n}")
        return
    inst = Inst(q, n, k, w, g)
    cdist = Counter(); badmax = 0; badsum = 0; cnt = 0
    for _ in range(trials):
        l0 = [random.randrange(q) for _ in range(w + 1)]
        r0 = [random.randrange(q) for _ in range(w + k)]
        l1 = [random.randrange(q) for _ in range(w + 1)]
        r1 = [random.randrange(q) for _ in range(w + k)]
        if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
            continue
        u0, u1 = inst.ratword(l0, r0), inst.ratword(l1, r1)
        if u0 is None or u1 is None:
            continue
        M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
        ncol = sum(dims)
        mr = 0
        for gam in range(q):
            M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)]
                 for i in range(len(M0))]
            rk, _ = rank_and_kernel(M, q)
            mr = max(mr, rk)
        cdist[ncol - mr] += 1
        B = bad_set(inst, u0, u1)
        badmax = max(badmax, len(B)); badsum += len(B); cnt += 1
    import math
    print(f"(q,n,k,w)=({q},{n},{k},{w}): stacks={cnt} corank dist={dict(cdist)} "
          f"max|BAD|={badmax} mean={badsum/max(cnt,1):.1f} "
          f"[C(n,2)+n+1={math.comb(n,2)+n+1} C(n,3)={math.comb(n,3)}]", flush=True)

# w=2 < c=3: rigidity class governs; expect q-stable max <= C(n,2)+n+1 = 22
run(31, 6, 2, 2, 50)
run(127, 6, 2, 2, 30)
# w=3 = c: coincidence class activates; expect counts ~ C(n,3)-shape, q-stable
run(19, 9, 5, 3, 25)
run(127, 9, 5, 3, 12)

# q-stabilization check at the true grade-3 slice
run(271, 9, 5, 3, 8)
run(523, 9, 5, 3, 5)
