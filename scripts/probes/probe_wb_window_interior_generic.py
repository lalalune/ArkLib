import random, os
from collections import Counter
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
random.seed(60221023)

def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None

import math
def run(q, n, k, w, trials):
    g = gen_mu(q, n)
    if g is None:
        print(f"q={q}: no mu_{n}"); return
    inst = Inst(q, n, k, w, g)
    c = 2 * w + k - n + 1
    pred = math.comb(n, c) * max(0, w + 1 - c) if 0 <= c else None
    badmax = 0; badsum = 0; cnt = 0
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
        B = bad_set(inst, u0, u1)
        badmax = max(badmax, len(B)); badsum += len(B); cnt += 1
    print(f"(q,n,k,w)=({q},{n},{k},{w}) excess={2*w+k-n} c={c}: stacks={cnt} "
          f"max|BAD|={badmax} mean={badsum/max(cnt,1):.1f} frac={badsum/max(cnt,1)/q:.3f} "
          f"[C(n,c)(w+1-c)={pred}]", flush=True)

# (12,4): boundary w=4. Test the march toward capacity w = n-k = 8.
for w in (5, 6, 8):
    run(97, 12, 4, w, 6)
for w in (5, 6, 8):
    run(409, 12, 4, w, 4)

# third q-point (run separately due to cost): (1201,12,4,6): stacks |BAD| = 0,2,2
# scaling summary (q, mean bad): (97, 10.0) -> (409, 1.8) -> (1201, 1.3)
# => interior generic count decays to a q-INDEPENDENT FLOOR ~1-2 (deterministic
#    owned-set component) + O(1/q) tail: generic interior eps_mca ~ O(1)/q,
#    production-silent; the window is adversary-controlled.
