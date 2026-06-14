import random, os
from collections import Counter
from itertools import combinations
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
random.seed(555)

def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None

def run(q, n, k, w, trials):
    g = gen_mu(q, n)
    inst = Inst(q, n, k, w, g)
    badmax = 0; badsum = 0; cnt = 0
    coincviol = 0
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
        # necessary-condition check INCLUDING kerdim>=3 gammas
        M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
        nz = dims[0]; ncol = sum(dims)
        ok_gammas = set()
        for gam in range(q):
            M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)]
                 for i in range(len(M0))]
            rk, ker = rank_and_kernel(M, q, want_kernel=True)
            if len(ker) >= 3:
                ok_gammas.add(gam); continue
            if len(ker) == 2:
                K1, K2 = ker
                z1 = [sum(K1[t] * pow(a, t, q) for t in range(nz)) % q for a in inst.dom]
                z2 = [sum(K2[t] * pow(a, t, q) for t in range(nz)) % q for a in inst.dom]
                c2 = Counter()
                for i in range(n):
                    pa = (z1[i], z2[i])
                    if pa == (0, 0): key = "zero"
                    elif pa[1] != 0: key = (pa[0] * pow(pa[1], q - 2, q)) % q
                    else: key = "inf"
                    c2[key] += 1
                if any(v >= w for kk, v in c2.items() if kk != "zero"):
                    ok_gammas.add(gam)
            elif len(ker) == 1:
                if is_dsplit(inst, ker[0][:nz]):
                    ok_gammas.add(gam)
        if not set(B) <= ok_gammas:
            coincviol += 1
    print(f"q={q} n={n}: stacks={cnt} max|BAD|={badmax} mean={badsum/max(cnt,1):.1f} "
          f"necessary-cond violations={coincviol}", flush=True)

run(29, 7, 4, 2, 60)
run(113, 7, 4, 2, 40)
run(449, 7, 4, 2, 15)
