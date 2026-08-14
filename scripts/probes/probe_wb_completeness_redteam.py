import os
from itertools import combinations
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None
def census(q, n, k, a_exp, w):
    g = gen_mu(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    ns = n - w; dh = a_exp - ns
    if dh < 0: return None
    conds = list(range(k, a_exp - 1)); nunk = dh
    if len(conds) <= nunk: return None  # at/above cliff: skip
    gammas = set(); ncert = 0
    for S in combinations(range(n), ns):
        zs = [1]
        for i in S:
            zs = pmul(zs, [(-dom[i]) % q, 1], q)
        A = [[(zs[j - t] if 0 <= j - t < len(zs) else 0) for t in range(nunk)] for j in conds]
        b = [(-(zs[j - dh] if 0 <= j - dh < len(zs) else 0)) % q for j in conds]
        M = [A[r] + [b[r]] for r in range(len(conds))]
        rA, _ = rank_and_kernel([row[:-1] for row in M], q)
        rM, _ = rank_and_kernel(M, q)
        if rA != rM: continue
        rk, ker = rank_and_kernel([row[:-1] + [(-row[-1]) % q] for row in M], q, want_kernel=True)
        sol = next(([c * pow(v[-1], q-2, q) % q for c in v[:-1]] for v in ker if v[-1] != 0), None)
        if sol is None: continue
        h = sol + [1]
        zh = pmul(zs, h, q)
        gammas.add((zh[a_exp - 1] if a_exp - 1 < len(zh) else 0) % q)
        ncert += 1
    return ncert, gammas, dom
q, n = 31, 15
viol_total = 0
for k in (2, 3):
    for w in range(8, 12):           # interior slices: capacity-1 = 15-k-1
        for a_exp in range(n - w + 1, min(n, n - w + 6)):
            r = census(q, n, k, a_exp, w)
            if r is None: continue
            nc, gs, dom = r
            if nc == 0: continue
            negmu = set((q - x) % q for x in dom)
            nz = set(x for x in gs if x != 0)
            viol = nz - negmu
            viol_total += len(viol)
            print(f"k={k} w={w} s={a_exp} j={(n-k-1)-w}: cert={nc} #γ={len(gs)} "
                  f"off −μ₁₅: {sorted(viol) if viol else 'NONE'}", flush=True)
print(f"\nTOTAL violations of completeness: {viol_total}")
import os
from itertools import combinations
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None
def census(q, n, k, a_exp, w):
    g = gen_mu(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    ns = n - w; dh = a_exp - ns
    if dh < 0: return None
    conds = list(range(k, a_exp - 1)); nunk = dh
    if len(conds) <= nunk: return None
    gammas = set(); ncert = 0
    for S in combinations(range(n), ns):
        zs = [1]
        for i in S:
            zs = pmul(zs, [(-dom[i]) % q, 1], q)
        A = [[(zs[j - t] if 0 <= j - t < len(zs) else 0) for t in range(nunk)] for j in conds]
        b = [(-(zs[j - dh] if 0 <= j - dh < len(zs) else 0)) % q for j in conds]
        M = [A[r] + [b[r]] for r in range(len(conds))]
        rA, _ = rank_and_kernel([row[:-1] for row in M], q)
        rM, _ = rank_and_kernel(M, q)
        if rA != rM: continue
        rk, ker = rank_and_kernel([row[:-1] + [(-row[-1]) % q] for row in M], q, want_kernel=True)
        sol = next(([c * pow(v[-1], q-2, q) % q for c in v[:-1]] for v in ker if v[-1] != 0), None)
        if sol is None: continue
        h = sol + [1]
        zh = pmul(zs, h, q)
        gammas.add((zh[a_exp - 1] if a_exp - 1 < len(zh) else 0) % q)
        ncert += 1
    return ncert, gammas, dom
# 1. q-scaling of the n=15 violation
for q in (31, 211):
    r = census(q, 15, 2, 5, 11)
    nc, gs, dom = r
    negmu = set((q - x) % q for x in dom)
    nz = set(x for x in gs if x != 0)
    print(f"(q={q},15,2,w=11,s=5) j=1: cert={nc} #γ={len(gs)} off−μ₁₅={len(nz - negmu)}",
          flush=True)
# 2. production shape: 2-power n = 16
q2 = 97
viol = 0
for k in (2, 3):
    for w in range(9, 13):
        for a_exp in range(16 - w + 1, min(16, 16 - w + 5)):
            r = census(q2, 16, k, a_exp, w)
            if r is None: continue
            nc, gs, dom = r
            if nc == 0: continue
            negmu = set((q2 - x) % q2 for x in dom)
            nz = set(x for x in gs if x != 0)
            v = nz - negmu
            viol += len(v)
            tag = f"OFF: {sorted(v)[:6]}" if v else "clean"
            print(f"n=16 k={k} w={w} s={a_exp} j={(16-k-1)-w}: cert={nc} #γ={len(gs)} {tag}",
                  flush=True)
print(f"2-power total violations: {viol}")
