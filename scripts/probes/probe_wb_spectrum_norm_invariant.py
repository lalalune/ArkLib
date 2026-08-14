import os
from itertools import combinations
from collections import Counter
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None
def census_g(q, n, k, a, w):
    g = gen_mu(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    ns = n - w; dh = a - ns
    conds = list(range(k, a - 1)); nunk = dh
    gammas = set()
    for S in combinations(range(n), ns):
        zs = [1]
        for i in S:
            zs = pmul(zs, [(-dom[i]) % q, 1], q)
        A = [[(zs[j - t] if 0 <= j - t < len(zs) else 0) for t in range(nunk)]
             for j in conds]
        b = [(-(zs[j - dh] if 0 <= j - dh < len(zs) else 0)) % q for j in conds]
        M = [A[r] + [b[r]] for r in range(len(conds))]
        rA, _ = rank_and_kernel([row[:-1] for row in M], q)
        rM, _ = rank_and_kernel(M, q)
        if rA != rM: continue
        rk, ker = rank_and_kernel([row[:-1] + [(-row[-1]) % q] for row in M], q,
                                  want_kernel=True)
        sol = next(([c * pow(v[-1], q-2, q) % q for c in v[:-1]]
                    for v in ker if v[-1] != 0), None)
        if sol is None: continue
        h = sol + [1]
        zh = pmul(zs, h, q)
        gammas.add((zh[a - 1] if a - 1 < len(zh) else 0) % q)
    return gammas
q, n, k = 449, 14, 4
for (a, w) in [(10, 8), (9, 8), (10, 7), (9, 7), (8, 8)]:
    j = (n - k - 1) - w
    gs = census_g(q, n, k, a, w)
    gs_nz = [x for x in gs if x != 0]
    norms = set(pow(x, n, q) for x in gs_nz)
    print(f"a={a} w={w} j={j}: #γ={len(gs)} (nz={len(gs_nz)}) #cosets={len(norms)} "
          f"norms={sorted(norms)[:5]}", flush=True)
