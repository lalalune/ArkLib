import os
from itertools import combinations
from collections import Counter, defaultdict
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None
q, n, k, a_exp, w = 97, 16, 3, 9, 10
g = gen_mu(q, n)
dom = [pow(g, i, q) for i in range(n)]
dlog = {x: i for i, x in enumerate(dom)}
ns = n - w; dh = a_exp - ns
conds = list(range(k, a_exp - 1)); nunk = dh
bycoset = defaultdict(list)
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
    gam = (zh[a_exp - 1] if a_exp - 1 < len(zh) else 0) % q
    # h root structure
    hr = []
    hh = h[:]
    for x in range(q):
        while len(hh) > 1 and peval(hh, x, q) == 0:
            hh, _ = pdivmod(hh, [(-x) % q, 1], q)
            hr.append(x)
    coset = pow(gam, n, q) if gam else 'zero'
    Tlogs = tuple(sorted(dlog[dom[i]] for i in S))
    # log-difference pattern (rotation-invariant signature)
    diffs = tuple(sorted((Tlogs[(i+1) % len(Tlogs)] - Tlogs[i]) % n for i in range(len(Tlogs))))
    bycoset[coset].append((Tlogs, diffs, gam, tuple(sorted(hr)), len(hh) - 1))
print(f"dom=mu16 in F97; cosets found: {sorted(bycoset.keys(), key=str)}")
for coset, items in sorted(bycoset.items(), key=lambda kv: str(kv[0])):
    diffsigs = Counter(it[1] for it in items)
    print(f"\ncoset γ¹⁶={coset}: {len(items)} configs, T-diff signatures: {dict(diffsigs)}")
    for it in items[:3]:
        x0 = (q - it[2]) % q
        print(f"   T={it[0]} γ={it[2]} −γ{'∈dom log'+str(dlog.get(x0)) if x0 in dlog else '∉dom'} "
              f"h-roots={it[3]} irred-deg={it[4]}")
