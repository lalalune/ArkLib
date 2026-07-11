import os
from itertools import combinations
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None
q, n, k, a_exp, w = 37, 9, 2, 7, 5
g = gen_mu(q, n)
dom = [pow(g, i, q) for i in range(n)]
dlog = {x: i for i, x in enumerate(dom)}
ns = n - w; dh = a_exp - ns
conds = list(range(k, a_exp - 1)); nunk = dh
print(f"dom = mu9 in F37: {dom}")
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
    # factor h over F_q: roots + check domain membership
    hroots = [x for x in range(q) for _ in range(1)
              if peval(h, x, q) == 0]
    # multiplicity check
    hr = []
    hh = h[:]
    for x in range(q):
        while peval(hh, x, q) == 0 and len(hh) > 1:
            hh, _ = pdivmod(hh, [(-x) % q, 1], q)
            hr.append(x)
    irred = len(hh) > 1
    Tlogs = sorted(dlog[dom[i]] for i in S)
    x0 = (q - gam) % q  # -gamma: the predicted domain root
    print(f"T(logs)={Tlogs} γ={gam} −γ={x0}{'∈dom(log ' + str(dlog.get(x0)) + ')' if x0 in dlog else '∉dom'} "
          f"h-roots={hr}{' +irred' if irred else ''} "
          f"hroots∈dom={[dlog.get(r) for r in hr]}", flush=True)
