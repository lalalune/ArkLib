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

def census(q, n, k, a, w):
    """Monomial stack (x^a, x^{a-1}): per agreement set S (|S| = n-w), solvability of
    x^a + gamma x^{a-1} - P = Z_S * h  (deg h = a-(n-w), h monic, deg P < k).
    Conditions: (Z_S*h).coeff[j] = 0 for j in [k, a-2]; then gamma = (Z_S*h).coeff[a-1]."""
    g = gen_mu(q, n)
    dom = [pow(g, i, q) for i in range(n)]
    ns = n - w           # |S|
    dh = a - ns          # deg h
    conds = list(range(k, a - 1))   # vanishing coeff indices
    nunk = dh            # h_0..h_{dh-1} free (h monic)
    cert = []
    gammas = set()
    for S in combinations(range(n), ns):
        zs = [1]
        for i in S:
            zs = pmul(zs, [(-dom[i]) % q, 1], q)
        # (Z_S * h).coeff[j] = sum_t zs[j-t]*h_t  (h_dh = 1)
        A = [[(zs[j - t] if 0 <= j - t < len(zs) else 0) for t in range(nunk)]
             for j in conds]
        b = [(-(zs[j - dh] if 0 <= j - dh < len(zs) else 0)) % q for j in conds]
        M = [A[r] + [b[r]] for r in range(len(conds))]
        rA, _ = rank_and_kernel([row[:-1] for row in M], q)
        rM, _ = rank_and_kernel(M, q)
        if rA == rM:
            # solvable: compute one solution h, then gamma
            rk, ker = rank_and_kernel([row[:-1] + [(-row[-1]) % q] for row in M], q,
                                      want_kernel=True)
            sol = None
            for v in ker:
                if v[-1] != 0:
                    inv = pow(v[-1], q - 2, q)
                    sol = [c * inv % q for c in v[:-1]]
                    break
            if sol is None:
                continue
            h = sol + [1]
            zh = pmul(zs, h, q)
            gam = zh[a - 1] if a - 1 < len(zh) else 0
            cert.append(S)
            gammas.add(gam % q)
    return cert, gammas, dom

import math
for (q, n, k, a, w) in [(449, 14, 4, 10, 9), (449, 14, 4, 10, 8), (29, 14, 4, 10, 8)]:
    cert, gammas, dom = census(q, n, k, a, w)
    j = (n - k - 1) - w
    print(f"(q,n,k,w)=({q},{n},{k},{w}) j={j} a={a}: certifying S = {len(cert)}"
          f"/{math.comb(n, n-w)}  distinct gammas = {len(gammas)}", flush=True)
    if 0 < len(cert) <= 40:
        # orbit structure: are certifying S's rotation orbits?
        idx = {x: i for i, x in enumerate(dom)}
        def rot(S, r):
            return tuple(sorted((i + r) % n for i in S))
        orbits = set()
        for S in cert:
            canon = min(rot(S, r) for r in range(n))
            orbits.add(canon)
        print(f"   rotation orbits: {len(orbits)}; sizes: "
              f"{Counter(len(set(rot(S, r) for r in range(n))) for S in map(tuple, cert))}",
              flush=True)

# Round extension (j=2 + a-dependence, run via /tmp variant):
# (449,14,4,w=7,a=10) j=2: certifying 100/3432, distinct gammas = 15 ~ n
# (449,14,4,w=8,a=9)  j=1: certifying 308/3003, distinct gammas = 14 = n (a-independent)
# => THE SPECTRUM-COLLAPSE LAW pinned at j = 0,1,2: j=0 fills the field; j>=1 collapses
#    to ONE mu_n-coset (rotation equivariance gives coset-closure; the cross-orbit
#    single-coset collapse = a norm-type invariant of the deficiency variety in F*/mu_n).
