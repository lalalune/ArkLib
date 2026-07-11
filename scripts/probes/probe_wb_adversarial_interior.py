import random, os
from collections import Counter
exec(open("scripts/probes/probe_wb_window_pencil_crt.py").read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))
random.seed(11)
def gen_mu(q, n):
    for cand in range(2, q):
        if pow(cand, n, q) == 1 and all(pow(cand, d, q) != 1 for d in range(1, n) if n % d == 0):
            return cand
    return None
def wb_rep(inst, u, q, w, k):
    M = []
    for i, x in enumerate(inst.dom):
        row = [pow(x, t, q) * u[i] % q for t in range(w + 1)]
        row += [(-pow(x, s, q)) % q for s in range(w + k)]
        M.append(row)
    _, ker = rank_and_kernel(M, q, want_kernel=True)
    return next(((pnorm(list(v[:w+1])), pnorm(list(v[w+1:]))) for v in ker
                 if pnorm(list(v[:w+1]))), None)
import math
def run(q, n, k, w):
    g = gen_mu(q, n)
    inst = Inst(q, n, k, w, g)
    print(f"=== (q,n,k,w)=({q},{n},{k},{w}) ===", flush=True)
    for a in range(k, min(2*k + 3, n)):
        u0 = [pow(x, a, q) for x in inst.dom]
        u1 = [pow(x, a - 1, q) for x in inst.dom]
        B = bad_set(inst, u0, u1)
        # subset-sum comparison: e1 over (n-w)-subsets? compare bad to ALL subset sums
        sums_w = set()
        from itertools import combinations
        for T in combinations(inst.dom, w):
            sums_w.add(sum(T) % q)
        negsums = set((-s) % q for s in sums_w)
        inter = len(set(B) & sums_w)
        interneg = len(set(B) & negsums)
        print(f"  a={a}: |BAD|={len(B)} |∩e1(w-sets)|={inter} |∩−e1|={interneg} "
              f"[#wsums={len(sums_w)}]", flush=True)
run(97, 12, 4, 5)
run(97, 12, 4, 6)
run(409, 12, 4, 6)

# Growth curve at (409,12,4) monomial families: w=5: 12, w=6: 12-13, w=7 (cap-1): 156-301
# (29,14,4,8/9): both saturate q=29 (q too small to discriminate).
# THE CLIFF, explained analytically: line = x^{a-1}(x+gamma) is a 2-term polynomial;
# explainability at slack w needs Z_S*h + P to have vanishing coefficients in [k, a-2]:
# (a-1-k) conditions on (a-n+w+1) unknowns => SQUARE exactly at w = n-k-1 (every S
# certifies: the capacity cliff), overdetermined by j at capacity-1-j: only j-fold
# rank-deficient S-configurations certify. Interior count n = the mu_n rotation orbit
# (smoothness!). Cliff depth = supply of j-fold-deficient configurations on smooth
# domains = subgroup-census-controlled => the window-top term is the census question.
