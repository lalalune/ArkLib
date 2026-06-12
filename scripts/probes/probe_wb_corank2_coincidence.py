#!/usr/bin/env python3
"""The corank-2 coincidence-graph law (#371): cracking the multi-parameter wall
one slice ABOVE the boundary.

At n = 2w+k-1 (first slice past the pencil law's exact reach) the window pencil
has generic corank 2: kernels are spanned by two Cramer families K1(g), K2(g)
(polynomial entries, gamma-degree <= w+1).  A split witness at gamma is
alpha*K1(gamma) + beta*K2(gamma) with Z-part = Z_E: for each error point a in E,
the ratio lambda_a(gamma) := -Z1(gamma,a)/Z2(gamma,a) must take the COMMON value
beta/alpha — so bad gamma's need a w-clique in the coincidence graph
{(a,b) : lambda_a(gamma) = lambda_b(gamma)}.

PREDICTIONS to validate/falsify:
1. generic corank at n = 2w+k-1 is 2; the 2-dim kernel = span{K1,K2} at good gamma;
2. bad gammas (off the secondary-minor root set) are exactly those where some
   w-subset of ratio functions coincides AND the candidate vector certifies;
3. non-twinned pairs (a,b) coincide at <= 2(w+1) gammas => poly count;
   twin pairs (identical ratio functions) form the degenerate classes —
   check whether twin classes relate to normalizer/Moebius pair structure.

Instance: (q,n,k,w) = (29,7,4,2), mu7 in F29 (7 | 28). n = 2w+k-1 = 7.
"""
import random
from collections import Counter
from itertools import combinations
import os

exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),
     "probe_wb_window_pencil_crt.py")).read().split("total_mm = 0")[0]
     .replace('random.seed(20260611)', 'pass'))

random.seed(2718281)

q, n, k, w = 29, 7, 4, 2
g7 = None
for cand in range(2, q):
    if pow(cand, 7, q) == 1 and cand != 1:
        g7 = cand
        break
inst = Inst(q, n, k, w, g7)
print(f"dom = {inst.dom} (mu7 in F29), n=2w+k-1={2*w+k-1}")

def full_rank_data(l0, r0, l1, r1):
    M0, M1, dims = pencil_matrices(inst, l0, r0, l1, r1)
    ncol = sum(dims)
    ranks = {}
    kers = {}
    for gam in range(q):
        M = [[(M0[i][j] + gam * M1[i][j]) % q for j in range(ncol)]
             for i in range(len(M0))]
        rk, ker = rank_and_kernel(M, q, want_kernel=True)
        ranks[gam] = rk
        kers[gam] = ker
    return M0, M1, dims, ranks, kers

def expl_and_bad(u0, u1):
    return expl_set(inst, u0, u1), bad_set(inst, u0, u1)

stats = Counter()
twin_reports = []
for trial in range(400):
    l0 = [random.randrange(q) for _ in range(w + 1)]
    r0 = [random.randrange(q) for _ in range(w + k)]
    l1 = [random.randrange(q) for _ in range(w + 1)]
    r1 = [random.randrange(q) for _ in range(w + k)]
    if not (genuine_reduced(inst, l0, r0) and genuine_reduced(inst, l1, r1)):
        continue
    u0, u1 = inst.ratword(l0, r0), inst.ratword(l1, r1)
    if u0 is None or u1 is None:
        continue
    M0, M1, dims, ranks, kers = full_rank_data(l0, r0, l1, r1)
    ncol = sum(dims)
    maxrank = max(ranks.values())
    ck = ncol - maxrank
    stats[("corank", ck)] += 1
    if ck != 2:
        continue
    # the 2-dim kernel: ratio coincidence analysis at each gamma with kerdim 2
    E_, B_ = expl_and_bad(u0, u1)
    stats[("maxbad", len(B_))] += 0  # placeholder to record below
    nz = dims[0]
    # per-gamma: compute the set of "splittable" gammas from the kernel directly
    # (reference check: explainable == exists D-split Z in 2-dim kernel; reuse crt probe logic)
    P_, _ = pencil_expl_set(inst, M0, M1, dims)
    if P_ != E_:
        print(f"  REFORMULATION MISMATCH at corank2: E={sorted(E_)} P={sorted(P_)}")
        stats[("mismatch",)] += 1
        continue
    stats[("badmax_seen", len(B_))] += 1
    # ratio-coincidence structure at kerdim-2 gammas:
    # build lambda_a(gamma) per gamma from an actual kernel basis (numeric, per gamma)
    coincidence_gammas = set()
    for gam in range(q):
        ker = kers[gam]
        if len(ker) != 2:
            continue
        K1, K2 = ker
        # Z-parts evaluated at domain points
        z1 = [sum(K1[t] * pow(a, t, q) for t in range(nz)) % q for a in inst.dom]
        z2 = [sum(K2[t] * pow(a, t, q) for t in range(nz)) % q for a in inst.dom]
        # lambda_a as projective pairs (z1[a] : z2[a]); coincidence pairs:
        cnt = Counter()
        for i in range(n):
            # projective normalize
            pa = (z1[i], z2[i])
            if pa == (0, 0):
                key = "zero"
            else:
                if pa[1] != 0:
                    key = (pa[0] * pow(pa[1], q - 2, q)) % q
                else:
                    key = "inf"
            cnt[key] += 1
        if any(v >= w for kk, v in cnt.items() if kk != "zero"):
            coincidence_gammas.add(gam)
    # bad should be inside coincidence_gammas (necessary condition)
    if not set(B_) <= coincidence_gammas:
        print(f"  NECESSARY-CONDITION VIOLATION: bad={sorted(B_)} "
              f"coinc={sorted(coincidence_gammas)}")
        stats[("necviol",)] += 1
    stats[("coinc_size", len(coincidence_gammas))] += 1

print(f"\nstats: {dict(sorted(stats.items(), key=str))}")

# adversarial: aligned/twin-rich constructions — adjacent monomial pairs
print("\n=== adjacent pairs at the above-boundary slice ===")
for a in range(1, n):
    u0 = [pow(x, a, q) for x in inst.dom]
    u1 = [pow(x, a - 1, q) for x in inst.dom]
    # find any WB rep
    ncol_wb = (w + 1) + (w + k)
    M = []
    for i, x in enumerate(inst.dom):
        row = [pow(x, t, q) * u0[i] % q for t in range(w + 1)]
        row += [(-pow(x, s, q)) % q for s in range(w + k)]
        M.append(row)
    _, ker0 = rank_and_kernel(M, q, want_kernel=True)
    M = []
    for i, x in enumerate(inst.dom):
        row = [pow(x, t, q) * u1[i] % q for t in range(w + 1)]
        row += [(-pow(x, s, q)) % q for s in range(w + k)]
        M.append(row)
    _, ker1 = rank_and_kernel(M, q, want_kernel=True)
    rep = lambda kk: next(((pnorm(list(v[:w+1])), pnorm(list(v[w+1:])))
                           for v in kk if pnorm(list(v[:w+1]))), None)
    s0, s1 = rep(ker0), rep(ker1)
    if s0 is None or s1 is None:
        continue
    M0, M1, dims, ranks, kers = full_rank_data(*s0, *s1)
    ncol = sum(dims)
    ck = ncol - max(ranks.values())
    B = bad_set(inst, u0, u1)
    print(f"  a={a}: corank={ck} |BAD|={len(B)} bad={sorted(B)}")
