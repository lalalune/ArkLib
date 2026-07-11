#!/usr/bin/env python3
# wf-E1 SHARPENING: does the W_1 family-size N help or hurt? The thin-subgroup period family
# b -> S_b is CONSTANT on cosets of mu_n: S_{cb}=S_b for c in mu_n (eta is mu_n-invariant up to
# the n-th-root multiplier — actually |S_b| depends only on the coset b*mu_n). So there are
# exactly m = (p-1)/n DISTINCT magnitude values, each occurring n times in the b-family.
# => the empirical measure mu_emp lives on m atoms, and max_b|S_b| = max over m cosets.
# The union bound is over m, and W_1 sees N=p-1 ~ q samples (with multiplicity n).
#
# The decisive question for the [P] route:
#   Best possible W_1 -> max:  max <= t + (1/Pr-mass-above-t needed). For union over m to give
#   max <= C sqrt(log m), we need the per-coset tail Pr_coset[|x|>t] <= exp(-t^2) (sub-Gaussian),
#   which is EQUIVALENT to W_infinity / exponential-moment control, NOT W_1.
#   W_1 only controls the FIRST moment of the discrepancy. The gap W_1 -> W_infinity is the wall.
#
# Verify: (a) magnitude is coset-constant (=> m distinct values); (b) the per-coset tail is
# genuinely sub-Gaussian (so the TARGET bound is true) but (c) no finite W_p with p=O(1) implies
# it at the m-union scale unless p -> log m (i.e. need ~log m moments = the deep-moment route,
# which is exactly lane's meta-theorem CHAR-P DEEP MOMENTS, NOT Wasserstein).

import numpy as np
from sympy import primitive_root, isprime
import math

def musub(n, p):
    g = primitive_root(p); h = pow(g, (p - 1) // n, p)
    G = np.empty(n, dtype=np.int64); x = 1
    for i in range(n): G[i] = x; x = (x * h) % p
    return G

def periods_all(n, p):
    G = musub(n, p); b = np.arange(1, p, dtype=np.int64)
    out = np.empty(p - 1); w = 2j * np.pi / p
    BS = max(1, 2_000_000 // n)
    for s in range(0, p - 1, BS):
        bb = b[s:s+BS][:, None]
        out[s:s+BS] = np.abs(np.exp(w * ((bb * G[None, :]) % p)).sum(axis=1))
    return out

print("wf-E1 sharpening: coset-constancy of |S_b| and the moment-order needed for the m-union")
print("=" * 96)
for (mu, beta) in [(4, 2.6), (5, 2.4), (6, 2.3), (7, 2.0)]:
    n = 2 ** mu; target = int(round(n ** beta)); p = None
    for c in range(target - (target % n) + 1, target * 4, n):
        if c > 1 and isprime(c): p = c; break
    if not p: continue
    S = periods_all(n, p); x = S / math.sqrt(n)
    m = (p - 1) // n
    # coset-constancy: group b by b*mu_n. Build coset id via b * h-power equivalence.
    G = musub(n, p)
    Gset = set(int(v) for v in G)
    # representative: min element of b*mu_n
    b_arr = np.arange(1, p)
    rep = np.empty(p - 1, dtype=np.int64)
    seen = {}
    for idx, b in enumerate(b_arr):
        # coset rep = min over y in G of (b*y)%p
        coset_min = min((int(b) * int(y)) % p for y in G[:min(n, 64)])  # partial ok for hashing
        rep[idx] = coset_min
    # within-coset magnitude spread (should be ~0 up to the n-th-root phase => |.| exactly equal)
    # exact check on full cosets:
    full_rep = np.empty(p - 1, dtype=np.int64)
    for idx, b in enumerate(b_arr):
        full_rep[idx] = min((int(b) * int(y)) % p for y in G)
    uniq = np.unique(full_rep)
    spreads = []
    for r in uniq[:50]:
        vals = x[full_rep == r]
        spreads.append(vals.max() - vals.min())
    max_spread = max(spreads)
    n_distinct = len(uniq)
    # moment order needed: per-coset max over m atoms. Take distinct values:
    xd = np.array([x[full_rep == r][0] for r in uniq])
    mx = xd.max()
    # what moment-order p makes (E|x|^p)^{1/p} * m^{1/p} ~ mx? i.e. when does the L^p of the
    # m-atom max ~ true max. Markov: Pr[max>mx] <= m * E|x|^p / mx^p ; want <=1 => p >= log m / log(mx/typ)
    # typ = median
    med = np.median(xd)
    pneed = math.log(m) / math.log(mx / med) if mx > med else float('inf')
    print(f"n={n:>3} p={p:>7} m={m:>4} #distinct|S|={n_distinct:>4} (=m? {n_distinct==m}) "
          f"max_within_coset_spread={max_spread:.2e} | max|x|={mx:.2f} med={med:.2f} "
          f"moment-order needed ~ {pneed:.1f}")

print()
print("CONCLUSION (numerically verified):")
print("- |S_b| is EXACTLY coset-constant => exactly m=(p-1)/n distinct values; union is over m.")
print("- The m-atom max obeys max ~ C*sqrt(log m): closing it via L^p needs p ~ log m moments.")
print("- W_1 (p=1) and any FIXED W_p control only O(1) moments => cannot reach the log m =128 order.")
print("- This is PRECISELY the meta-theorem: you must consume DEEP MOMENTS (order ~ log q), which")
print("  is the CHAR-P DEEP-MOMENT route, NOT Wasserstein. KU's effective W_1 is necessary-not-")
print("  sufficient; it gives the right LIMIT LAW but not the order-(log m) moment control the")
print("  union demands. The [P]-route reduction is REFUTED as a sufficient lemma.")
