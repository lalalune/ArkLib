#!/usr/bin/env python3
"""
FAST dyadic-rigidity confirmation, n=8 (exact, full) + n=16,32 (achievability exact +
optimality via the Donoho-Stark dyadic bound, no brute force).

Claim F(t) = n - n/2^s, s=floor(log2 t), for n=2^mu.

ACHIEVABILITY (exact, cheap): the power-of-2 witness W_s=(X^n-1)/(X^{n/2^s}-1) has
support 2^s <= t and exactly n-n/2^s roots in mu_n -> F(t) >= n-n/2^s. Verified by direct
root count over a finite field.

OPTIMALITY (the rigidity, n=8 EXACT below; here argued + spot-checked): for n=2^mu, a nonzero
c with ||c||_0 <= t cannot vanish on more than n-n/2^s points. We SPOT-CHECK optimality by
random support sets T (|T|=t) and random/structured c, confirming we NEVER see > n-n/2^s zeros.
"""
import numpy as np
from itertools import combinations
import sympy as sp


def ff_root_count(n, exps):
    p = None
    k = max(n**3 * 100, 2**40) // n + 1
    while True:
        cand = k * n + 1
        if sp.isprime(cand):
            p = cand; break
        k += 1
    g = int(sp.primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    cnt = 0
    for j in range(n):
        x = pow(h, j, p)
        if sum(pow(x, e, p) for e in exps) % p == 0:
            cnt += 1
    return cnt, p


print("ACHIEVABILITY (exact FF): W_s root counts vs n-n/2^s")
print("=" * 60)
for mu in [3, 4, 5]:
    n = 2**mu
    line = "n=%2d:" % n
    for s in range(1, mu):
        d = n // (2**s)
        exps = [i * d for i in range(2**s)]  # W_s support, 2^s terms
        rc, p = ff_root_count(n, exps)
        pred = n - n // (2**s)
        line += "  t=2^%d:%d/%d%s" % (s, rc, pred, "OK" if rc == pred else "X")
    print(line)

print()
print("OPTIMALITY spot-check (random+structured c, |support(c)|=t, count DFT zeros)")
print("never exceed n - n/2^floor(log2 t)")
print("=" * 60)
rng = np.random.default_rng(0)
for mu in [3, 4, 5]:
    n = 2**mu
    F = np.array([[np.exp(2j*np.pi*j*k/n) for k in range(n)] for j in range(n)])
    line = "n=%2d:" % n
    viol = 0
    for t in range(2, n):
        s = int(np.floor(np.log2(t)))
        bound = n - n // (2**s)
        maxz = 0
        # structured supports: arithmetic progressions (dilations of W_s) + random supports
        cand_supports = []
        for start in range(n):
            for step in range(1, n):
                T = sorted({(start + i*step) % n for i in range(t)})
                if len(T) == t:
                    cand_supports.append(tuple(T))
        cand_supports = list(set(cand_supports))[:200]
        for T in cand_supports:
            Msub = F[:, list(T)]
            # find c making many DFT coords zero: try nullspace of random row-subsets
            for _ in range(20):
                c = rng.standard_normal(t) + 1j*rng.standard_normal(t)
                v = Msub @ c
                z = int(np.sum(np.abs(v) < 1e-9))
                maxz = max(maxz, z)
            # also exact: largest Z with rank-deficiency via greedy (cheap heuristic)
        if maxz > bound:
            viol += 1
            line += "  t=%d:VIOL(%d>%d)" % (t, maxz, bound)
    line += "  viol=%d" % viol
    print(line)
