#!/usr/bin/env python3
"""WF407 / T334-13-M3 : ground-truth brute M2/M3/M4 agreement moments at n=6 (mu_6 F_13).

The decomp probes establish the t2-ladder (P1,P2 pinned, P3+ separate).  Here we
CONFIRM the agreement-moment claim itself by exact brute force at the smallest scale
where the smooth subgroup's normalizer spikes exist (mu_6 in F_13: -1 in H, the
inversion + negation pencils present).  We compare the FULL agreement-moment tensors
M2, M3, M4 (over all q^n words) of the subgroup vs several random 6-subsets, and the
coset (must equal subgroup exactly by affine invariance).

EXACT integers.  Cost: 13^6 = 4.8M words x 13^k codewords.  Reproduce:
    python wf407_T334-13-M3_brute_n6.py
"""

import itertools
import math
import random
import sys
from operator import eq


def primitive_root(q):
    def pf(m):
        fs, d = set(), 2
        while d * d <= m:
            while m % d == 0:
                fs.add(d); m //= d
            d += 1
        if m > 1:
            fs.add(m)
        return fs
    fs = pf(q - 1)
    for g in range(2, q):
        if all(pow(g, (q - 1) // p, q) != 1 for p in fs):
            return g
    raise ValueError


def subgroup(q, n):
    g = primitive_root(q)
    h = pow(g, (q - 1) // n, q)
    out, e = [], 1
    for _ in range(n):
        out.append(e); e = (e * h) % q
    return sorted(set(out))


def moments(q, k, domain, rmax):
    n = len(domain)
    qk = q ** k
    pows = [[pow(x, e, q) for e in range(k)] for x in domain]
    cws = [tuple(sum(c[e] * pows[i][e] for e in range(k)) % q for i in range(n))
           for c in itertools.product(range(q), repeat=k)]
    M = {r: {} for r in range(2, rmax + 1)}
    for u in itertools.product(range(q), repeat=n):
        hist = [0] * (n + 1)
        for cw in cws:
            hist[sum(map(eq, cw, u))] += 1
        support = [(j, aj) for j, aj in enumerate(hist) if aj]
        for r in range(2, rmax + 1):
            Mr = M[r]
            for combo in itertools.combinations_with_replacement(support, r):
                key = tuple(c[0] for c in combo)
                prod = 1
                for c in combo:
                    prod *= c[1]
                Mr[key] = Mr.get(key, 0) + prod
    return M


def diff(a, b):
    keys = set(a) | set(b)
    nd = w = 0; arg = None; pair = None
    for kk in keys:
        d = abs(a.get(kk, 0) - b.get(kk, 0))
        if d:
            nd += 1
            if d > w:
                w, arg, pair = d, kk, (a.get(kk, 0), b.get(kk, 0))
    return nd, w, arg, pair


def main():
    q, n, rmax = 13, 6, 4
    print(f"WF407 / T334-13-M3 : brute M2..M{rmax} at q={q}, n={n} (mu_{n}) -- {q**n} words")
    for k in (2, 3):
        print(f"\n--- k={k} ---")
        H = subgroup(q, n)
        MH = moments(q, k, H, rmax)
        Hset = set(H)
        g = next(x for x in range(2, q) if x not in Hset)
        coset = sorted(x * g % q for x in H)
        MC = moments(q, k, coset, rmax)
        rands = []
        for seed in range(1, 4):
            dom = sorted(random.Random(999 * q + seed).sample(range(1, q), n))
            rands.append((seed, moments(q, k, dom, rmax)))
        for r in range(2, rmax + 1):
            ndc, _, _, _ = diff(MH[r], MC[r])
            seps = [diff(MH[r], rm[r]) for _, rm in rands]
            null = 0
            for i in range(len(rands)):
                for jx in range(i + 1, len(rands)):
                    _, w, _, _ = diff(rands[i][1][r], rands[jx][1][r])
                    null = max(null, w)
            minsep = min(s[1] for s in seps)
            anyd = any(s[0] for s in seps)
            arg = seps[0][2]
            print(f"  M{r}: coset==sub: {ndc==0} | sub-vs-rand min|D|={minsep} "
                  f"(any diff {anyd}) | rand-cloud diam={null} | "
                  f"SEPARATES={minsep>null} | argmax cell {arg}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
