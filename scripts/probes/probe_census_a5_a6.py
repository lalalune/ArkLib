#!/usr/bin/env python3
"""Item 12: char-0 census closed forms N_a(n) for a=5,6 — count a-subsets A of the
2^m-th roots of unity with e2(A) = 0 in char 0, computed EXACTLY in Z[zeta_{2^m}]
via folding (zeta^{N} = -1, N = 2^{m-1}): g^t -> (+/-) basis e_{t mod N}."""
import itertools, sys
from itertools import combinations

def count(m, a):
    n = 1 << m
    N = n >> 1
    # pairvec[i][j] = folded vector of g^{i+j} as tuple index/sign
    def fold(t):
        t %= n
        if t < N: return (t, 1)
        return (t - N, -1)
    cnt = 0
    sols = []
    for A in combinations(range(n), a):
        vec = [0]*N
        for x, y in combinations(A, 2):
            idx, s = fold(x + y)
            vec[idx] += s
        if not any(vec):
            cnt += 1
            if len(sols) < 4: sols.append(A)
    return cnt, sols

for a in (5, 6):
    for m in (3, 4, 5):
        c, sols = count(m, a)
        print(f"a={a} n={1<<m}: N = {c}   examples: {sols[:2]}", flush=True)
# forecast scale for a=5, n=64
c, sols = count(6, 5)
print(f"a=5 n=64: N = {c}", flush=True)
