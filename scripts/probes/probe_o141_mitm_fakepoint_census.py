# O141: MITM census via the FAKE-POINT characterization.
# e_2(A)=...=e_c(A)=0  <=>  p_j(A) = p_1(A)^j for j=2..c  ("A masquerades as the point
# t = p_1(A) through its first c moments"; the bad scalar is -t).
# Exact counts at n=32 (k=8, rate 1/4) for a = 10..14 (c = a-k-... constraints e_2..e_{a-8}),
# p in {97, 193}. GATES: a=10,11 must reproduce the exhaustive O140 counts.
from itertools import combinations
import sys
def subgroup(p, n):
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p-1):
            x = x*g % p; elems.add(x)
        if len(elems) == p-1:
            gen = pow(g, (p-1)//n, p)
            H = sorted(set(pow(gen, i, p) for i in range(n)))
            assert len(H) == n
            return H
def census(p, H, a, c):
    # count a-subsets A with p_j(A) = p_1(A)^j for j=2..c ; also distinct -p_1 values
    n = len(H)
    H1, H2 = H[:n//2], H[n//2:]
    # dictionaries: for each size s, map (p_1..p_c) -> count
    from collections import defaultdict
    def vecs(half, s):
        d = defaultdict(int)
        for A in combinations(half, s):
            v = tuple(sum(pow(x, j, p) for x in A) % p for j in range(1, c+1))
            d[v] += 1
        return d
    D1 = {s: vecs(H1, s) for s in range(0, a+1) if s <= len(H1) and a-s <= len(H2)}
    D2 = {s: vecs(H2, s) for s in range(0, a+1) if s <= len(H2) and a-s <= len(H1)}
    total = 0
    lams = set()
    lamcount = defaultdict(int)
    for t in range(p):
        tv = [pow(t, j, p) for j in range(1, c+1)]
        cnt_t = 0
        for s1 in D1:
            s2 = a - s1
            if s2 not in D2: continue
            for v1, m1 in D1[s1].items():
                key = tuple((tv[j] - v1[j]) % p for j in range(c))
                m2 = D2[s2].get(key, 0)
                if m2: cnt_t += m1 * m2
        if cnt_t:
            total += cnt_t
            lams.add((-t) % p)
    return total, len(lams)
n, k = 32, 8
for p in (97, 193):
    H = subgroup(p, n)
    for a in (10, 11, 12, 13, 14):
        c = a - k  # constraints e_2..e_c, i.e. moments up to c
        tot, nl = census(p, H, a, c)
        print(f"p={p} a={a} (c={c}): qualifying={tot}  census(distinct -t)={nl}", flush=True)
