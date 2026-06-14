"""Fully independent (this session, from scratch) per-class mod-p count:
dict-based MITM, conventions re-derived from construct_n64.py only.
Counts 15-subsets B of Z_32\O with sum_{c in B} zeta^{2c} == z* - e2(x) - e1(O_z) mod p.
(Mod-p only: the char-0 side of the comparison comes from falsify.c / audit_sweep64.)"""
from itertools import combinations
from collections import Counter

def run(P, g0, O, m, expect_modp):
    n, s = 64, 32
    h = pow(g0, (P-1)//n, P)
    H = [pow(h, i, P) for i in range(n)]
    assert len(set(H)) == n and H[s] == P-1
    G = [H[(2*c) % n] for c in range(s)]
    ZS = H[16]; assert ZS*ZS % P == P-1
    d = (0, m & 1, (m >> 1) & 1)
    a = [O[i] + s*d[i] for i in range(3)]
    x = [H[ai] for ai in a]
    e2 = sum(x[i]*x[j] for i in range(3) for j in range(i+1, 3)) % P
    tgt = (ZS - e2 - sum(G[o] for o in O)) % P
    cand = [c for c in range(s) if c not in O]
    L, Rh = cand[:14], cand[14:]
    # left: all (size, sum) counters
    lt = {}
    for k in range(16):
        for sub in combinations(L, k):
            key = (k, sum(G[c] for c in sub) % P)
            lt[key] = lt.get(key, 0) + 1
    cnt = 0
    for k2 in range(16):
        for sub in combinations(Rh, k2):
            sR = sum(G[c] for c in sub) % P
            cnt += lt.get((15-k2, (tgt - sR) % P), 0)
    print(f"p={P} O={O} m={m}: independent dict-MITM modp count = {cnt} "
          f"(expect {expect_modp}) {'OK' if cnt==expect_modp else 'FAIL'}")
    assert cnt == expect_modp
run(2013265921, 31, (5,20,31), 2, 10)
run(2013265921, 31, (14,17,21), 1, 1)
run(3221225473, 5, (9,12,14), 1, 15)
run(3221225473, 5, (8,10,15), 3, 10)
print("INDEPENDENT REPRODUCTION OK")
