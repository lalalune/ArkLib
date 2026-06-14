import numpy as np
from itertools import combinations
from sympy import primerange

def run(n, m, r, bands, max_subsets=2_000_000):
    HALF = n//2
    size = r*m
    gap = [i for i in range(1, 2*m) if i != m]
    # enumerate subsets, build coeff matrices M[i]: (Nsub, HALF)
    from math import comb
    Nsub = comb(n, size)
    if Nsub > max_subsets:
        print(f"n={n} m={m} r={r}: C(n,size)={Nsub} too big, skip"); return
    subs = list(combinations(range(n), size))
    needed = sorted(set(gap + [m]))
    M = {i: np.zeros((Nsub, HALF), dtype=np.int64) for i in needed}
    for s_idx, S in enumerate(subs):
        for i in needed:
            for comb_i in combinations(S, i):
                T = sum(comb_i) % n
                if T < HALF: M[i][s_idx, T] += 1
                else:        M[i][s_idx, T-HALF] -= 1
    # C count
    zero_mask = np.ones(Nsub, dtype=bool)
    for i in gap:
        zero_mask &= (M[i]==0).all(axis=1)
    C_em = M[m][zero_mask]
    C_count = len({tuple(row) for row in C_em})
    C_valid = int(zero_mask.sum())

    def prim_root(p):
        e = (p-1)//n
        for a in range(2, p):
            g = pow(a, e, p)
            if pow(g, n, p)==1 and pow(g, n//2, p)==p-1:
                return g
        return None

    worst = 0; worst_p = None; max_valid = 0
    total_primes = 0
    for lo, hi in bands:
        for p in primerange(lo, hi):
            if p % n != 1: continue
            g = prim_root(p)
            if g is None: continue
            total_primes += 1
            powv = np.array([pow(g, l, p) for l in range(HALF)], dtype=np.int64)
            valid = np.ones(Nsub, dtype=bool)
            for i in gap:
                valid &= ((M[i] @ powv) % p == 0)
            em = (M[m][valid] @ powv) % p
            cnt = len(set(em.tolist()))
            nv = int(valid.sum())
            if cnt > worst: worst, worst_p = cnt, p
            if nv > max_valid: max_valid = nv
    flag = "  <<< INFLATION (REFUTES exact deltastar)" if worst > C_count else "  ok (q-indep)"
    print(f"n={n} m={m} r={r} |S|={size} gap={gap}: C: valid_configs={C_valid} distinct_em(=|H^+r|)={C_count} "
          f"| F_p over {total_primes} primes: worst #bad={worst}@p={worst_p}, max valid_configs={max_valid}{flag}")

# bands: include past exponential threshold for small n
run(8,  2, 2, [(17,5000),(60000,80000)])
run(8,  2, 3, [(17,5000),(60000,80000)])
run(16, 2, 4, [(17,4000),(65000,75000)])
run(16, 4, 2, [(17,4000),(65000,75000)])
run(16, 4, 3, [(17,4000)])
run(32, 2, 3, [(97,4000)])
run(32, 2, 4, [(97,2000)])
run(32, 4, 2, [(97,2000)])
