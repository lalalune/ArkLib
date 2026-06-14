# a=4 depth-1 census: predicted |{-e1(A) : A qualifying}| = n^2/4 - n + 1, exact in Z[zeta_n]
from itertools import combinations

def red(v, half):
    out = [0]*half
    for i, c in enumerate(v):
        q, r = divmod(i, half)
        out[r] += c if q % 2 == 0 else -c
    return out

def run(m):
    n = 2**m; half = n//2; h = half
    # qualifying 4-subsets via balance (structure law verified earlier); compute e1 in Z[X]/(X^half+1)
    from collections import Counter
    def balanced(A):
        c = Counter((A[i]+A[j]) % n for i in range(4) for j in range(i+1,4))
        return all(c[t] == c[(t+h) % n] for t in range(n))
    sums = set()
    count_q = 0
    for A in combinations(range(n), 4):
        if balanced(A):
            count_q += 1
            v = [0]*n
            for i in A: v[i] += 1
            sums.add(tuple(red(v, half)))
    pred = n*n//4 - n + 1
    print(f"n={n}: qualifying={count_q} (N4 pred {n*(n-3)//4}), distinct e1 = {len(sums)}, predicted {pred}, match={len(sums)==pred}")

for m in range(2, 6):
    run(m)
