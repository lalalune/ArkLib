from itertools import combinations
from collections import Counter

def balanced(A, n, h):
    c = Counter((A[i]+A[j]) % n for i in range(len(A)) for j in range(i+1,len(A)))
    return all(c[t] == c[(t+h) % n] for t in range(n))

for n in (8, 16, 32):
    h = n//2; q = n//4
    sols = [A for A in combinations(range(n), 5) if balanced(A, n, h)]
    def is_coset_plus_point(A):
        S = set(A)
        for x in A:
            coset = {x, (x+q)%n, (x+h)%n, (x+q+h)%n}
            if coset <= S:
                return True
        return False
    ok = all(is_coset_plus_point(A) for A in sols)
    pred = (n//4)*(n-4)
    print(f"n={n}: balanced-5-sets={len(sols)} pred={pred} match={len(sols)==pred} all-coset-shape={ok}")
