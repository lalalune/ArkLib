from itertools import combinations
from collections import Counter
n, h, q = 16, 8, 4
def balanced(A):
    c = Counter((A[i]+A[j]) % n for i in range(len(A)) for j in range(i+1,len(A)))
    return all(c[t] == c[(t+h) % n] for t in range(n))
cosets = [frozenset({x,(x+q)%n,(x+h)%n,(x+q+h)%n}) for x in range(q)]
bal = {a: [frozenset(A) for A in combinations(range(n), a) if balanced(A)] for a in (4,5,9,12,13)}
bal4, bal5 = set(bal[4]), set(bal[5])
def core_decomposes(A):
    # try stripping any subset of full cosets; core must be balanced 4/5-set, empty, or a coset itself
    full = [C for C in cosets if C <= A]
    from itertools import chain
    for k in range(len(full), -1, -1):
        for sel in combinations(full, k):
            rest = frozenset(A) - frozenset().union(*sel) if sel else frozenset(A)
            if len(rest) == 0 and len(set(sel)) * 4 == len(A): return True
            if len(rest) == 4 and rest in bal4 and 4 + 4*len(sel) == len(A): return True
            if len(rest) == 5 and rest in bal5 and 5 + 4*len(sel) == len(A): return True
    return False
for a in (9, 12, 13):
    sols = bal[a]
    ok = sum(1 for A in sols if core_decomposes(A))
    print(f"a={a}: balanced={len(sols)}, conjecture-decomposable={ok}, exceptions={len(sols)-ok}")
