from itertools import combinations
from collections import Counter

n, h, q = 16, 8, 4
def balanced(A):
    c = Counter((A[i]+A[j]) % n for i in range(len(A)) for j in range(i+1,len(A)))
    return all(c[t] == c[(t+h) % n] for t in range(n))

cosets = [frozenset({x, (x+q)%n, (x+h)%n, (x+q+h)%n}) for x in range(q)]
sols8 = [frozenset(A) for A in combinations(range(n), 8) if balanced(A)]
sols4 = [frozenset(A) for A in combinations(range(n), 4) if balanced(A)]
sols4set = set(sols4)

cls = Counter()
for A in sols8:
    full = [C for C in cosets if C <= A]
    if len(full) == 2:
        cls['two-cosets'] += 1
    elif len(full) == 1:
        rest = A - full[0]
        cls['coset+balanced4' if frozenset(rest) in sols4set else 'coset+NONbalanced4'] += 1
    else:
        cls['no-coset'] += 1
print(dict(cls), "total", len(sols8))
# for the no-coset ones: their e1 values vs census(4)
def e1fold(A):
    v = [0]*h
    for i in A:
        if i < h: v[i] += 1
        else: v[i-h] -= 1
    return tuple(v)
c4 = {e1fold(A) for A in sols4}
nocoset = [A for A in sols8 if not any(C <= A for C in cosets)]
print("no-coset count:", len(nocoset), "values in census4:", sum(1 for A in nocoset if e1fold(A) in c4), "distinct:", len({e1fold(A) for A in nocoset}))
# sample a no-coset solution
if nocoset: print("sample:", sorted(nocoset[0]))
