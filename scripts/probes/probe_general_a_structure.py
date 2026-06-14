# Structure of balanced a-sets (char-0 depth-1 census) for a = 5, 8 (first rows where
# the parity law is silent beyond a = 4).
from itertools import combinations
from collections import Counter

def balanced(A, n, h):
    c = Counter((A[i]+A[j]) % n for i in range(len(A)) for j in range(i+1,len(A)))
    return all(c[t] == c[(t+h) % n] for t in range(n))

def has_antipodal(A, n, h):
    S = set(A)
    return [x for x in A if (x+h) % n in S and x < (x+h) % n or ((x+h)%n in S and (x+h)%n < x and False)]

def antipodal_pairs(A, n, h):
    S = set(A)
    return [(x, (x+h)%n) for x in A if (x+h)%n in S and x < (x+h)%n]

def couple_structure(A, n, h):
    """check: A = {x,x+h} U couples symmetric about x, for some antipodal pair"""
    S = set(A)
    out = []
    for (x, xh) in antipodal_pairs(A, n, h):
        rest = [u for u in A if u != x and u != xh]
        used = set()
        ok = True
        for u in rest:
            if u in used: continue
            v = (2*x - u) % n
            if v in S and v != u and v not in (x, xh):
                used.add(u); used.add(v)
            else:
                ok = False; break
        if ok and len(used) == len(rest):
            out.append(x)
    return out

for n, alist in [(16, [5, 8]), (32, [5])]:
    h = n // 2
    for a in alist:
        sols = [A for A in combinations(range(n), a) if balanced(A, n, h)]
        nap = sum(1 for A in sols if not antipodal_pairs(A, n, h))
        cs = sum(1 for A in sols if couple_structure(A, n, h))
        # census values (exact char-0 via folding e1)
        half = n//2
        def e1fold(A):
            v = [0]*half
            for i in A:
                if i < half: v[i] += 1
                else: v[i-half] -= 1
            return tuple(v)
        census = len({e1fold(A) for A in sols})
        print(f"n={n} a={a}: balanced={len(sols)}, no-antipodal-pair={nap}, "
              f"couple-ansatz={cs}, census(e1)={census}")
