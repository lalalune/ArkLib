from itertools import combinations
from collections import Counter
n, h, q = 16, 8, 4
def balanced(A):
    c = Counter((A[i]+A[j]) % n for i in range(len(A)) for j in range(i+1,len(A)))
    return all(c[t] == c[(t+h) % n] for t in range(n))
cosets = [frozenset({x,(x+q)%n,(x+h)%n,(x+q+h)%n}) for x in range(q)]
sols9 = [frozenset(A) for A in combinations(range(n), 9) if balanced(A)]
exc = [A for A in sols9 if not any(C <= A for C in cosets)]
print(f"exceptional: {len(exc)}")
# structure stats: antipodal pairs count, coset-intersection profile, complement
for A in exc[:4]:
    pairs = [(x,(x+h)%n) for x in A if (x+h)%n in A and x < (x+h)%n]
    prof = sorted(len(A & C) for C in cosets)
    comp = sorted(set(range(n)) - A)
    print(sorted(A), "| pairs:", len(pairs), "| coset profile:", prof, "| complement:", comp)
# complements: 7-sets; are complements related to balanced structures?
comps = [frozenset(range(n)) - A for A in exc]
# check: complement 7-sets, p1^2 = -p2 quadric? compute in Z[zeta16] fold (deg 8)
def fold_vec(exps, mult=1):
    v = [0]*8
    for e in exps:
        e %= 16
        if e < 8: v[e] += mult
        else: v[e-8] -= mult
    return v
def addv(u,v): return [a+b for a,b in zip(u,v)]
def mulv(u,v):
    out = [0]*15
    for i,a in enumerate(u):
        for j,b in enumerate(v): out[i+j] += a*b
    w = out[:8]
    for i in range(8,15): w[i-8] -= out[i]
    return w
cnt = 0
for T in comps:
    p1 = fold_vec(T)
    p2 = fold_vec([2*e for e in T])
    lhs = mulv(p1,p1)
    if all(a == -b for a,b in zip(lhs, p2)): cnt += 1
print(f"complements (7-sets) satisfying p1^2 = -p2: {cnt}/{len(comps)}")
# orbit structure of the exceptional family under rotation+reflection
def rot(A): return frozenset((x+1)%n for x in A)
def refl(A): return frozenset((-x)%n for x in A)
seen, orbits = set(), 0
for A in exc:
    if A in seen: continue
    orbits += 1
    O = set()
    B = A
    for _ in range(n):
        O.add(B); O.add(refl(B)); B = rot(B)
    seen |= {x for x in O if x in set(exc)}
print(f"rotation+reflection orbits: {orbits}")
