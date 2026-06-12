# a=9 coset-free balanced sets at n=32 via coset-class decomposition:
# classes = 8 cosets of K = {0,8,16,24}; contents B_i subset of the coset (as mu4-labels),
# sizes <= 3 (coset-free), sum 9. Balance <=> e2 = 0 in Z[zeta_32]; work in the fold
# Z[X]/(X^16+1) exactly.
from itertools import combinations, product
from collections import Counter

n, N = 32, 8  # N = n/4 classes; coset of x: {x, x+8, x+16, x+24}
def balanced(A):
    h = n//2
    c = Counter((a+b) % n for i,a in enumerate(A) for b in A[i+1:])
    return all(c[t] == c[(t+h) % n] for t in range(n))

# enumerate via classes to keep it feasible: choose sizes per class summing to 9 (<=3),
# then content choices (positions within coset = which of {0,1,2,3} quarter-offsets)
def gen_sets():
    # recursive over classes 0..7
    def rec(cls, remaining, chosen):
        if cls == N:
            if remaining == 0:
                yield chosen
            return
        maxs = min(3, remaining)
        for s in range(0, maxs+1):
            if remaining - s > 3*(N-cls-1):
                continue
            for sub in combinations(range(4), s):
                yield from rec(cls+1, remaining-s, chosen + [(cls, q) for q in sub])
    yield from rec(0, 9, [])

cnt = 0
sols = []
for config in gen_sets():
    A = sorted(c + 8*q for (c,q) in config)
    if balanced(A):
        cnt += 1
        sols.append(tuple(A))
print("coset-free balanced 9-sets at n=32:", cnt)
# how many are doubles of n=16 sets (all elements even)?
doubles = [A for A in sols if all(x % 2 == 0 for x in A)]
print("all-even (= doubled from n=16):", len(doubles))
# orbit structure under rotation+reflection
def rot(A): return tuple(sorted((x+1) % n for x in A))
def refl(A): return tuple(sorted((-x) % n for x in A))
solset = set(sols); seen = set(); orbits = []
for A in sols:
    if A in seen: continue
    O = set(); B = A
    for _ in range(n):
        O.add(B); O.add(refl(B)); B = rot(B)
    O &= solset
    seen |= O
    orbits.append(len(O))
print("orbits (sizes):", sorted(orbits))

# exact census at n=32: values of -e1 over ALL balanced 9-sets = decomposables (coset +
# balanced-5: values = a5 orbit) + coset-free; fold e1 into Z[X]/(X^16+1)
def e1fold(A):
    v = [0]*16
    for x in A:
        if x < 16: v[x] += 1
        else: v[x-16] -= 1
    return tuple(v)
vals_free = {e1fold(A) for A in sols}
# a5-orbit values at n=32: -g^v over v: as folds of single exponents
orbit = set()
for v in range(n):
    w = [0]*16
    if v < 16: w[v] += 1
    else: w[v-16] -= 1
    orbit.add(tuple(w))
print("coset-free value count:", len(vals_free))
print("overlap with a5-orbit:", len(vals_free & orbit))
print("TOTAL census(9, 32) =", len(vals_free | orbit))
