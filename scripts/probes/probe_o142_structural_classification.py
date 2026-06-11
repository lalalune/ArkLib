# O142 APEX PROBE: classify field-independent solutions of the gap-band system.
# Instance: stack (X^8, X^6) on mu_16, code deg < 5 (KKH26 r=4, m=2 shape).
# Band (badScalar_iff_gapBand): e1(A) = 0, pivot at coeff 6, e3(A) = 0.
# VERDICT (exact, 5 primes): solutions = 102 @ p=17 (70 + 32 halo), exactly 70 at
# p in {97,113,193,257}; intersection over all primes = 70 = EXACTLY the antipodal
# 4-fiber unions (A = preimage of a 4-subset of mu_8 under x -> x^2).
#   => the field-independent solutions are PRECISELY the fiber unions, and at p >= 97
#      there is no halo at this instance: structural core = entire census.
from itertools import combinations
def subgroup_gen(p, n):
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p-1):
            x = x*g % p; elems.add(x)
        if len(elems) == p-1:
            return pow(g, (p-1)//n, p)
n, A_size = 16, 8
primes = [17, 97, 113, 193, 257]
sols = {}
for p in primes:
    gen = subgroup_gen(p, n)
    H = [pow(gen, i, p) for i in range(n)]
    S = set()
    for idx in combinations(range(n), A_size):
        elems = [H[i] for i in idx]
        if sum(elems) % p: continue
        if sum(pow(e, 3, p) for e in elems) % p == 0:
            S.add(idx)
    sols[p] = S
common = set.intersection(*sols.values())
fiber_unions = set()
for T in combinations(range(8), 4):
    fiber_unions.add(tuple(sorted(list(T) + [i + 8 for i in T])))
assert len(sols[17]) == 102 and all(len(sols[p]) == 70 for p in primes[1:])
assert common == fiber_unions and len(common) == 70
print("counts:", {p: len(sols[p]) for p in primes})
print("field-independent solutions = fiber unions (70): CONFIRMED")
