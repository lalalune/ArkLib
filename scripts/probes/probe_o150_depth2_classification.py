# O150 depth-2 classification probe (companion to CensusTowerDescent.lean):
# stride-4 system on mu_16 (stack (X^8,X^4), k=1): band e1,e2,e3,e5,e6,e7 = 0 over
# 8-subsets. Field-independent solutions = EXACTLY the 6 unions of two quartic fibers,
# with ZERO halo at p in {97,113,193,257} (count = 6 at every prime).
from itertools import combinations
def subgroup_gen(p, n):
    for g in range(2, p):
        x, elems = 1, set()
        for _ in range(p-1):
            x = x*g % p; elems.add(x)
        if len(elems) == p-1:
            return pow(g, (p-1)//n, p)
def esymms(elems, mmax, p):
    pws = [sum(pow(x, j, p) for x in elems) % p for j in range(1, mmax+1)]
    e = [1]
    for j in range(1, mmax+1):
        s = 0
        for i in range(1, j+1):
            s += (-1)**(i-1) * e[j-i] * pws[i-1]
        e.append(s * pow(j, p-2, p) % p)
    return e[1:]
sols = {}
for p in (97, 113, 193, 257):
    gen = subgroup_gen(p, 16)
    H = [pow(gen, i, p) for i in range(16)]
    S = set()
    for idx in combinations(range(16), 8):
        e = esymms([H[i] for i in idx], 7, p)
        if all(e[j] == 0 for j in [0, 1, 2, 4, 5, 6]):
            S.add(idx)
    assert len(S) == 6, (p, len(S))
    sols[p] = S
common = set.intersection(*sols.values())
fibers = set(tuple(sorted([j + 4*l for j in T for l in range(4)]))
             for T in combinations(range(4), 2))
assert common == fibers and len(common) == 6
print("depth-2: 6 = 6 at all primes, zero halo, = quartic-fiber unions  [OK]")
