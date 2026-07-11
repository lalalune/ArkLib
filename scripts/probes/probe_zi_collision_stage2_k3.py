# Stage 2, k = 3: positions x1<x2<x3 distinct mod N; full per-residue Z[i] system with
# the REAL exponents (D_i = 2x_i, S_ij = x_i + x_j mod 2N, residue = mod N, eps = div N).
# Profile (3,3,2) in any order. If nothing survives at several N, the 3-class profile is
# dead at those scales (and the hand argument covers general N).
from itertools import combinations, permutations

mu4 = [(1,0),(0,1),(-1,0),(0,-1)]
def gmul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def gadd(a,b): return (a[0]+b[0], a[1]+b[1])
def gsum(l):
    r=(0,0)
    for x in l: r=gadd(r,x)
    return r
def e2(B):
    r=(0,0)
    for p in combinations(B,2): r=gadd(r,gmul(*p))
    return r
I=(0,1)

def itw(e,c): return c if e==0 else gmul(I,c)

def survives(N):
    cnt = 0
    subs = {s:[list(c) for c in combinations(mu4,s)] for s in (2,3)}
    for xs in combinations(range(N),3):
        for perm in set(permutations((3,3,2))):
            for B1 in subs[perm[0]]:
                for B2 in subs[perm[1]]:
                    for B3 in subs[perm[2]]:
                        Bs=[B1,B2,B3]
                        terms = []
                        for i in range(3):
                            e = (2*xs[i]) % (2*N)
                            terms.append((e % N, e // N, e2(Bs[i])))
                        for i,j in combinations(range(3),2):
                            e = (xs[i]+xs[j]) % (2*N)
                            terms.append((e % N, e // N, gmul(gsum(Bs[i]),gsum(Bs[j]))))
                        from collections import defaultdict
                        acc = defaultdict(lambda: (0,0))
                        for r,eps,c in terms:
                            acc[r] = gadd(acc[r], itw(eps,c))
                        if all(v==(0,0) for v in acc.values()):
                            cnt += 1
    return cnt

for N in (4, 8, 16):
    print(f"N={N} (n={4*N}): surviving (x,B) configs with 3 classes:", survives(N))
