# Stage 2, all class-counts k = 3..8 (sizes <= 3 summing to 8): exhaustive position+content
# check of the per-residue Z[i] system. Zero survivors at a scale = no coset-free balanced
# 8-set with that class structure at that scale.
from itertools import combinations, permutations, product
from collections import defaultdict
import sys

mu4 = [(1,0),(0,1),(-1,0),(0,-1)]
def gmul(a,b): return (a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0])
def gadd(a,b): return (a[0]+b[0], a[1]+b[1])
def gsum(l):
    r=(0,0)
    for x in l: r=gadd(r,x)
    return r
def e2v(B):
    r=(0,0)
    for p in combinations(B,2): r=gadd(r,gmul(*p))
    return r
I=(0,1)
def itw(e,c): return c if e==0 else gmul(I,c)

subs = {s:[ (list(c), gsum(c), e2v(c)) for c in combinations(mu4,s)] for s in (1,2,3)}

def profiles(total, maxpart, k):
    if k == 0:
        if total == 0: yield []
        return
    for p in range(min(maxpart, total), 0, -1):
        for rest in profiles(total - p, p, k - 1):
            yield [p] + rest

def check(N, k):
    total_surv = 0
    for prof in profiles(8, 3, k):
        size_perms = set(permutations(prof))
        for xs in combinations(range(N), k):
            for sp in size_perms:
                # choose contents per class
                for choice in product(*[range(len(subs[s])) for s in sp]):
                    sig = [subs[sp[i]][choice[i]] for i in range(k)]
                    acc = defaultdict(lambda: (0,0))
                    ok = True
                    for i in range(k):
                        e = (2*xs[i]) % (2*N)
                        acc[e % N] = gadd(acc[e % N], itw(e // N, sig[i][2]))
                    for i in range(k):
                        for j in range(i+1, k):
                            e = (xs[i]+xs[j]) % (2*N)
                            acc[e % N] = gadd(acc[e % N],
                                itw(e // N, gmul(sig[i][1], sig[j][1])))
                    if all(v == (0,0) for v in acc.values()):
                        total_surv += 1
    return total_surv

for N in (4, 8):
    for k in range(3, 9):
        if k > N: continue
        print(f"N={N} k={k}: survivors = {check(N, k)}", flush=True)
