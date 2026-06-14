#!/usr/bin/env python3
"""
The key distinction: explainable-CORE count (subsets) vs LIST size (codewords)
at Johnson scale, for the extremal coset word.

ExplainableCoreSupply bounds the CORE count = #{a-subsets explainable by some
codeword} = sum_codewords C(agreement, a) -- one rich codeword (n/2 pts on a
line) contributes C(n/2,a) ~ EXPONENTIAL. But delta*/bad-scalars depend on the
LIST = #codewords agreeing on >= a points, which can be SMALL even when cores
are huge. Measure BOTH for the coset word (k=2), to show: cores exp, list poly.
=> the supply-via-core-count route is intrinsically lossy; the list is the
right delta*-relevant quantity, and it's poly at Johnson scale.
"""
import itertools, math, random
from collections import defaultdict

def find_prime(n, lo=50):
    c=(lo//n+1)*n+1
    while True:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=n
def smooth(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)]
    raise RuntimeError

def cores_and_list_k2(D,p,w,a):
    n=len(D); lines=defaultdict(set)
    for i in range(n):
        for j in range(i+1,n):
            dx=(D[i]-D[j])%p
            if dx==0: continue
            A=((w[i]-w[j])*pow(dx,p-2,p))%p; B=(w[i]-A*D[i])%p
            lines[(A,B)].add(i); lines[(A,B)].add(j)
    rich=[len(s) for s in lines.values() if len(s)>=a]
    cores=sum(math.comb(r,a) for r in rich)
    listsize=len(rich)   # # codewords (lines) agreeing on >= a points
    return cores, listsize, max(rich,default=0)

random.seed(1)
print("coset word, k=2: CORE count (subsets) vs LIST size (codewords) at Johnson scale")
print("n    a   | cores(subsets)   list(codewords)   max-agreement")
for n in (12,16,20,24,28,32):
    p=find_prime(n); D=smooth(p,n); k=2; aJ=math.ceil(math.sqrt(k*n)); a=max(k+1,aJ-1)
    # coset word: line A on evens, line B on odds (maximizes both)
    best=(0,0,0)
    for _ in range(40):
        cA=[random.randrange(p) for _ in range(2)]; cB=[random.randrange(p) for _ in range(2)]
        w=[ (cA[0]*D[i]+cA[1])%p if i%2==0 else (cB[0]*D[i]+cB[1])%p for i in range(n)]
        cr,ls,mx=cores_and_list_k2(D,p,w,a)
        if cr>best[0]: best=(cr,ls,mx)
    print(f"{n:3d}  {a:3d}  | cores={best[0]:8d}   list={best[1]:4d}   max-agree={best[2]}  "
          f"(coset size n/2={n//2})")
