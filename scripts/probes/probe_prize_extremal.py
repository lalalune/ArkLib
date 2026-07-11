#!/usr/bin/env python3
"""
Does the Mann lead extend to GENERAL words? Is the monomial word extremal at
Johnson scale for the explainable-core count?

The supply must hold for EVERY word w. Mann controls the MONOMIAL word's
Johnson-scale fiber (= poly, coset-unions). If the monomial word is extremal
(max explainable-core count over all w at Johnson radius), Mann's poly bound
governs the supply. Test: max over words w of
  #{a-subsets T : exists deg<k codeword agreeing with w on T}
at Johnson radius a, compared to the monomial word's count, small smooth n.

k=2: explainable a-subset = a points (x_i,w_i) on a common line => count via
rich lines. Computable. Sweep many w (random, monomial, coset-structured).
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

def expl_cores_k2(D,p,w,a):
    """#{a-subsets on a common line} = sum_lines C(rich,a)."""
    n=len(D); lines=defaultdict(set)
    for i in range(n):
        for j in range(i+1,n):
            dx=(D[i]-D[j])%p
            if dx==0: continue
            A=((w[i]-w[j])*pow(dx,p-2,p))%p; B=(w[i]-A*D[i])%p
            lines[(A,B)].add(i); lines[(A,B)].add(j)
    return sum(math.comb(len(s),a) for s in lines.values() if len(s)>=a)

random.seed(3)
print("k=2 general-word extremality at Johnson scale: max explainable a-cores over w")
for n in (12,16,20,24):
    p=find_prime(n); D=smooth(p,n); k=2; aJ=math.ceil(math.sqrt(k*n))
    a=max(k+1,aJ-1)  # window-interior near Johnson
    best=0; bestkind=None
    cand=[]
    for _ in range(60): cand.append(("random",[random.randrange(p) for _ in range(n)]))
    # monomial words X^d
    for d in range(k,k+4): cand.append((f"monomial X^{d}",[pow(D[i],d,p) for i in range(n)]))
    # coset-structured: line A on evens, line B on odds
    for _ in range(20):
        cA=[random.randrange(p) for _ in range(2)]; cB=[random.randrange(p) for _ in range(2)]
        cand.append(("coset",[ (cA[0]*D[i]+cA[1])%p if i%2==0 else (cB[0]*D[i]+cB[1])%p for i in range(n)]))
    for kind,w in cand:
        c=expl_cores_k2(D,p,w,a)
        if c>best: best=c; bestkind=kind
    print(f"  n={n:3d} p={p} a={a}(Johnson~{aJ}): max expl a-cores = {best}  (achiever: {bestkind})  "
          f"[poly ref C(n,a)={math.comb(n,a)}]")
