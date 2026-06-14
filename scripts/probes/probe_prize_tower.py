#!/usr/bin/env python3
"""
Brick-by-brick disposition of S2 (tower-telescoped supply recursion):
does the 2-adic tower step GROW or SHRINK the list?

mu_{2n} contains mu_n as the index-2 subgroup (the squares). A word w on
mu_{2n} restricts to two mu_n-cosets (even/odd powers). S2 conjectures the
mu_{2n} list bound telescopes from the mu_n lists. Test the DIRECTION:
compare max list size on mu_{2n} to the max on a single mu_n coset, same
code dim k and a window radius. If mu_{2n} list <= ~2x mu_n list
(sub-multiplicative => telescope works), S2 has legs. If it grows faster
(super-multiplicative => coset-union explosion), S2 is REFUTED (proves the
wrong direction, consistent with not_explainableCoreSupply_exponential).

Brute-forceable: small q^k. n in {8,16}, k=2,3.
"""
import itertools, math
from collections import Counter

def find_prime(N, lo):
    c=(lo//N+1)*N+1
    while True:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=N
def smooth(p,N):
    for g in range(2,p):
        h=pow(g,(p-1)//N,p)
        if pow(h,N,p)==1 and all(pow(h,j,p)!=1 for j in range(1,N)):
            return [pow(h,j,p) for j in range(N)]
    raise RuntimeError
def peval(c,x,p):
    r=0
    for a in reversed(c): r=(r*x+a)%p
    return r
def maxlist(D,p,k,a,trials,rng):
    n=len(D); best=0
    cws=[tuple(peval(c,x,p) for x in D) for c in itertools.product(range(p),repeat=k)]
    for _ in range(trials):
        # structured word: low-deg on each parity coset
        cA=[rng.randrange(p) for _ in range(k+1)]; cB=[rng.randrange(p) for _ in range(k+1)]
        w=[ (peval(cA,D[i],p) if i%2==0 else peval(cB,D[i],p)) for i in range(n)]
        ls=sum(1 for cw in cws if sum(1 for i in range(n) if cw[i]==w[i])>=a)
        best=max(best,ls)
    return best

import random
print("comparing list(mu_{2n}) vs list(mu_n), same k, window radius scaled:")
for (k, N2) in [(2,16),(3,16),(2,32),(3,8)]:
    Nn=N2//2
    # need both N2 and Nn dividing p-1: pick p with N2 | p-1
    p=find_prime(N2, 30)
    if p**k > 5_000_000: 
        print(f"  k={k} n={N2}: q^k too big"); continue
    D2=smooth(p,N2); Dn=smooth(p,Nn)
    # window radius ~ between capacity k and Johnson sqrt(k*N)
    a2=math.ceil(math.sqrt(k*N2)); an=math.ceil(math.sqrt(k*Nn))
    # use radius just inside window (Johnson-1)
    l2=maxlist(D2,p,k,max(k+1,a2-1),40,random.Random(1))
    ln=maxlist(Dn,p,k,max(k+1,an-1),40,random.Random(2))
    ratio = l2/ln if ln else float('inf')
    print(f"  k={k} mu_{N2}(a={max(k+1,a2-1)}) list={l2}  vs  mu_{Nn}(a={max(k+1,an-1)}) list={ln}  "
          f"ratio={ratio:.2f}  {'GROWS(>2 => S2 refuted)' if ratio>2.01 else 'sub-mult (S2 plausible)'}")
