#!/usr/bin/env python3
"""
The prize regime at minimal scale: constant rate (rho~1/2), dyadic n, IN-WINDOW
agreement. Brute-forceable since q^k is small for tiny n.

n=8,k=4 (rho=1/2): Johnson agree = ceil(sqrt(kn))=ceil(sqrt(32))=6; capacity
agree = k=4. Window (1-sqrt(rho),1-rho) => agreement (rho*n, sqrt(rho)*n) =
(4, 5.66) => a in {4,5} is IN the prize window (strictly between capacity and
Johnson). Measure the smooth-RS list there for structured + random words.
Also n=12,k=6 (rho=1/2), q=13: q^k=4.8M (heavier).

If the in-window list stays SMALL (poly/const) for dyadic smooth RS => beyond-
Johnson plausibly winnable. If it EXPLODES (super-poly in n) => the structured
domain kills beyond-Johnson (negative resolution). This is the actual open
question at the smallest honest scale.
"""
import itertools, math
from collections import Counter

def find_prime(n, lo):
    c=(lo//n+1)*n+1
    while True:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=n
def smooth(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,j,p) for j in range(n)]
    raise RuntimeError

def max_list_inwindow(p,n,k,a_lo,a_hi,trials):
    D=smooth(p,n)
    # precompute all codeword eval-vectors
    cws=[]
    for c in itertools.product(range(p),repeat=k):
        cws.append(tuple(sum(c[t]*pow(x,t,p) for t in range(k))%p for x in D))
    import random; rng=random.Random(9)
    best={a:0 for a in range(a_lo,a_hi+1)}
    bestw=None
    # structured words: agree with codeword A on a subgroup coset, B on the rest
    def struct():
        cA=[rng.randrange(p) for _ in range(k)]; cB=[rng.randrange(p) for _ in range(k)]
        return tuple((sum(cA[t]*pow(D[i],t,p) for t in range(k)) if i%2==0
                      else sum(cB[t]*pow(D[i],t,p) for t in range(k)))%p for i in range(n))
    # also: degree-(k) and degree-(k+1) monomial-ish words (the explosion witnesses)
    def monomialish(deg):
        c=[rng.randrange(p) for _ in range(deg+1)]
        return tuple(sum(c[t]*pow(x,t,p) for t in range(deg+1))%p for x in D)
    for _ in range(trials):
        for w in (struct(), monomialish(k), monomialish(k+1),
                  tuple(rng.randrange(p) for _ in range(n))):
            agc=[sum(1 for i in range(n) if cw[i]==w[i]) for cw in cws]
            for a in range(a_lo,a_hi+1):
                ls=sum(1 for g in agc if g>=a)
                if ls>best[a]: best[a]=ls
    return best

for (p_lo,n,k) in [(20,8,4),(20,12,6)]:
    p=find_prime(n,p_lo)
    aJ=math.ceil(math.sqrt(k*n)); 
    a_lo=k; a_hi=aJ
    if p**k > 6_000_000:
        print(f"n={n} k={k} p={p}: q^k={p**k} too big, skip"); continue
    best=max_list_inwindow(p,n,k,a_lo,a_hi,12 if n==8 else 4)
    rho=k/n
    print(f"n={n} k={k} rho={rho} p={p} Johnson_a={aJ} capacity_a={k}: "
          f"max in-window list per agreement: "
          f"{ {a:best[a] for a in range(a_lo,a_hi+1)} }")
