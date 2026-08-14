#!/usr/bin/env python3
"""HONESTY CHECK on the +11.6% crossover excess (n=32,r=4,Nr/p~0.9): real arithmetic, or
birthday-variance? Test MULTIPLE primes at Nr/p in [0.7,1.3] and also a RANDOM-SET control
(same cardinality random subset of F_p*, NOT mu_n) -- if the excess is the SAME for random sets,
it's birthday not arithmetic. If mu_n excess > random, it's thin-subgroup structure (door-iv signal)."""
import math, random
from itertools import combinations
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    i=3
    while i*i<=x:
        if x%i==0: return False
        i+=2
    return True
def primes_for(n, lo_ratio, hi_ratio, Nr, count=6):
    # want p in [Nr/hi, Nr/lo], p ≡ 1 mod n, odd m
    out=[]
    plo=int(Nr/hi_ratio); phi=int(Nr/lo_ratio)
    k=max(2,plo//n)
    while len(out)<count and k*n+1 <= phi*2:
        p=k*n+1
        if p>=plo and p<=phi and isprime(p) and ((p-1)//n)%2==1:
            out.append(p)
        k+=1
    return out
def subgroup(n,p):
    def pr(g):
        x=p-1; fs=set(); d=2
        while d*d<=x:
            while x%d==0: fs.add(d); x//=d
            d+=1
        if x>1: fs.add(x)
        return all(pow(g,(p-1)//q,p)!=1 for q in fs)
    g=2
    while not pr(g): g+=1
    h=pow(g,(p-1)//n,p); S=[]; c=1
    for _ in range(n): S.append(c); c=c*h%p
    return S
def Nr_cf(n,r):
    m=n//2; tot=0; k=r%2; kmax=min(r,2*m-r)
    while k<=kmax:
        if k<=m: tot+=math.comb(m,k)*2**k
        k+=2
    return tot
def distinct_count(Sset,p,r):
    seen=set()
    for comb in combinations(Sset,r): seen.add(sum(comb)%p)
    return len(seen)

n=32; r=4; Nr=Nr_cf(n,r)
print(f"n={n} r={r} Nr={Nr}. Crossover band Nr/p in [0.7,1.3].")
print(f"{'p':>10} {'Nr/p':>7} {'mu_n_dist':>10} {'rand_dist':>10} {'birthday':>10} {'mu/birth':>9} {'rand/birth':>10}")
for p in primes_for(n,0.7,1.3,Nr,count=8):
    Smu=subgroup(n,p)
    dmu=distinct_count(Smu,p,r)
    # random control: n distinct nonzero residues
    random.seed(p)
    Srand=random.sample(range(1,p),n)
    drand=distinct_count(Srand,p,r)
    birth=p*(1-(1-1/p)**Nr)
    print(f"{p:>10} {Nr/p:>7.3f} {dmu:>10} {drand:>10} {birth:>10.1f} {dmu/birth:>9.4f} {drand/birth:>10.4f}")
