#!/usr/bin/env python3
"""c_n is a UNIVERSAL constant at each fixed p (verified). Reconstruct as a rational via CRT
across primes (the denominator may be large -> need big modulus). c_n = T_{D_n}/(Vr Vc), D=n(n-1)/2."""
import itertools, random
from fractions import Fraction
def descfact(s,d,p):
    r=1
    for t in range(d): r=(r*((s-t)%p))%p
    return r
def Vand(v,p):
    n=len(v); r=1
    for i in range(n):
        for j in range(i+1,n): r=(r*((v[i]-v[j])%p))%p
    return r
def Td(ri,ci,n,d,p):
    total=0
    for sigma in itertools.permutations(range(n)):
        sign=1
        for a in range(n):
            for b in range(a+1,n):
                if sigma[a]>sigma[b]: sign=-sign
        S=0
        for i in range(n): S=(S-(ci[sigma[i]]*ri[i]))%p
        total=(total+sign*descfact(S,d,p))%p
    nf=1
    for t in range(1,d+1): nf*=t
    return (total*pow(nf%p,p-2,p))%p
def cn_mod(n,p,seed):
    random.seed(seed); D=n*(n-1)//2
    while True:
        ri=random.sample(range(p),n); ci=random.sample(range(p),n)
        Vr=Vand(ri,p); Vc=Vand(ci,p)
        if Vr and Vc:
            return (Td(ri,ci,n,D,p)*pow((Vr*Vc)%p,p-2,p))%p
def crt(rs,ms):
    from functools import reduce
    M=reduce(lambda a,b:a*b,ms)
    x=0
    for r,m in zip(rs,ms):
        Mi=M//m; x=(x+r*Mi*pow(Mi,-1,m))%M
    return x,M
def ratrecon(a,M):
    import math
    bound=int(math.isqrt(M//2))
    r0,r1=M,a%M; s0,s1=0,1
    while r1>bound:
        q=r0//r1; r0,r1=r1,r0-q*r1; s0,s1=s1,s0-q*s1
    if s1<0: r1,s1=-r1,-s1
    if s1==0 or abs(r1)>bound: return None
    return Fraction(r1,s1)
for n in (3,4,5,6,7):
    D=n*(n-1)//2
    primes=[101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197]
    primes=[p for p in primes if p>D+n+5][:14]
    rs=[cn_mod(n,p,seed=p+n) for p in primes]
    a,M=crt(rs,primes)
    fr=ratrecon(a,M)
    print(f"n={n} D_n={D}: c_n = {fr}   (per-prime residues sample {list(zip(primes,rs))[:4]})")
