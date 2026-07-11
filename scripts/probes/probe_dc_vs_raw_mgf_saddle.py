#!/usr/bin/env python3
"""Probe: at the saddle y*^2 = 2 log q / n, is the RAW MGF inequality
   Sum_r (q E_r y^{2r}/(2r)!) <= q exp(n y^2/2)  SATISFIABLE?
vs the DC-subtracted MGF  Sum_r ((q E_r - n^{2r}) y^{2r}/(2r)!) <= q exp(n y^2/2)?
RAW includes the b=0 term (period = n at b=0), so RAW MGF = sum_b cosh(|eta_b| y) INCLUDING b=0.
DC-subtracted drops b=0.  The b=0 term alone is cosh(n y) which at the saddle is huge.
PROPER mu_n: n=2^a, n|p-1, p>>n^3, NEVER n=q-1. exact F_p via numpy FFT of indicator.
"""
import numpy as np, math, cmath

def first_prime_ge(x):
    x=max(x,2)
    if x%2==0: x+=1
    while True:
        if all(x%d for d in range(3,int(x**0.5)+1,2)) and x>1: return x
        x+=2

def prize_prime(n, beta):
    # want p ≡ 1 mod n, p ≈ n^beta, p >> n^3
    target=int(n**beta)
    m=max(target//n,1)
    while True:
        p=n*m+1
        if all(p%d for d in range(3,int(p**0.5)+1,2)) and p>1:
            return p,m
        m+=1

def mu_n(p,n):
    # subgroup of order n in F_p*: g^{(p-1)/n}
    # find generator
    fac=[]
    x=p-1
    d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fac.append(x)
    def isgen(g):
        return all(pow(g,(p-1)//f,p)!=1 for f in fac)
    g=2
    while not isgen(g): g+=1
    h=pow(g,(p-1)//n,p)
    S=set()
    v=1
    for _ in range(n):
        S.add(v); v=v*h%p
    assert len(S)==n
    return sorted(S)

def eta(p,sub,b):
    # sum_{x in sub} exp(2pi i b x / p)
    return sum(cmath.exp(2j*math.pi*(b*x % p)/p) for x in sub)

for (n,beta) in [(8,4.0),(16,4.0),(8,5.0),(16,5.0),(32,4.0)]:
    p,m=prize_prime(n,beta)
    sub=mu_n(p,n)
    q=p
    y=math.sqrt(2*math.log(q)/n)
    rhs=q*math.exp(n*y*y/2)  # = q*q = q^2 at saddle
    # RAW MGF = sum over ALL b in 0..p-1 of cosh(|eta_b| y)  (b=0 gives eta=n)
    # but the in-tree raw object is sum_r q E_r y^{2r}/(2r)! = sum_{b in F_q} cosh(|eta_b| y)
    # (full additive group incl b=0). DC = sum_{b != 0}.
    # compute via direct cosh sum (cheaper than moments): need all eta_b
    # |eta_b|: b=0 -> n. For b!=0 compute.
    raw=math.cosh(n*y)  # b=0 term
    dc=0.0
    # sample/exact: p small enough for n<=16; for n=32 p is ~1e6 -> sum over all b is 1e6 etas * 32 = 3e7 ok-ish
    for b in range(1,p):
        e=abs(eta(p,sub,b))
        c=math.cosh(e*y)
        raw+=c; dc+=c
    raw_ok = raw<=rhs
    dc_ok  = dc<=rhs
    M=max(abs(eta(p,sub,b)) for b in range(1,p))
    print(f"n={n:3d} beta={beta} p={p} q^2={q*q:.3e} y*={y:.4f} M={M:.3f} sqrt(n log(q/n))={math.sqrt(n*math.log(q/n)):.3f}")
    print(f"    RAW MGF={raw:.3e}  <= q^2? {raw_ok}   (b=0 term cosh(n y)={math.cosh(n*y):.3e})")
    print(f"    DC  MGF={dc:.3e}  <= q^2? {dc_ok}")
