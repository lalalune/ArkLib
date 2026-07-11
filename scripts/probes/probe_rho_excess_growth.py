#!/usr/bin/env python3
"""
DECISIVE PROBE: the prize <=> Sum_{i<N} log rho(2^i) <= 1/2 N log2 + 1/2 log L + O(1),
i.e. the EXCESS  E_N := Sum_{i<N} (log rho(2^i) - 1/2 log2)  must be O(log log m) = O(log N).
  - If E_N grows ~ Theta(N) (linear): the geomean stays bounded ABOVE sqrt2 => the prize FAILS
    on the tower-product face (this is the wall / DyadicGeomean refutation, prod > (sqrt2)^N).
  - If E_N grows ~ O(log N): prize-consistent, the martingale/Freedman QV bound is the lever.
The increments d_i := log rho(2^i) - 1/2 log2 are BOUNDED in [0, 1/2 log2] (probe 1: rho in [sqrt2,2]).
Measure E_N at increasing amax, and the per-level d_i decay. ASYMPTOTIC-GUARD compliant: this is the
sub-leading-vs-linear test the guard demands BEFORE any beyond-Johnson lean.
NEVER n=q-1. p = 1 mod 2^amax, p >> n^3.
"""
import cmath, math
import numpy as np

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31):
        if a>=m: continue
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(r-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True

def find_prime(amax, beta):
    n=2**amax
    target=int(n**beta)
    mod=2**amax
    start=(target//mod)*mod+1
    for k in range(0, 500000):
        for cand in (start+k*mod, start-k*mod):
            if cand>n*n and is_prime(cand):
                return cand
    return None

def primitive_root(p):
    fac=[]; pm=p-1; d=2
    while d*d<=pm:
        if pm%d==0:
            fac.append(d)
            while pm%d==0: pm//=d
        d+=1
    if pm>1: fac.append(pm)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    return None

def subgroup(p, g, n):
    h=pow(g,(p-1)//n,p); S=[]; cur=1
    for _ in range(n): S.append(cur); cur=cur*h%p
    return S

def Mval(p, S):
    best=0.0; w=2j*math.pi/p
    for b in range(1,p):
        s=sum(cmath.exp(w*(b*x % p)) for x in S)
        a=abs(s)
        if a>best: best=a
    return best

half_log2 = 0.5*math.log(2)
print(f"half_log2 = {half_log2:.5f}  (rho=sqrt2 is the prize-equality per-level)")
print()
for beta in (4.0,):
    for amax in (4,5,6,7):
        p=find_prime(amax,beta)
        if p is None or p>400009:
            print(f"amax={amax}: no usable prime <=400009"); continue
        g=primitive_root(p)
        Ms=[]
        for a in range(1,amax+1):
            Ms.append(Mval(p,subgroup(p,g,2**a)))
        rhos=[Ms[i+1]/Ms[i] for i in range(len(Ms)-1)]
        d=[math.log(r)-half_log2 for r in rhos]   # excess increments >=0
        E=np.cumsum(d)
        N=len(d)
        print(f"amax={amax} p={p} n={2**amax} N={N} levels")
        print(f"  rho       = {[round(r,4) for r in rhos]}")
        print(f"  d_i(excess)= {[round(x,4) for x in d]}   (each in [0, {half_log2:.4f}])")
        print(f"  E_N (cumulative excess) = {round(float(E[-1]),4)}   vs  log2(N)={math.log2(N):.3f}  N/2={N/2:.1f}")
        print(f"  ratio E_N/N = {float(E[-1])/N:.4f}  (->0 = prize-consistent; ->const>0 = linear wall)")
        print(f"  ratio E_N/log(N+1) = {float(E[-1])/math.log(N+1):.4f}  (bounded = prize-consistent)")
        print()
