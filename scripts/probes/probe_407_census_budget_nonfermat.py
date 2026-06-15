#!/usr/bin/env python3
"""Confirm the SET>budget, GAMMA<=budget finding at n=16 holds at a NON-Fermat prize prime
(rule out a 65537-Fermat artifact). Need p prime, 16|(p-1), p~16^4=65536, p != 65537.
Candidates: 65537(Fermat), 65617, 65713, 66161, 66449 ... pick a generic one.
"""
import itertools, math, sys
from math import comb
def pf(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs
def is_prime(n):
    if n<2: return False
    for q in range(2,int(n**0.5)+1):
        if n%q==0: return False
    return True
def find_g(p,n):
    for h in range(2,4000):
        x=pow(h,(p-1)//n,p)
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in pf(n)): return x
    raise ValueError
def census(u0,u1,xs,p,k,a):
    n=len(xs); e0={}; e1={}
    for T in itertools.combinations(range(n),k+1):
        t0=t1=0
        for i in T:
            den=1
            for j in T:
                if i!=j: den=den*((xs[i]-xs[j])%p)%p
            inv=pow(den,-1,p); t0=(t0+u0[i]*inv)%p; t1=(t1+u1[i]*inv)%p
        e0[T]=t0; e1[T]=t1
    def ratio(T):
        a_,b_=e0[T],e1[T]
        if b_!=0: return (-a_)*pow(b_,-1,p)%p
        return None if a_==0 else 'X'
    sets=0; gam=set()
    for S in itertools.combinations(range(n),a):
        r=None; ok=True; nd=False
        for T in itertools.combinations(S,k+1):
            rt=ratio(T)
            if rt is None: continue
            if rt=='X': ok=False; break
            nd=True
            if r is None: r=rt
            elif r!=rt: ok=False; break
        if ok and nd: sets+=1; gam.add(r)
    return sets,len(gam)
# find a non-Fermat prize prime for n=16
n=16; mu=4
cands=[p for p in range(65539,70000) if (p-1)%16==0 and is_prime(p)]
p=cands[5]  # a generic one, not 65537
print(f"non-Fermat prize prime p={p}, beta={math.log(p)/math.log(16):.2f}")
g=find_g(p,n); xs=[pow(g,i,p) for i in range(n)]
for r in (3,4):
    k=(r-2)+1; a0=r+1; budget=2**r*comb(2**(mu-1),r)
    cand=[(j,j-1) for j in range(2,n)]
    ws=(0,None); wg=(0,None)
    for (aa,bb) in cand:
        u0=[pow(x,aa,p) for x in xs]; u1=[pow(x,bb,p) for x in xs]
        s,gm=census(u0,u1,xs,p,k,a0)
        if s>ws[0]: ws=(s,f"x^{aa},x^{bb}")
        if gm>wg[0]: wg=(gm,f"x^{aa},x^{bb}")
    print(f"  r={r} k={k} a0={a0} budget={budget}: worst SETS={ws[0]} ({ws[1]}) {'EXCEEDS' if ws[0]>budget else 'OK'}; worst GAMMA={wg[0]} ({wg[1]}) {'EXCEEDS' if wg[0]>budget else 'OK'}")
