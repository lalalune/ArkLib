#!/usr/bin/env python3
"""n=32 test of the CORRECTED census normal form: does #distinct-GAMMA stay <= budget
2^r*C(2^{mu-1},r) at the next scale? (the open content my n=16 refutation isolated).
Also re-confirm #alignable-SETS exceeds budget (the deployed-Prop falsity persists).
n=32: mu=5. budget(r) = 2^r*C(16,r). prize p~32^4 ~ 1.05e6, 32|(p-1).
Structured worst lines only (adjacent high-freq), a0=r+1, k=r-1 (m=1).
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
    if n%2==0: return n==2
    for q in range(3,int(n**0.5)+1,2):
        if n%q==0: return False
    return True
def find_g(p,n):
    for h in range(2,5000):
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

n=32; mu=5
# prize prime ~ n^4 = 1048576, 32 | p-1
p=next(q for q in range(1048609, 1100000) if (q-1)%32==0 and is_prime(q))
print(f"n=32 p={p} beta={math.log(p)/math.log(32):.2f}")
g=find_g(p,n); xs=[pow(g,i,p) for i in range(n)]
assert len(set(xs))==32
# r=2 (a0=3,k=1, budget 4*C(16,2)=480) and r=3 (a0=4,k=2, budget 8*C(16,3)=4480) feasible
for r in (2,3):
    k=r-1; a0=r+1; budget=2**r*comb(2**(mu-1),r)
    cand=[(j,j-1) for j in range(2,n)]+[(n//2,n//2-1),(n//2+1,n//2-1)]
    cand=sorted(set(cand))
    ws=(0,None); wg=(0,None)
    for (aa,bb) in cand:
        if aa>=n or bb<0 or aa==bb: continue
        u0=[pow(x,aa,p) for x in xs]; u1=[pow(x,bb,p) for x in xs]
        s,gm=census(u0,u1,xs,p,k,a0)
        if s>ws[0]: ws=(s,f"x^{aa},x^{bb}")
        if gm>wg[0]: wg=(gm,f"x^{aa},x^{bb}")
    print(f"  r={r} k={k} a0={a0} budget={budget}: worst SETS={ws[0]} ({ws[1]}) {'EXCEEDS' if ws[0]>budget else 'OK'}; worst GAMMA={wg[0]} ({wg[1]}) {'EXCEEDS' if wg[0]>budget else 'OK'}", flush=True)
