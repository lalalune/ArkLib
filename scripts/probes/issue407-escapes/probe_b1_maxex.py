#!/usr/bin/env python3
"""Find the genuine direction with max ragged excess at n=16 k=4, and report |S|, core, excess.
This is where R-thin (SparseRaggedExcessBound) would actually bite. Is its |S| above or below sqrt(nk)?
Is the excess itself bounded by k+2 or by s=n/d?"""
import math, itertools
from sympy import isprime, factorint
def find_prime(n,wm):
    p=max(wm,n+1); r=p%n
    if r!=1: p+=(1-r)%n
    while True:
        if p%n==1 and isprime(p): return p
        p+=n
def generator(p):
    fac=list(factorint(p-1).keys())
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): return c
def mu_n(p,n):
    g0=generator(p); w=pow(g0,(p-1)//n,p)
    return [pow(w,j,p) for j in range(n)], w
def max_agree_set(fv,xs,k,p):
    n=len(xs); best=k; bestS=set(range(k)); fv=[int(v)%p for v in fv]; inv={}
    for T in itertools.combinations(range(n),k):
        ag=set()
        for j in range(n):
            xj=xs[j]; val=0
            for t in T:
                term=fv[t]; xt=xs[t]
                for s in T:
                    if s==t: continue
                    d=(xt-xs[s])%p
                    if d not in inv: inv[d]=pow(d,p-2,p)
                    term=term*((xj-xs[s])%p)%p*inv[d]%p
                val=(val+term)%p
            if val==fv[j]: ag.add(j)
        if len(ag)>best: best=len(ag); bestS=ag
    return best,bestS
def coset_core(S,n):
    Sset=set(S); best=0;bd=1
    for dp in [d for d in range(2,n+1) if n%d==0]:
        step=n//dp;cov=0
        for i in range(step):
            cs=set((i+step*t)%n for t in range(dp))
            if cs<=Sset:cov+=len(cs)
        if cov>best:best=cov;bd=dp
    return best,bd
n,k=16,4
p=find_prime(n,200); xs,w=mu_n(p,n)
print(f"### n={n} k={k} p={p} sqrt(nk)={math.sqrt(n*k):.2f} k+2={k+2}")
best_ex=[]
for a in range(k,n):
    for b in range(0,a):
        for g in range(1,p,max(1,(p-1)//40)):
            fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
            sz,S=max_agree_set(fv,xs,k,p)
            core,cd=coset_core(S,n);ex=sz-core
            nd=len(set(fv)); gg=math.gcd(math.gcd(a,b),n)
            if nd>n//2 and gg==1 and ex>0:
                best_ex.append((ex,sz,core,cd,a,b,g,nd))
best_ex.sort(reverse=True)
print("Top genuine RAGGED by EXCESS (where R-thin bites):")
for r in best_ex[:10]:
    ex,sz,core,cd,a,b,g,nd=r
    d=math.gcd(a-b,n)
    print(f"  a={a} b={b} d={d} g={g}: |S|={sz} core={core}(mu_{cd}) EXCESS={ex} | nd={nd} sqrt(nk)={math.sqrt(n*k):.1f} k+2={k+2} s=n/d={n//d}")
