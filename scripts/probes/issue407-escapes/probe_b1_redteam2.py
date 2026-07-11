#!/usr/bin/env python3
"""Lean red-team: n=16 k=4 only. Per genuine direction, max|S| and excess. Decisive question:
do GENUINE RAGGED (excess>0) sets stay <= sqrt(nk)? Is the max-|S| genuine direction coset or ragged?"""
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
def max_agreement_set(fv,xs,k,p):
    n=len(xs)
    best=k; bestS=set(range(k))
    for T in itertools.combinations(range(n),k):
        Tl=list(T); ag=set()
        for j in range(n):
            xj=xs[j]; val=0
            for t in Tl:
                term=fv[t]; xt=xs[t]
                for s in Tl:
                    if s==t: continue
                    term=(term*((xj-xs[s])%p))%p
                    term=(term*pow((xt-xs[s])%p,p-2,p))%p
                val=(val+term)%p
            if val==fv[j]%p: ag.add(j)
        if len(ag)>best: best=len(ag); bestS=ag
    return best, bestS
def coset_core(Sidx, n):
    Sset=set(Sidx); best=0; bestd=1
    for dp in [d for d in range(2,n+1) if n%d==0]:
        step=n//dp; cov=0
        for i in range(step):
            cs=set((i+step*t)%n for t in range(dp))
            if cs<=Sset: cov+=len(cs)
        if cov>best: best=cov; bestd=dp
    return best, bestd
n,k=16,4
p=find_prime(n,n*40+1); xs,w=mu_n(p,n); rho=k/n
print(f"### n={n} k={k} p={p} rho={rho:.3f} sqrt(nk)={math.sqrt(n*k):.2f} ###")
res=[]
for a in range(k,n):
    for b in range(0,a):
        best=0;bestS=None;bg=None
        for g in range(1,p,max(1,(p-1)//80)):
            fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
            sz,S=max_agreement_set(fv,xs,k,p)
            if sz>best: best=sz;bestS=S;bg=g
        core,cd=coset_core(bestS,n); ex=best-core
        nd=len(set((pow(x,a,p)+bg*pow(x,b,p))%p for x in xs))
        gg=math.gcd(math.gcd(a,b),n)
        res.append((a,b,best,core,cd,ex,nd,gg))
genuine=[r for r in res if r[6]>n//2 and r[7]==1]
gr=[r for r in genuine if r[5]>0]; gc=[r for r in genuine if r[5]==0]
print(f"max|S| ALL dirs = {max(r[2] for r in res)}")
print(f"GENUINE dirs (nd>{n//2},gcd=1): {len(genuine)}, max|S|={max(r[2] for r in genuine)}")
print(f"  genuine COSET (excess0): {len(gc)} max|S|={max((r[2] for r in gc),default=0)}")
print(f"  genuine RAGGED(excess>0): {len(gr)} max|S|={max((r[2] for r in gr),default=0)} max-excess={max((r[5] for r in gr),default=0)}")
print(f"  => sqrt(nk)={math.sqrt(n*k):.2f}; does genuine-ragged max|S| <= sqrt(nk)? {max((r[2] for r in gr),default=0) <= math.sqrt(n*k)}")
print("\nTop 8 genuine by |S|:")
for r in sorted(genuine,key=lambda r:-r[2])[:8]:
    print(f"  a={r[0]} b={r[1]} |S|={r[2]} core={r[3]}(mu_{r[4]}) excess={r[5]} nd={r[6]}")
