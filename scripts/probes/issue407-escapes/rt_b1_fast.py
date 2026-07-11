#!/usr/bin/env python3
"""Fast vectorized red-team: for n=16,20,24,32 find whether any GENUINE direction with
ragged EXCESS > coset-core achieves binding (max) |S|.  Uses numpy mod-p; Lagrange via
precomputed barycentric weights per k-subset.  Caps subset enumeration with a generous cap
and random sampling for the big cases (we want the BINDING set; sampling subsets that hit it)."""
import itertools, math, random
import numpy as np
from sympy import isprime, factorint
def out(*a): print(*a, flush=True)
def find_prime(n,wm):
    p=max(wm,n+1); r=p%n
    if r!=1: p+=(1-r)%n
    while True:
        if p%n==1 and isprime(p): return p
        p+=n
def gen(p):
    fac=list(factorint(p-1).keys())
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): return c
def mu(p,n):
    w=pow(gen(p),(p-1)//n,p); return [pow(w,j,p) for j in range(n)]
def core(S,n):
    Sset=set(S); best=0;bd=1
    for dp in [d for d in range(2,n+1) if n%d==0]:
        step=n//dp; cov=0
        for i in range(step):
            cs=set((i+step*t)%n for t in range(dp))
            if cs<=Sset: cov+=len(cs)
        if cov>best: best=cov;bd=dp
    return best,bd
def corr(a,b,n,k):
    nh=n//2; return (a%nh<k) and (b%nh<k)

def maxagree_set_sampled(fv,xs,k,p,maxsub):
    n=len(xs)
    xa=np.array(xs,dtype=np.int64)
    fa=np.array([v%p for v in fv],dtype=np.int64)
    P=p
    subs=list(itertools.combinations(range(n),k))
    if len(subs)>maxsub:
        subs=random.sample(subs,maxsub)
    best=k; bestS=set(range(k))
    for T in subs:
        Tl=list(T)
        # interpolate poly through (xs[t],fv[t]); evaluate at all xs via Lagrange (python ints, exact)
        ag=set()
        for j in range(n):
            xj=xs[j]; val=0
            for t in Tl:
                term=fv[t]; xt=xs[t]
                for s in Tl:
                    if s==t: continue
                    term=(term*((xj-xs[s])%P))%P
                    term=(term*pow((xt-xs[s])%P,P-2,P))%P
                val=(val+term)%P
            if val==fv[j]%P: ag.add(j)
        if len(ag)>best: best=len(ag); bestS=ag
    return best,bestS

def run(n,k,gsamp,maxsub):
    p=find_prime(n,n*40+1); xs=mu(p,n)
    out(f"\n### n={n} k={k} p={p} rho={k/n:.3f} sqrt(nk)={math.sqrt(n*k):.2f} ###")
    G=list(range(1,p,max(1,(p-1)//gsamp)))
    recs=[]
    for a in range(k,n):
        for b in range(a):
            if corr(a,b,n,k): continue
            gmax=(0,set(),None)
            for g in G:
                fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
                sz,S=maxagree_set_sampled(fv,xs,k,p,maxsub)
                if sz<n and sz>gmax[0]: gmax=(sz,S,g)
            if gmax[0]==0: continue
            c,cd=core(gmax[1],n); exc=gmax[0]-c
            recs.append((a,b,math.gcd(a-b,n),gmax[0],c,exc,cd))
    recs.sort(key=lambda r:-r[3])
    out("  by global-max |S| (a,b,d,|S|,core,excess):")
    for r in recs[:8]:
        out(f"    a={r[0]:>2} b={r[1]:>2} d={r[2]} |S|={r[3]} core={r[4]}(mu_{r[6]}) excess={r[5]}")
    bind=recs[0]
    # any excess-dominant (excess>core) genuine dir reaching within 1 of binding?
    nearbind=[r for r in recs if r[5]>r[4] and r[3]>=bind[3]-1]
    out(f"  BINDING |S|={bind[3]} excess={bind[5]}; #excess-dominant dirs within 1 of binding={len(nearbind)}")
    for r in nearbind[:4]:
        out(f"     excess-dom: a={r[0]} b={r[1]} d={r[2]} |S|={r[3]} core={r[4]} excess={r[5]}")

run(20,2,gsamp=50,maxsub=20000)   # C(20,2)=190 cheap
run(24,3,gsamp=40,maxsub=4000)    # C(24,3)=2024
run(16,4,gsamp=50,maxsub=1820)    # full
out("DONE")
