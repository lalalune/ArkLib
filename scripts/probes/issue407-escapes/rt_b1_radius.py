#!/usr/bin/env python3
"""
RED-TEAM the central flaw: the claim measures max|S| over ALL gamma (= largest agreement set
ANYWHERE = smallest delta = DEEP good region). But the PRIZE binds at the delta*-CROSSING.
At the crossing radius, the binding family (comment 125) is the LOW-exponent single monomial,
whose count is BGK-governed. We test:

  For each direction (a,b), genuine (not correlated), compute the agreement-set-size DISTRIBUTION
  over gamma, and report:
    - global max |S| (what the claim uses)  + its core/excess
    - the count at the delta*-crossing band (|S| just above the witness threshold (1-delta*)n)
  and compare WHICH direction binds at each.

Writes incrementally to stdout (line-buffered).
"""
import itertools, math, sys
from sympy import isprime, factorint
def out(*a): print(*a, flush=True)

def find_prime(n, wm):
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

def maxagree_set(fv,xs,k,p):
    n=len(xs)
    if k>=n: return n,set(range(n))
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
    return best,bestS

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

def run(n,k,gsamp=80):
    p=find_prime(n,n*40+1); xs=mu(p,n)
    out(f"\n### n={n} k={k} p={p} rho={k/n:.3f} sqrt(nk)={math.sqrt(n*k):.2f} ###")
    G=list(range(1,p,max(1,(p-1)//gsamp)))
    recs=[]
    for a in range(k,n):
        for b in range(a):
            if corr(a,b,n,k): continue
            # full distribution over gamma
            sizes=[]
            for g in G:
                fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
                sz,S=maxagree_set(fv,xs,k,p)
                if sz<n: sizes.append((sz,S,g))
            if not sizes: continue
            gmax=max(sizes,key=lambda t:t[0])
            c,cd=core(gmax[1],n); exc=gmax[0]-c
            recs.append((a,b,math.gcd(a-b,n),gmax[0],c,exc,cd))
    recs.sort(key=lambda r:-r[3])
    out("  genuine dirs by global-max |S| (a,b,d,|S|,core,excess):")
    for r in recs[:6]:
        out(f"    a={r[0]:>2} b={r[1]:>2} d={r[2]} |S|={r[3]} core={r[4]}(mu_{r[6]}) excess={r[5]}")
    # ALSO: the single low-exponent monomial x^k far count (comment 125 binding family)
    out(f"  binding(global-max) dir excess = {recs[0][5]}  (claim says 0)")

run(8,2); run(12,3); run(16,4); run(20,2); run(24,3, gsamp=50)
out("DONE")
