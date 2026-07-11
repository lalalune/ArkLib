#!/usr/bin/env python3
"""
probe_444_2adic_stall_mechanism.py  (#444 growth-law conflict)

GOAL: derive WHY s* STALLS at powers of 2 (n=16: s*7->7, n=32: s*13->13) and what
that implies for m*=s*-k along the PRIZE sequence n=2^mu.

The rust engine (char-0, p-indep) shows the per-direction over-det far-line incidence
I(a,b;s) is a CLIFF: for FIXED direction (a,b) it is nonzero on a SHORT window of s
(1-3 consecutive values) then identically 0. s* = max over far dirs of {first s with
I(a,b;s) <= budget=n}. Beyond the per-direction support cutoff, I=0 (good).

So s* is governed by:
  s_max(a,b) := largest s with I(a,b;s) > 0   (the agreement-support cutoff per dir)
  and the VALUE I(a,b;s) near that cutoff vs budget=n.

This probe computes, EXACTLY (char-0 via p == 1 mod n, p >> n^4), for every far
direction (a,b) (k<=a<n, k<=b<a, ρ=1/4 so k=n/4):
  - the full incidence vector I(a,b; s) for s = k+2 .. n-1
  - s_max(a,b) = last s with I>0, and the binding s for that dir = first s with I<=budget
Then it reports:
  - the OVERALL s* (max over dirs of first-s-with-I<=budget) -- cross-checks rust
  - the direction that BINDS s* and its 2-adic structure
  - decomposition of s* and m*=s*-k by gcd(a,b,n)/2-adic valuation, to expose the
    stall: at n=2^mu the binding direction has a special 2-adic alignment.

Tractable n: 8,16,24,32 (C(32,16)~6e8 -- we cap directions & use the cliff: once a
dir's I hits 0 we stop raising s for it).
"""
import itertools, sys, math
from functools import lru_cache

def isprime(x):
    if x<2:return False
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%x==0:continue
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f={};dd=2
    while dd*dd<=x:
        while x%dd==0:f[dd]=f.get(dd,0)+1;x//=dd
        dd+=1
    if x>1:f[x]=f.get(x,0)+1
    return f
def proot(p):
    fs=set(fac(p-1))
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fs):return g
def find_prime(n, mult=4):
    base=max(1000003, n**mult); c=base+((1-base)%n)
    while not isprime(c): c+=n
    return c
def setup(n,p):
    g=proot(p);h=pow(g,(p-1)//n,p)
    mu=[pow(h,i,p) for i in range(n)]
    assert len(set(mu))==n
    return mu

def v2(x):
    if x==0: return 99
    v=0
    while x%2==0: x//=2; v+=1
    return v

def incidence_dir(a,b,n,k,p,s,mu,invd):
    """# distinct gamma with x^a+gamma x^b agreeing with deg<k poly on >=s pts of mu_n."""
    gam=set()
    MUa=[pow(x,a,p) for x in mu];MUb=[pow(x,b,p) for x in mu]
    def ddk(vals,idx):
        vs=list(vals[:k+1])
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                vs[i]=(vs[i]-vs[i-1])*invd[idx[i]*n+idx[i-j]]%p
        return vs[k]
    def in_RS(vals,idx):
        if len(idx)<=k:return True
        for st in range(len(idx)-k):
            if ddk(vals[st:st+k+1],idx[st:st+k+1])!=0:return False
        return True
    HEAVY=False
    for R in itertools.combinations(range(n),s):
        u0=[MUa[i] for i in R];u1=[MUb[i] for i in R]
        if in_RS(u1,R):
            if in_RS(u0,R): return -1  # heavy/saturated
            continue
        a0=ddk(u0,R);a1=ddk(u1,R)
        if a1%p==0:continue
        gm=(-a0*pow(a1,p-2,p))%p
        if in_RS([(u0[i]+gm*u1[i])%p for i in range(s)],R):gam.add(gm)
    return len(gam)

def run(n):
    k=n//4; budget=n
    p=find_prime(n,4); mu=setup(n,p)
    invd=[0]*(n*n)
    for i in range(n):
        for j in range(n):
            if i!=j: invd[i*n+j]=pow((mu[i]-mu[j])%p,p-2,p)
    # For each far direction (k<=a<n, k<=b<a) compute first-s-with-I<=budget & s_max.
    # cliff: stop raising s once I==0.
    overall_sstar=0; binder=None; binder_prof=None
    cap_C = 300_000_000
    dirs=[(a,b) for b in range(k,n) for a in range(k,n) if a!=b]
    results=[]
    for (a,b) in dirs:
        prof={}
        first_bind=None  # first s with I<=budget
        s=k+2
        while s<n-1:
            if math.comb(n,s)>cap_C: break
            I=incidence_dir(a,b,n,k,p,s,mu,invd)
            prof[s]=I
            if I==-1:  # heavy: counts as > budget
                s+=1; continue
            if I<=budget and first_bind is None:
                first_bind=s
            if I==0:  # cliff cutoff: all higher s are 0 too -> good
                break
            s+=1
        if first_bind is None: first_bind=k+2  # never above budget (degenerate)
        results.append((a,b,first_bind,prof))
    # s* = max over dirs of first_bind
    binder=max(results,key=lambda r:r[2])
    overall_sstar=binder[2]
    return n,k,budget,p,overall_sstar,binder,results

if __name__=="__main__":
    ns=[int(x) for x in sys.argv[1:]] or [8,12,16,20,24]
    print("n  k  budget  s*  m*=s*-k  delta*  binder(a,b)  v2(a) v2(b) v2(a-b) v2(gcd(a,b,n))")
    for n in ns:
        n,k,budget,p,sstar,binder,results=run(n)
        a,b,fb,prof=binder
        m=sstar-k
        g=math.gcd(math.gcd(a,b),n)
        print(f"{n:<3}{k:<3}{budget:<8}{sstar:<4}{m:<8}{(n-sstar)/n:<8.4f}({a},{b})  "
              f"{v2(a)}    {v2(b)}    {v2((a-b)%n) if (a-b)%n else 99}    {v2(g)}  [profile {dict(sorted(prof.items()))}]",flush=True)
        # also report ALL directions achieving the binding s*
        binders=[r for r in results if r[2]==sstar]
        print(f"     #binding dirs at s*={sstar}: {len(binders)}  e.g. {[(r[0],r[1]) for r in binders[:6]]}",flush=True)
    print("DONE",flush=True)
