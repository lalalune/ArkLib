#!/usr/bin/env python3
"""
DECOUPLING decay crossing-depth c* ACROSS RATES rho (the live-edge test).

My rho=1/4 result: c*=s*-k = n/4-1 = m-1 = Theta(n) (DEEPLY over-det, OFF BGK, FIRST HORN of §6).
Question: does c*=Theta(n) generalize across rates rho in {1/2,1/4,1/8}, or does some THINNER rate
cross into UNDER-determined (c*/n -> 0, re-coupling to BGK = the live edge)?

EXACT full (a,b) direction sweep, multi-prime p-independence, PROPER mu_n, p>>n^3, p==1 mod n,
NEVER n=q-1. Reports s*, c*=s*-k, c*/n, delta*=(n-s*)/n for each (n, rho).
"""
import itertools, sys
from math import sqrt

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
    assert len(set(mu))==n and (p-1)//n>=2
    return mu
def inc(a,b,n,k,p,s,mu):
    gam=set();inv=lambda z:pow(z,p-2,p)
    MUa=[pow(x,a,p) for x in mu];MUb=[pow(x,b,p) for x in mu]
    def ddk(vals,pts):
        vs=list(vals[:k+1]);xs=pts[:k+1]
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                vs[i]=(vs[i]-vs[i-1])*inv((xs[i]-xs[i-j])%p)%p
        return vs[k]
    def inRS(vals,pts):
        if len(pts)<=k:return True
        for st in range(len(pts)-k):
            if ddk(vals[st:st+k+1],pts[st:st+k+1])!=0:return False
        return True
    for R in itertools.combinations(range(n),s):
        pts=[mu[i] for i in R];u0=[MUa[i] for i in R];u1=[MUb[i] for i in R]
        if inRS(u1,pts):
            if inRS(u0,pts):return p
            continue
        a0=ddk(u0,pts);a1=ddk(u1,pts)
        if a1%p==0:continue
        gm=(-a0*inv(a1))%p
        if inRS([(u0[i]+gm*u1[i])%p for i in range(s)],pts):gam.add(gm)
    return len(gam)
def find_sstar(n,k,p,mu,budget):
    """full (a,b) sweep, find s*=first s (from k+2 up) with maxI<=budget. returns (sstar, profile)"""
    prof={}
    sstar=None
    for s in range(k+2, n):
        best=0
        for a in range(k,n):
            for b in range(k,n):
                if a==b: continue
                I=inc(a,b,n,k,p,s,mu)
                if I<p and I>best: best=I
        prof[s]=best
        if best<=budget and sstar is None: sstar=s
    return sstar, prof

if __name__=='__main__':
    print("=== c* across rates rho (full sweep, multi-prime) ===", flush=True)
    # (n, rho) with k=rho*n integer. Keep n small enough for full-sweep feasibility.
    cases=[]
    for n in [16,24]:
        for denom in [2,4,8]:
            if n%denom==0 and (n//denom)>=1:
                cases.append((n, n//denom, 1.0/denom))
    for n,k,rho in cases:
        budget=n
        # two primes for p-independence on the over-det band
        sstars=[]
        for mult in [4,5]:
            p=find_prime(n,mult); mu=setup(n,p)
            ss,prof=find_sstar(n,k,p,mu,budget)
            sstars.append((p,ss,prof))
        p0,ss0,pr0=sstars[0]; p1,ss1,pr1=sstars[1]
        pind = (ss0==ss1)
        if ss0 is None:
            print(f" n={n} k={k} rho={rho:.3f}: NO crossing in band (maxI>budget all s) p={p0}", flush=True)
            continue
        c=ss0-k
        m=n//4
        print(f" n={n} k={k} rho={rho:.3f} budget={budget}: s*={ss0} c*={c} c*/n={c/n:.3f} "
              f"delta*={(n-ss0)/n:.4f} Johnson={1-sqrt(rho):.4f} p-indep={pind} (p={p0},{p1})", flush=True)
    print("\n=== READING: c*/n constant across rho => OFF-BGK universal. c*/n -> 0 at thin rho => live edge.",
          flush=True)
    print("DONE", flush=True)
