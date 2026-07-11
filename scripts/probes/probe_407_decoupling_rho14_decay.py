#!/usr/bin/env python3
"""
DECOUPLING decay law I(c), rho=1/4 axis (k=n/4) -- the PRIZE axis.

On the k=2 axis the antipodal decay is a CLIFF (cubic peak at c=2, then <=1 at c>=3): probe
probe_407_decoupling_decay_law.py established I(c=2)=2m^3-2m^2+1 exactly (9,37,97) then I(c>=3)<=1.
=> on k=2, s*=k+3 always, delta*->1, far from prize.

The PRIZE axis is rho=1/4 (k grows with n). There the decay is GRADUAL (DISPROOF two-engine table:
n=16: c=1->3824,c=2->89,c=3->9 ; n=24: c=2->1153,c=3->65,c=4->25,c=5->24). This probe derives the
general decay law I(c;n,k=n/4) and locates the budget crossing c* (s* = k + c*).

EXACT, ANTIPODAL direction (n/2,n/2-1) [+ 1-neighborhood extremality check at small n], over-det band
c=1..ceil(n/4). PROPER mu_n, p>>n^3, p==1 mod n, NEVER n=q-1, two prime scales => p-independence.
"""
import itertools, sys, math

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

def incidence_dir(a,b,n,k,p,s,mu):
    gam=set();inv=lambda z:pow(z,p-2,p)
    MUa=[pow(x,a,p) for x in mu];MUb=[pow(x,b,p) for x in mu]
    def ddk(vals,pts):
        vs=list(vals[:k+1]);xs=pts[:k+1]
        for j in range(1,k+1):
            for i in range(k,j-1,-1):
                vs[i]=(vs[i]-vs[i-1])*inv((xs[i]-xs[i-j])%p)%p
        return vs[k]
    def in_RS(vals,pts):
        if len(pts)<=k:return True
        for st in range(len(pts)-k):
            if ddk(vals[st:st+k+1],pts[st:st+k+1])!=0:return False
        return True
    for R in itertools.combinations(range(n),s):
        pts=[mu[i] for i in R];u0=[MUa[i] for i in R];u1=[MUb[i] for i in R]
        if in_RS(u1,pts):
            if in_RS(u0,pts):return p
            continue
        a0=ddk(u0,pts);a1=ddk(u1,pts)
        if a1%p==0:continue
        gm=(-a0*inv(a1))%p
        if in_RS([(u0[i]+gm*u1[i])%p for i in range(s)],pts):gam.add(gm)
    return len(gam)

if __name__=="__main__":
    print("=== rho=1/4 axis (k=n/4) ANTIPODAL DECAY I(c), c=s-k ===",flush=True)
    # over-det band only: c from 1 (just-determined+1) to ~n/4; deep c proven ->small
    data={}
    for n in [8,12,16,20,24]:
        if n%4: continue
        k=n//4; budget=n; a,b=n//2,n//2-1
        primes=[find_prime(n,4), find_prime(n,5)]
        cmax=min(n//2 - k, k+4)  # band up to s~n/2
        prof={}
        pind=True
        for c in range(1, cmax+1):
            s=k+c
            vals=[]
            for p in primes:
                mu=setup(n,p)
                vals.append(incidence_dir(a,b,n,k,p,s,mu))
            if vals[0]!=vals[1]: pind=False
            prof[c]=vals[0]
        data[n]=(k,prof,pind,primes)
        m=n//4
        peak=2*m**3-2*m**2+1
        print(f"n={n} k={k} m={m} budget={budget} p-indep={pind} (p={primes}):",flush=True)
        sstar=None
        for c in sorted(prof):
            s=k+c; flag=""
            if prof[c]<=budget and sstar is None: sstar=s; flag=f" <== s*=k+{c} (first <= budget {budget})"
            note=""
            if c==2: note=f"  [cubic-peak pred 2m^3-2m^2+1={peak} {'OK' if prof[c]==peak else 'DIFF'}]"
            print(f"   c={c} (s={s}, r={n-s}): I={prof[c]}{flag}{note}",flush=True)
        if sstar: print(f"  => s*={sstar}, c*={sstar-k}, delta*=(n-s*)/n={(n-sstar)/n:.4f}",flush=True)
    print("\n=== DECAY-LAW FIT: I(c) ratios (geometric? polynomial?) ===",flush=True)
    for n,(k,prof,pind,primes) in data.items():
        cs=sorted(prof)
        ratios=[]
        for i in range(1,len(cs)):
            if prof[cs[i]]>0:
                ratios.append(round(prof[cs[i-1]]/prof[cs[i]],2))
            else:
                ratios.append(float('inf'))
        print(f"n={n} k={k}: I(c)={[prof[c] for c in cs]}  drop-ratios I(c-1)/I(c)={ratios}",flush=True)
    print("DONE",flush=True)
