#!/usr/bin/env python3
"""
DECOUPLING / INCIDENCE-DECAY frontier (#444 caveat #2, the named open item).

The single remaining char-0 open item in the far-line decoupling is the FULL s-dependence
I(s) of the over-determined incidence at the proven-extremal ANTIPODAL direction (n/2, n/2-1).
Known endpoints (in-tree):
  - I(s=k+2) = 2 m^3 - 2 m^2 + 1 ~ n^3/32   (cubic peak, OverdetIncidenceMaxClosedForm.lean)
  - I(s -> n/2) -> 1            (the trivial gamma=0 antipodal-closed witness floor)
GOAL: derive the GENERAL decay law I(s) (= I(c) with c = s-k the over-determination depth),
and locate the crossing s* = min{ s : I(s) <= budget = n }.

Method: EXACT incidence at the SINGLE antipodal direction (a,b)=(n/2, n/2-1), sweeping s.
p-INDEPENDENT in the over-det regime (s-k>=2) -- validated multi-prime. PROPER mu_n, p>>n^3,
p==1 mod n, NEVER n=q-1. rho=1/4 axis (k=n/4) AND k=2 axis (the closed-form axis) both swept.
"""
import itertools, sys

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
    assert len(set(mu))==n, "mu_n not order n"
    assert (p-1)//n>=2, "n=q-1 forbidden (need proper subgroup)"
    return mu

def incidence_dir(a,b,n,k,p,s,mu):
    """EXACT #{gamma : x^a + gamma x^b within Hamming dist (n-s) of RS[k]},
    counted via: gamma is forced by any far witness subset R of size s on which
    u0+gamma u1 is a degree<k poly (divided-diff_k = 0). Over-det => <=1 gamma per R."""
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
            if in_RS(u0,pts):return p   # whole line in RS -> degenerate
            continue
        a0=ddk(u0,pts);a1=ddk(u1,pts)
        if a1%p==0:continue
        gm=(-a0*inv(a1))%p
        if in_RS([(u0[i]+gm*u1[i])%p for i in range(s)],pts):gam.add(gm)
    return len(gam)

def profile_antipodal(n,k,p,mu):
    """Full I(s) profile at the antipodal direction (n/2, n/2-1)."""
    a,b=n//2, n//2-1
    prof={}
    for s in range(k+2, n):
        prof[s]=incidence_dir(a,b,n,k,p,s,mu)
    return prof

if __name__=="__main__":
    # multi-prime p-independence check + decay profile, k=2 axis (closed-form axis) and rho=1/4 axis
    print("=== ANTIPODAL (n/2,n/2-1) DECAY PROFILE I(s), k=2 axis (closed-form axis) ===",flush=True)
    for n in [8,12,16,20,24]:
        k=2; budget=n
        profs=[]
        for mult in [4,5]:  # two prime scales => p-independence
            p=find_prime(n,mult); mu=setup(n,p)
            profs.append((p, profile_antipodal(n,k,p,mu)))
        p0,prof0=profs[0]; p1,prof1=profs[1]
        pind = all(prof0[s]==prof1[s] for s in prof0)
        m=n//4
        peak_pred = 2*m**3-2*m**2+1 if n%4==0 else None
        line=f"n={n} k={k} m={m} budget={budget} p-indep={pind} (p={p0},{p1}):"
        print(line,flush=True)
        sstar=None
        for s in sorted(prof0):
            c=s-k
            flag=""
            if prof0[s]<=budget and sstar is None: sstar=s; flag=" <== s* (first <= budget)"
            extra=""
            if s==k+2 and peak_pred is not None:
                extra=f"  [closed-form peak pred={peak_pred} {'OK' if prof0[s]==peak_pred else 'MISMATCH'}]"
            print(f"   s={s} (c=s-k={c}, r={n-s}): I={prof0[s]}{flag}{extra}",flush=True)
        if sstar: print(f"  => s*={sstar}, c*=s*-k={sstar-k}, delta*=(n-s*)/n={(n-sstar)/n:.4f}",flush=True)
    print("DONE",flush=True)
