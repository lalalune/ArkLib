#!/usr/bin/env python3
"""
SECOND HORN of the §6 dichotomy — the BOUNDARY where the far-line crossing STOPS being
deeply over-determined (antipodal s*=n/2-1) and the rate k approaches/crosses the antipodal
floor s=k+2=n/2+1, i.e. where c*=s*-k could go to 0 / negative = the re-coupling boundary.

FIRST-HORN result (prior, axiom-clean Lean): s*=n/2-1 (antipodal-mechanism), so
c* = (n/2-1)-k = n(1/2-rho)-1 = Theta(n) for fixed rho<1/2, DEGENERATING as rho->1/2.

QUESTION (second horn): as k -> n/2 (rho -> 1/2), what is the ACTUAL binding s*?  Does the
antipodal s*=n/2-1 keep binding (impossible once k+2 > n/2-1, i.e. k > n/2-3), or does the
crossing jump to a DIFFERENT, possibly UNDER-determined regime that re-couples to BGK?

We sweep k near n/2 (rho near 1/2) and record:
  - the FULL incidence profile I(s) for s in [k+2 .. n-1]  (exact, both engines)
  - s* = first s with maxI <= budget(=n)
  - c* = s*-k, and whether s* is at/below the antipodal floor n/2-1 or ABOVE it
  - the maximizing direction (a,b): is it still antipodal-adjacent (n/2,n/2-1) or something new?

EXACT full (a,b) sweep, multi-prime (mult=4,5) p-independence, PROPER mu_n, p>>n^3, p==1 mod n,
NEVER n=q-1.  Exclude correlated dirs X^{n/2}=+-1 implicitly by tracking which (a,b) wins.
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

def profile_and_winner(n,k,p,mu,budget):
    """full (a,b) sweep per s; returns (sstar, {s:(maxI,argmax(a,b))})."""
    prof={}; sstar=None
    for s in range(k+2, n):
        best=0; arg=None
        for a in range(1,n):
            for b in range(1,n):
                if a==b: continue
                I=inc(a,b,n,k,p,s,mu)
                if I<p and I>best: best=I; arg=(a,b)
        prof[s]=(best,arg)
        if best<=budget and sstar is None: sstar=s
    return sstar, prof

if __name__=='__main__':
    print("=== SECOND HORN boundary: k -> n/2 (rho -> 1/2) ===", flush=True)
    # Sweep k from n/4 up toward n/2-1, watching c* and the maximizer direction.
    for n in [16, 20, 24]:
        budget=n
        anti_floor = n//2 - 1   # antipodal binding witness size s*
        print(f"\n--- n={n}, antipodal s*-floor = n/2-1 = {anti_floor}, budget={budget} ---", flush=True)
        for k in range(n//4, n//2):       # rho from 1/4 up to just below 1/2
            rho=k/n
            results=[]
            for mult in [4,5]:
                p=find_prime(n,mult); mu=setup(n,p)
                ss,prof=profile_and_winner(n,k,p,mu,budget)
                results.append((p,ss,prof))
            p0,ss0,pr0=results[0]; p1,ss1,pr1=results[1]
            pind=(ss0==ss1)
            if ss0 is None:
                # no crossing in band: maxI stays above budget for ALL s up to n-1 => UNDER-determined / re-couple
                lasts=n-1; lastI=pr0[lasts][0] if lasts in pr0 else None
                print(f" k={k} rho={rho:.3f} c*: NO-CROSS-in-band (maxI>budget all s; I({lasts})={lastI}) "
                      f"=> candidate RE-COUPLE/under-det p-indep={pind}", flush=True)
                continue
            c=ss0-k
            win=pr0[ss0][1]
            # is s* at/below antipodal floor (deep over-det, FIRST horn) or strictly above (re-couple)?
            horn = "FIRST(deep-overdet)" if ss0 <= anti_floor else "SECOND(re-couple?)"
            print(f" k={k} rho={rho:.3f} budget={budget}: s*={ss0} c*={c} c*/n={c/n:+.3f} "
                  f"delta*={(n-ss0)/n:.4f} win(a,b)={win} vs-anti-floor({anti_floor}):{horn} "
                  f"p-indep={pind}", flush=True)
    print("\n=== READING: FIRST horn while s*<=n/2-1 (antipodal binds, c*=Theta(n)). "
          "When k grows so that antipodal floor n/2-1 < k+2 (k>n/2-3), the crossing must MOVE: "
          "either s* jumps ABOVE n/2-1 (re-couple/SECOND horn) or no crossing (under-det). "
          "The k where this flips = the SECOND-HORN BOUNDARY.", flush=True)
    print("DONE", flush=True)
