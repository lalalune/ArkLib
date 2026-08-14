#!/usr/bin/env python3
"""FAST (n<=16 only): census multiplicity excess vs band depth. Direct full census
per band, exact. Verifies the landed partition #alignableSets=#bad+excess and whether
the excess (per-gamma multiplicity surplus) is concentrated/grows in deeper bands.
Proper mu_n, p>>n^3, p=1 mod n, NEVER n=q-1."""
import itertools
from collections import defaultdict

def setup(a,beta=4):
    n=2**a;p=n**beta+1
    while True:
        p+=1
        if (p-1)%n: continue
        if all(p%d for d in range(2,int(p**0.5)+1)): break
    for c in range(2,p):
        o=1;y=c%p
        while y!=1:y=(y*c)%p;o+=1
        if o==p-1:g=c;break
    h=pow(g,(p-1)//n,p)
    return p,n,[pow(h,i,p) for i in range(n)]
def inv(x,p):return pow(x%p,p-2,p)
def dd(t,u,dom,p):
    s=0
    for b in range(len(t)):
        d=1;pb=dom[t[b]]
        for c in range(len(t)):
            if c!=b:d=(d*(pb-dom[t[c]]))%p
        s=(s+u[t[b]]*inv(d,p))%p
    return s
def census(a_exp,k,A,B,beta=4):
    p,n,dom=setup(a_exp,beta)
    u0=[pow(dom[i],A,p) for i in range(n)];u1=[pow(dom[i],B,p) for i in range(n)]
    print(f"\n== n={n} k={k} (A,B)=({A},{B}) p={p} ==")
    for band in range(k+1,n+1):
        owner=defaultdict(int);total=0
        for S in itertools.combinations(range(n),band):
            gam=None;ok=True;nd=False
            for t in itertools.combinations(S,k+1):
                D0=dd(t,u0,dom,p);D1=dd(t,u1,dom,p)
                if D0 or D1:nd=True
                if D1==0:
                    if D0:ok=False;break
                    continue
                gt=(-D0*inv(D1,p))%p
                if gam is None:gam=gt
                elif gam!=gt:ok=False;break
            if ok and nd and gam is not None:
                total+=1;owner[gam]+=1
        if total==0: 
            print(f"  band={band}: empty (no aligned a-sets) -> #bad=0");break
        mults=sorted(owner.values(),reverse=True)
        excess=total-len(owner)
        print(f"  band={band}: #incidence={total} #distinct_gamma(#bad)={len(owner)} "
              f"excess={excess} maxmult={mults[0]} ratio_inc/bad={total/len(owner):.2f}")
if __name__=="__main__":
    census(3,2,3,4);census(4,2,5,7);census(4,3,5,9)
