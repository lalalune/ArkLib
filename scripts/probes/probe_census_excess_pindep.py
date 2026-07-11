#!/usr/bin/env python3
"""p-independence check of the census excess collapse at deep bands (n=16 k=3,
band 4..8): re-run at a SECOND prime to confirm the distinct-gamma collapse + the
incidence/bad ratio are p-independent structural facts (not artifacts)."""
import itertools
from collections import defaultdict
def nextp(n,start):
    p=start
    while True:
        p+=1
        if (p-1)%n: continue
        if all(p%d for d in range(2,int(p**0.5)+1)): return p
def setup_p(n,p):
    for c in range(2,p):
        o=1;y=c%p
        while y!=1:y=(y*c)%p;o+=1
        if o==p-1:g=c;break
    h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]
def inv(x,p):return pow(x%p,p-2,p)
def dd(t,u,dom,p):
    s=0
    for b in range(len(t)):
        d=1;pb=dom[t[b]]
        for c in range(len(t)):
            if c!=b:d=(d*(pb-dom[t[c]]))%p
        s=(s+u[t[b]]*inv(d,p))%p
    return s
def run(n,k,A,B,p):
    dom=setup_p(n,p)
    u0=[pow(dom[i],A,p) for i in range(n)];u1=[pow(dom[i],B,p) for i in range(n)]
    res=[]
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
            if ok and nd and gam is not None: total+=1;owner[gam]+=1
        if total==0:break
        res.append((band,total,len(owner)))
    return res
if __name__=="__main__":
    n,k,A,B=16,3,5,9
    for p in [nextp(n,16**4), nextp(n,16**4+5000), nextp(n,3*16**4)]:
        r=run(n,k,A,B,p)
        print(f"p={p}: "+ " ".join(f"b{b}:inc{t}/bad{o}" for b,t,o in r))
