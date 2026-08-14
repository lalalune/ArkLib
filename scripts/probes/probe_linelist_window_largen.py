#!/usr/bin/env python3
"""
PROBE (#389): the AFFINE-LINE LIST Lambda across the past-Johnson window, at LARGE n.

Established (probe_amortization.py): worst-case #bad = Lambda exactly (multiplicity 1). So the
delta* floor = bounding the affine-line list Lambda(u0,u1,a) = #{codewords c : agreement(c,u0+g*u1)
>= a for some g}. FAST characterization: c is on the list iff the slope multiset {(c_i-u0_i)/u1_i}
has a value of multiplicity >= a (plus free coords where u1_i=0 & c_i=u0_i). O(n) per codeword =>
n=16,32 feasible, where the past-Johnson window is WIDE.

PRIZE QUESTION read directly: does max-Lambda stay POLY across the window (sqrt(nk), n-k), or BLOW
UP toward q? Poly across window = floor reaches near capacity = prize plausible.
"""
import math, random
from itertools import product
from collections import Counter

def cw(co,D,p):
    o=[]
    for x in D:
        v=0;xp=1
        for c in co: v=(v+c*xp)%p; xp=(xp*x)%p
        o.append(v)
    return tuple(o)
def all_cws(D,k,p): return [cw(co,D,p) for co in product(range(p),repeat=k)]

def line_list(u0,u1,C,p,a,inv):
    n=len(u0); cnt=0
    for c in C:
        free=0; slopes=Counter()
        for i in range(n):
            if inv[i] is None:
                if c[i]==u0[i]: free+=1
            else:
                slopes[((c[i]-u0[i])*inv[i])%p]+=1
        mx = free + (max(slopes.values()) if slopes else 0)
        if mx>=a: cnt+=1
    return cnt

def maxlambda(D,k,p,a,rs,cl,rng):
    C=all_cws(D,k,p);n=len(D);best=0
    for _ in range(rs):
        u0=[rng.randrange(p) for _ in range(n)]
        u1=[rng.randrange(1,p) for _ in range(n)]
        inv=[pow(u1[i],p-2,p) for i in range(n)]
        cur=line_list(u0,u1,C,p,a,inv)
        for _ in range(cl):
            if rng.random()<0.5:
                i=rng.randrange(n);old=u0[i];u0[i]=rng.randrange(p)
                nl=line_list(u0,u1,C,p,a,inv)
                if nl>=cur:cur=nl
                else:u0[i]=old
            else:
                i=rng.randrange(n);old=u1[i];u1[i]=rng.randrange(1,p);inv[i]=pow(u1[i],p-2,p)
                nl=line_list(u0,u1,C,p,a,inv)
                if nl>=cur:cur=nl
                else:u1[i]=old;inv[i]=pow(old,p-2,p)
        best=max(best,cur)
    return best

def mun(p,n):
    if (p-1)%n: return None
    def od(x):
        o=1;c=x%p
        while c!=1:c=(c*x)%p;o+=1
        return o
    g=next((c for c in range(2,p) if od(c)==p-1),None)
    if g is None: return None
    b=pow(g,(p-1)//n,p);d=sorted({pow(b,i,p) for i in range(n)})
    return d if len(d)==n else None

def run(p,n,k,rs,cl,sd=0):
    D=mun(p,n)
    if D is None: print(f"(p={p} n={n}: no mu_n)",flush=True); return
    J=math.sqrt(n*k)
    print(f"\np={p} n={n} k={k} q={p} Johnson agr={J:.2f} capacity agr={k}",flush=True)
    print(f"   {'a':>2} {'reg':>5} | {'maxLambda':>9} {'Lam/n':>6} {'Lam/q':>6}",flush=True)
    for a in range(k+1, math.ceil(J)+1):
        ml=maxlambda(D,k,p,a,rs,cl,random.Random(sd))
        reg = "PAST" if a<J else " - "
        print(f"   {a:>2} {reg:>5} | {ml:>9} {ml/n:>6.2f} {ml/p:>6.3f}",flush=True)
    print(flush=True)

if __name__=="__main__":
    run(p=97, n=16, k=2, rs=30, cl=40)
    run(p=97, n=32, k=2, rs=20, cl=50)
    run(p=193,n=16, k=2, rs=24, cl=44)
    print("===LINEDONE===",flush=True)
