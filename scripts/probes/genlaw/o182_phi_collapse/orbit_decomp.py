#!/usr/bin/env python3
"""Decompose Phi-image into orbits under gamma -> g*gamma (rotation, order n)
and gamma -> -gamma (antipode, = g^{n/2}*gamma, ALREADY inside the rotation group).
So the rotation group C_n already contains negation. The image = disjoint union of
C_n-orbits + {0}. Orbit size divides n. #bad = sum of orbit sizes + 1(for 0)."""
import collections, sys
from math import comb
P=2013265921
def make_dom(n):
    e=(P-1)//n
    for c in range(2,300):
        h=pow(c,e,P)
        if pow(h,n,P)==1 and pow(h,n//2,P)!=1:
            cur=1; d=[]
            for _ in range(n): d.append(cur); cur=cur*h%P
            return d,h
def parse(l):
    d={}
    for tok in l.replace('|',' ').split():
        if '=' in tok:
            k,v=tok.split('=',1)
            try: d[k]=int(v)
            except: pass
    return d
exact={3:97,4:145,5:89,6:113}
for r in range(3,7):
    R=[parse(l) for l in open(f"r{r}_struct.txt") if l.startswith('S ')]
    n=16; dom,g=make_dom(n)
    gset=set(x['gam'] for x in R)
    # orbits under mult by g
    seen=set(); orbits=[]
    for gam in gset:
        if gam in seen: continue
        orb=[]; v=gam
        while v not in seen:
            seen.add(v); orb.append(v); v=v*g%P
        # only keep elements actually in the image (orbit may exit image if not closed)
        orbits.append(orb)
    sizes=collections.Counter(len(o) for o in orbits)
    # verify image is union of FULL C_n orbits (each orbit fully in image)
    full_closed=all(all((v in gset) for v in o) for o in orbits)
    K=(1<<r)*comb(n//2,r)
    nbad=len(gset)
    print(f"r={r} #bad={nbad}(exact {exact[r]}) K={K} #orbits={len(orbits)} orbit-size-hist={dict(sorted(sizes.items()))} full_Cn_closed={full_closed}")
    # the brief decomposition: 1 + (n/2)*full_orb  where full_orb = #(size-?) orbits
    # Count orbits of each size
