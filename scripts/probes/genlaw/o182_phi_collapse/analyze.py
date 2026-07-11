#!/usr/bin/env python3
import collections, sys
from math import comb
P=2013265921
def parse(l):
    d={}
    for tok in l.replace('|',' ').split():
        if '=' in tok:
            k,v=tok.split('=',1)
            try: d[k]=int(v)
            except: d[k]=v
    return d
def load(fn):
    return [parse(l) for l in open(fn) if l.startswith('S ')]
exact={3:97,4:145,5:89,6:113,7:225,8:104}
print(f"{'r':>2} {'#LF':>5} {'#bad':>5} {'exact':>5} {'K':>6} {'negclo':>6} {'gam0':>5} "
      f"{'#negorb':>7} {'1+2*po':>7} {'C(8,r)':>7} {'2^r*C':>8} {'antneg':>6} {'frobOK':>6}")
for r in range(3,7):
    R=load(f"r{r}_struct.txt")
    gset=set(x['gam'] for x in R)
    nbad=len(gset)
    negclo=all(((P-g)%P) in gset for g in gset)
    has0=0 in gset
    # negation orbits: pair g with -g
    seen=set(); norb=0; pairorb=0
    for g in gset:
        if g in seen: continue
        ng=(P-g)%P
        seen.add(g); seen.add(ng)
        norb+=1
        if ng!=g: pairorb+=1
    n=16; g=n//4
    K=(1<<r)*comb(n//2,r)
    Cn2r=comb(n//2,r)
    antneg=sum(x['agam_eq_neggam'] for x in R)==len(R)
    frobOK=sum(x['fgam_eq_gam2'] for x in R)
    print(f"{r:>2} {len(R):>5} {nbad:>5} {exact[r]:>5} {K:>6} {str(negclo):>6} {str(has0):>5} "
          f"{norb:>7} {1+2*(norb-(1 if has0 else 0)):>7} {Cn2r:>7} {(1<<r)*Cn2r:>8} {str(antneg):>6} {frobOK:>6}")
