#!/usr/bin/env python3
"""
C1 DECISIVE-DIRECTION TEST.
For the maximizing line, compute the CORRECT Cauchy-Schwarz over the line-forced
set L (not all C(n,a0) subsets):
   |L|^2 <= #fibers * collision        (CS, exact)
   #bad  <= #fibers                    (c1-projection drops c2)
Both give LOWER bounds tied to #fibers; neither upper-bounds #bad.
Also report the per-fiber max-N2 bound and what the BEST conceivable per-fiber
support bound would yield, to show it cannot reach K.
"""
import itertools
from math import comb
import fiber_probe as fp

def run(n,r,e,f):
    dom=fp.make_dom(n)
    k=(r-2)+1; a0=r+1
    U0=[fp.powm(dom[i],e) for i in range(n)]
    U1=[fp.powm(dom[i],f) for i in range(n)]
    fibers={}; bad=set(); Lcount=0
    for S in itertools.combinations(range(n),a0):
        ok,hg,gam=fp.aligned_gamma(dom,k,list(S),U0,U1)
        if not ok or not hg: continue
        Lcount+=1
        c1=sum(dom[i] for i in S)%fp.P
        c2=sum(dom[i]*dom[i]%fp.P for i in S)%fp.P
        fibers[(c1,c2)]=fibers.get((c1,c2),0)+1
        bad.add(gam)
    nfib=len(fibers); coll=sum(v*v for v in fibers.values())
    nbad=len(bad); maxN2=max(fibers.values()) if fibers else 0
    K=(1<<r)*comb(n//2,r)
    # CS over line-forced L:  |L|^2 <= nfib * coll
    cs_lower_fib = (Lcount*Lcount + coll - 1)//coll if coll else 0
    print(f"n={n} r={r} (x^{e},x^{f}): |L|(line-forced sets)={Lcount}  #fib={nfib}  coll={coll}")
    print(f"   #bad={nbad}  K={K}")
    print(f"   CS:  |L|^2/coll = {cs_lower_fib}  <= #fib={nfib}  (CS is a LOWER bound on #fib; {cs_lower_fib<=nfib})")
    print(f"   #bad <= #fib :  {nbad} <= {nfib}  ({nbad<=nfib})   [proj drops c2-stacking]")
    print(f"   max_fiber N2 = {maxN2}")
    # The honest per-fiber-only support bound: even max N2=1 would only give
    # #fib = |L| (each S own fiber); #bad <= #fib still >= |L|/maxN2.
    print(f"   per-fiber-only #bad>= |L|/maxN2 = {Lcount//maxN2 if maxN2 else 0}  (a LOWER bound, not upper)")
    return nbad,nfib,Lcount,coll,maxN2,K

if __name__=="__main__":
    for n,r,e,f in [(16,3,8,7),(16,4,8,5),(16,5,9,15)]:
        run(n,r,e,f); print()
