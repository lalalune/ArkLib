#!/usr/bin/env python3
"""
C1 DECISIVE per-fiber analysis (cycle2, #232/#334 demand lane).

GOAL: settle whether the Mansfield-Mudgal incidence machinery can be turned
into a PER-FIBER N2(c1,c2) bound that yields #bad <= K for general r.

DICTIONARY (exact identification with M-M arXiv:2310.02950):
  A      = mu_n  (the n-th roots of unity in F_p), s = r+1 = a0
  n=(n1,n2)=(c1,c2)  the joint (e1,e2)=(sum x, sum x^2) of an (r+1)-subset
  r_s(c1,c2) = #{ subsets S, |S|=a0 : sum_{x in S} x=c1, sum x^2=c2 }   [eqn 2.3]
             = our FIBER count N2(c1,c2) RESTRICTED to line-forced S
  J_s        = sum_fiber r_s^2  [eqn 2.4]  = our collisionCount
  sum_fiber r_s = |A|^s = C(n,a0)            [eqn 2.4]
  support(r_s) subset of sA x (Fp)            (line 433)
  #bad       = | proj_1 ( support(r_s|line-forced) ) |   (distinct c1)

We measure for each MAXIMIZING line (worst #bad), and ALSO the worst #fibers line,
ALL the quantities a per-fiber / level-set argument could use, and compare to K.

This reuses fiber_probe.aligned_gamma (the validated line-forcing test).
"""
import itertools, sys
from math import comb
import fiber_probe as fp

def analyze_line(n,r,e,f, restrict=True):
    """restrict=True -> only line-forced S (the actual #bad object).
       restrict=False -> ALL a0-subsets (the raw M-M r_s over mu_n)."""
    dom=fp.make_dom(n)
    k=(r-2)+1; a0=r+1
    U0=[fp.powm(dom[i],e) for i in range(n)]
    U1=[fp.powm(dom[i],f) for i in range(n)]
    fibers={}; bad=set(); Lcount=0
    c1set=set(); c2set=set()
    for S in itertools.combinations(range(n),a0):
        if restrict:
            ok,hg,gam=fp.aligned_gamma(dom,k,list(S),U0,U1)
            if not ok or not hg: continue
        Lcount+=1
        c1=sum(dom[i] for i in S)%fp.P
        c2=sum(dom[i]*dom[i]%fp.P for i in S)%fp.P
        fibers[(c1,c2)]=fibers.get((c1,c2),0)+1
        c1set.add(c1); c2set.add(c2)
        if restrict: bad.add(gam)
        else: bad.add((-c1)%fp.P)
    nfib=len(fibers); coll=sum(v*v for v in fibers.values())
    maxN2=max(fibers.values()) if fibers else 0
    nbad=len(bad)
    K=(1<<r)*comb(n//2,r)
    return dict(nbad=nbad,nfib=nfib,coll=coll,maxN2=maxN2,L=Lcount,
                nc1=len(c1set),nc2=len(c2set),K=K)

if __name__=="__main__":
    # n=16 maximizing lines (worst #bad)
    cases=[(16,3,8,7),(16,4,8,5),(16,5,9,15),(16,6,8,10),(16,7,10,15),(16,8,9,11)]
    exact_bad={3:97,4:145,5:89,6:113,7:225,8:104}
    print("=== n=16, maximizing line (line-forced restriction = the real #bad object) ===")
    print(f"{'r':>2} {'#bad':>5} {'exact':>5} {'K':>6} {'bad<=K':>6} {'#fib':>6} {'fib<=K':>6} "
          f"{'maxN2':>5} {'coll=Js':>8} {'#c1':>5} {'#c2':>5} {'L':>6}")
    for n,r,e,f in cases:
        d=analyze_line(n,r,e,f,restrict=True)
        ok = "OK" if d['nbad']==exact_bad[r] else "MISMATCH!"
        print(f"{r:>2} {d['nbad']:>5} {exact_bad[r]:>5} {d['K']:>6} {str(d['nbad']<=d['K']):>6} "
              f"{d['nfib']:>6} {str(d['nfib']<=d['K']):>6} {d['maxN2']:>5} {d['coll']:>8} "
              f"{d['nc1']:>5} {d['nc2']:>5} {d['L']:>6}  {ok}")
    print()
    print("=== same lines, UNRESTRICTED (raw M-M r_s over all a0-subsets of mu_n) ===")
    print(f"{'r':>2} {'#c1':>6} {'c1<=K':>6} {'#fib':>7} {'fib<=K':>6} {'maxN2':>6} {'coll=Js':>10} {'C(n,a0)':>9}")
    for n,r,e,f in cases:
        d=analyze_line(n,r,e,f,restrict=False)
        print(f"{r:>2} {d['nc1']:>6} {str(d['nc1']<=d['K']):>6} {d['nfib']:>7} {str(d['nfib']<=d['K']):>6} "
              f"{d['maxN2']:>6} {d['coll']:>10} {comb(n,r+1):>9}")
