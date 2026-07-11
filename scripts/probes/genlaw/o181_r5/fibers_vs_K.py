#!/usr/bin/env python3
"""
C1 KEY TEST:  is #fibers (= #distinct joint (c1,c2) over line-forced sets) <= K ?
If yes for ALL lines (worst case), then since #bad <= #fibers, the level-set
count (which incidence/Mansfield-Mudgal CAN bound -- it counts nonempty fibers
via the |V_i| dyadic decomposition) would give #bad <= K.
We sweep ALL monomial lines (e,f) at each r, take the WORST #fibers, compare to K.
This is the make-or-break calibration for the forward lead.
"""
import itertools, sys
from math import comb
import fiber_probe as fp

def worst_fibers(n,r):
    dom=fp.make_dom(n)
    k=(r-2)+1; a0=r+1
    K=(1<<r)*comb(n//2,r)
    best_fib=0; best_bad=0; arg_fib=None; arg_bad=None
    best_fib_at_badmax=0
    for e in range(n):
        for f in range(n):
            if e==f: continue
            U0=[fp.powm(dom[i],e) for i in range(n)]
            U1=[fp.powm(dom[i],f) for i in range(n)]
            fibers=set(); bad=set()
            for S in itertools.combinations(range(n),a0):
                ok,hg,gam=fp.aligned_gamma(dom,k,list(S),U0,U1)
                if not ok or not hg: continue
                c1=sum(dom[i] for i in S)%fp.P
                c2=sum(dom[i]*dom[i]%fp.P for i in S)%fp.P
                fibers.add((c1,c2)); bad.add(gam)
            nf=len(fibers); nb=len(bad)
            if nf>best_fib: best_fib=nf; arg_fib=(e,f)
            if nb>best_bad: best_bad=nb; arg_bad=(e,f); best_fib_at_badmax=nf
    return K,best_fib,arg_fib,best_bad,arg_bad,best_fib_at_badmax

if __name__=="__main__":
    n=int(sys.argv[1]) if len(sys.argv)>1 else 16
    rmax=int(sys.argv[2]) if len(sys.argv)>2 else 8
    print(f"=== n={n}: worst-over-lines #fibers vs K (and worst #bad) ===")
    print(f"{'r':>2} {'K':>8} {'worst#fib':>9} {'fib<=K':>6} {'argfib':>9} {'worst#bad':>9} {'argbad':>9} {'#fib@badmax':>11}")
    for r in range(3,rmax+1):
        K,bf,af,bb,ab,fbm=worst_fibers(n,r)
        print(f"{r:>2} {K:>8} {bf:>9} {str(bf<=K):>6} {str(af):>9} {bb:>9} {str(ab):>9} {fbm:>11}")
        sys.stdout.flush()
