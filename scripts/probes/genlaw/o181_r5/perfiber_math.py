#!/usr/bin/env python3
"""
C1 -- the precise per-fiber math, calibrated against exact data.

Three candidate per-fiber/level-set bounds and what each yields for #bad:

(I)  TRIVIAL per-fiber:   r_s(c1,c2) = |h_{m,n} cap (A x A)| <= |A| = n.
     -> gives only #fibers >= L/n  (LOWER bound on support). USELESS for #bad upper.

(II) M-M level-set:       |V_i| << |A|^7 (2^i Delta)^{-11/2}   (# fibers of size ~2^i Delta).
     This is the only 'per-fiber-distribution' statement M-M proves.  It feeds the
     SUMMED energy  J_s = sum r_s^2.  It does NOT bound the SUPPORT |{(c1,c2):r_s>0}|
     nor its c1-projection #bad.  (A fiber of size 1 is invisible to V_i for i>=1.)

(III) Cauchy-Schwarz from energy:  L^2 <= #fibers * J_s  =>  #fibers >= L^2/J_s.
     LOWER bound on #fibers.  And  #bad <= #fibers  is an UPPER bound on #bad in
     terms of #fibers -- but #fibers itself is only LOWER-bounded by J_s.  So the
     energy direction and the support direction are OPPOSITE.  No chaining closes.

We confirm numerically that:
  - max_fiber N2 << n  (trivial bound (I) hugely slack, no help)
  - the c1-projection support #bad is NOT controlled by J_s in the right direction:
      J_s/ (n choose 2)  etc. give LOWER bounds that under/over-shoot #bad randomly.
"""
import itertools
from math import comb
import fiber_probe as fp

def fibers_of(n,r,e,f,restrict=True):
    dom=fp.make_dom(n); k=(r-2)+1; a0=r+1
    U0=[fp.powm(dom[i],e) for i in range(n)]
    U1=[fp.powm(dom[i],f) for i in range(n)]
    fib={}; c1set=set(); L=0
    for S in itertools.combinations(range(n),a0):
        if restrict:
            ok,hg,gam=fp.aligned_gamma(dom,k,list(S),U0,U1)
            if not ok or not hg: continue
        L+=1
        c1=sum(dom[i] for i in S)%fp.P
        c2=sum(dom[i]*dom[i]%fp.P for i in S)%fp.P
        fib[(c1,c2)]=fib.get((c1,c2),0)+1; c1set.add(c1)
    return fib,len(c1set),L

if __name__=="__main__":
    cases=[(16,3,8,7),(16,4,8,5),(16,5,9,15),(16,6,8,10),(16,7,10,15),(16,8,9,11)]
    exact={3:97,4:145,5:89,6:113,7:225,8:104}
    print("=== per-fiber bound (I) trivial vs reality, line-forced maximizer ===")
    print(f"{'r':>2} {'#bad':>5} {'K':>6} {'maxN2':>6} {'n=|A|':>6} {'(I)slack=n/maxN2':>16}")
    for n,r,e,f in cases:
        fib,nbad,L=fibers_of(n,r,e,f,True)
        mx=max(fib.values())
        print(f"{r:>2} {nbad:>5} {(1<<r)*comb(n//2,r):>6} {mx:>6} {n:>6} {n/mx:>16.1f}")
    print()
    print("=== direction check: energy J_s gives only LOWER bounds for support ===")
    print(f"{'r':>2} {'#bad':>5} {'#fib':>6} {'Js':>6} {'L^2/Js(>=#fib)':>14} {'L/n(>=#fib?)':>13}")
    for n,r,e,f in cases:
        fib,nbad,L=fibers_of(n,r,e,f,True)
        nfib=len(fib); Js=sum(v*v for v in fib.values())
        print(f"{r:>2} {nbad:>5} {nfib:>6} {Js:>6} {L*L//Js:>14} {L//n:>13}")
