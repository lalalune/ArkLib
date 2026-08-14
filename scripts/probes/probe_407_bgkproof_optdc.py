#!/usr/bin/env python3
"""
THE DECISIVE CHECK: does the DC subtraction actually make the optimization work?

MomentMethodNoGo proves (p*E_r)^{1/2r} >= n, where E_r = coll_r (DC-INCLUDED).
The skeleton claims using A_r = coll_r - n^{2r}/p (DC-SUBTRACTED) escapes this and gives
M <= C sqrt(n log p).

Two things to settle:
 (A) Is M^{2r} <= p*A_r actually TRUE?  (M = max_{b!=0}|eta_b|).
     Parseval: sum_{b!=0}|eta_b|^{2r} = p*A_r.  So M^{2r} <= sum_{b!=0}|eta_b|^{2r} = p*A_r.  TRIVIALLY TRUE.
 (B) Granting A_r <= Wick = (2r-1)!! n^r, minimize over r:  M <= (p (2r-1)!! n^r)^{1/2r}.
     Does the minimum land at ~ C sqrt(n log p)?  And what r achieves it?
 (C) Compare to the DC-INCLUDED bound (p*coll_r)^{1/2r} which NoGo says is >= n.
     Quantify the gap: the DC term n^{2r}/p is what we subtract. Is it the dominant part of coll_r
     at the optimal r?  If coll_r ~ n^{2r}/p (saturation), then A_r is a small difference and the
     subtraction is doing ALL the work -- exactly where bounding A_r is hard.
"""
import numpy as np, math
from math import comb, log, sqrt, exp

def doublefact_odd(m):
    r=1
    while m>0:
        r*=m; m-=2
    return r
def wick(n,r): return doublefact_odd(2*r-1)*n**r

print("="*78)
print("(B) Optimization of the Wick-bound (p*(2r-1)!! n^r)^{1/2r} over r")
print("    [GRANTING A_r<=Wick]  vs  sqrt(2 n ln p)")
print("="*78)
for (n,beta) in [(2**10,4),(2**20,4),(2**30,4),(2**30,5),(2**8,4),(2**8,2.5)]:
    p = n**beta  # prize-shaped, treat as real
    lnp = beta*math.log(n)
    best=None
    for r in range(1, int(3*lnp)+5):
        # bound = (p * (2r-1)!! * n^r)^{1/2r}
        log_bound = (math.log(p) + math.log(doublefact_odd(2*r-1)) + r*math.log(n))/(2*r)
        bound = math.exp(log_bound)
        if best is None or bound<best[1]:
            best=(r,bound)
    target = sqrt(2*n*lnp)
    print(f"n=2^{int(round(math.log2(n)))} beta={beta}: opt r*={best[0]}  Wick-bound={best[1]:.3f}  "
          f"sqrt(2 n ln p)={target:.3f}  ratio={best[1]/target:.4f}  trivial n={float(n):.0f}")
print()
print("Interpretation: if Wick-bound << n and ~ C sqrt(n log p), the OPTIMIZATION is sound")
print("(the deficit vs NoGo's >=n is real BECAUSE we subtracted DC). Check ratio ~ O(1).")
print()

print("="*78)
print("(C) Is coll_r dominated by the DC term n^{2r}/p at the optimal r? (saturation check)")
print("    If so, A_r = coll_r - DC is a near-cancellation and bounding it is the whole game.")
print("="*78)
print("At the optimal r~log p, with the TRUE bound A_r<=Wick:")
print("   DC = n^{2r}/p.  Wick = (2r-1)!! n^r.  ratio DC/Wick = n^r/(p (2r-1)!!).")
for (n,beta) in [(2**10,4),(2**20,4),(2**30,4)]:
    p=n**beta; lnp=beta*math.log(n)
    # optimal r approx ln p
    for r in [int(lnp*0.5), int(lnp), int(lnp*1.5)]:
        if r<1: continue
        logDC = 2*r*math.log(n)-math.log(p)
        logW = math.log(doublefact_odd(2*r-1))+r*math.log(n)
        print(f"  n=2^{int(round(math.log2(n)))} beta={beta} r={r}: "
              f"log10(DC)={logDC/math.log(10):.1f} log10(Wick)={logW/math.log(10):.1f} "
              f"DC/Wick=10^{(logDC-logW)/math.log(10):.1f}")
    print()
