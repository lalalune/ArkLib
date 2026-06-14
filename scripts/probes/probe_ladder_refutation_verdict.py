#!/usr/bin/env python3
"""FINAL: summarize the refutation status of the average-term, with the precise rate dependence.
The ladder (the ONLY explicit adversarial bad family that reaches below the deep band) certifies
bad radii BELOW the average-term ONLY for rho < 1/2 (antipodal halving needs r <= s/2 i.e. rho <= 1/2,
with equality vacuous). And ONLY if the char-0 fibre count transfers to F_q (the open hndvd wall)."""
from math import log2, log, lgamma
def H2(x):
    if x<=0 or x>=1: return 0.0
    return -x*log2(x)-(1-x)*log2(1-x)
def log2C(N,k):
    if k<0 or k>N: return -1e18
    if k==0 or k==N: return 0.0
    return (lgamma(N+1)-lgamma(k+1)-lgamma(N-k+1))/log(2)
import math
def avg_term(rho, nbits):
    log2q=128+nbits
    def h2nat(x):
        if x<=0 or x>=1: return 0.0
        return -x*math.log(x)-(1-x)*math.log(1-x)
    lnq=log2q*log(2); y=1-rho-(128.0/log2q)/(2**nbits); x=y
    for _ in range(100): x=y-h2nat(x)/lnq
    return x
def deepest_bad_ladder(rho, nbits):
    n=2**nbits; log2B=nbits; best=None; s=4
    while s<=n:
        r=round(rho*s)+2
        if 2<=r<=s//2:
            li=r+log2C(s//2,r); radius=1-r/s
            if li>log2B and (best is None or radius<best[0]):
                best=(radius,s,r,li)
        s*=2
    return best

print("VERDICT TABLE: ladder bad-radius vs average-term (Johnson < window < capacity)")
print(f"{'rho':>6} {'nbits':>5} {'Johnson':>8} {'ladder_bad':>11} {'avg_term':>9} {'cap':>7} {'REFUTES avg?':>13}")
for rho in [0.5,0.25,0.125,0.0625]:
    for nbits in [20,30,40]:
        J=1-rho**0.5; cap=1-rho; A=avg_term(rho,nbits); L=deepest_bad_ladder(rho,nbits)
        if L:
            lr=L[0]
            refute = (lr < A) and (lr > J)   # below avg-term AND still in window (above Johnson)
            print(f"{rho:>6} {nbits:>5} {J:>8.4f} {lr:>11.5f} {A:>9.5f} {cap:>7.4f} "
                  f"{'YES (if transfer)' if refute else ('below-J!' if lr<=J else 'no')}")
        else:
            print(f"{rho:>6} {nbits:>5} {J:>8.4f} {'(none)':>11} {A:>9.5f} {cap:>7.4f} {'NO ladder':>13}")
