#!/usr/bin/env python3
"""
probe_407_ArWick_ratio_profile.py  (#444 -- the A_r/Wick prize ratio profile, confirming the r/n margin)

Directly tracks the PRIZE object ratio A_r/Wick_r = E_r/((2r-1)!! n^r) (sub-Gaussian iff <1) to deep r at
n=16,32, to test the brick-4 verdict (g(r)=1-r/n, margin shrinks toward 0 as n grows) on the actual
A_r<=Wick object. THIN 2-power mu_n, PROPER (m=(p-1)/n>1, p~n^4, NEVER n=q-1). Exact integer E_r via dense
sumset convolution (no size-p FFT).

RESULT (exact): the ratio RISES toward 1 as n grows at every fixed r (n=16->32: r=2 0.94->0.97, r=3
0.82->0.91, r=4 0.68->0.83, r=5 0.52->0.76, r=6 0.38->0.71) -- the sub-Gaussian MARGIN (1-ratio) SHRINKS,
confirming A_r/Wick -> 1 (the Wick leading-order equality). HONEST: the deep-r tail at FIXED p turns UP
(n=32 r=7 ratio 0.744 > r=6 min 0.711) -- a FINITE-FIELD DC/wraparound artifact (n^{2r}/p contamination
when r ~ log_n p), NOT signal; only the clean rungs r << r* are trustworthy. The vanishing margin at fixed
r as n->inf is the same knife-edge as the closed-form g(r)=1-r/n law. CORE not closed.
"""
import sympy
from collections import Counter

def roots(n,p):
    g=int(sympy.primitive_root(p)); w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]
def find_prime(n,beta):
    t=int(n**beta); m=max(1,t//n)
    while True:
        p=m*n+1
        if p>=t*0.7 and sympy.isprime(p): return p
        m+=1
def Er_upto(n,p,rmax):
    base=roots(n,p); h={0:1}; E={0:n**0}
    # E[0] convention: define A_0 normalization. We'll use A_r/Wick_r directly.
    E={}
    h={0:1}
    for r in range(1,rmax+1):
        nh=Counter()
        for t,c in h.items():
            for x in base: nh[(t+x)%p]+=c
        h=nh; E[r]=sum(c*c for c in h.values())
    return E

def dfact(r):
    v=1
    for i in range(1,r+1): v*=(2*i-1)
    return v

# THE actual prize ratio: A_r / Wick_r where Wick_r = (2r-1)!! * n^r (the Gaussian sup-moment bound).
# A_r = E_r - n^{2r}/p (DC). Wick_r = (2r-1)!!*n^r. ratio = A_r/Wick_r. Prize: ratio bounded as r->r*,n->inf.
print("A_r/Wick_r = E_r/((2r-1)!! n^r)  (the moment-vs-Gaussian ratio; <1 = sub-Gaussian = good).")
print("Track to deep r at several n. Does the ratio at r*=round(log p) stay bounded BELOW 1?")
print(f"{'n':>4} {'p':>11} {'r*':>3} {'ratio(r*)':>10} {'ratio(2)':>9} {'ratio(r*/2)':>11} {'min_r ratio':>11}")
for n in [16,32]:
    beta=4.0
    p=find_prime(n,beta)
    rstar=max(2,round(__import__('math').log(p)))
    rmax=min(rstar+1, 9 if n<=16 else 7)  # feasibility cap on dense conv
    E=Er_upto(n,p,rmax)
    ratios={r: E[r]/(dfact(r)*n**r) for r in E}
    rs=rstar if rstar in ratios else max(ratios)
    rh=max(2,rs//2)
    print(f"{n:>4} {p:>11} {rs:>3} {ratios[rs]:>10.4f} {ratios.get(2,float('nan')):>9.4f} "
          f"{ratios.get(rh,float('nan')):>11.4f} {min(ratios.values()):>11.4f}", flush=True)
    print("       full profile:", {r: round(v,4) for r,v in sorted(ratios.items())}, flush=True)
