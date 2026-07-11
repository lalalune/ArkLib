# probe_fractional_moment_avg_vs_max.py (#444) — settles the multiplicative-chaos / Harper
# "better than squareroot cancellation" lead (the one lead with a structural reason to escape the
# phase-blind integer-moment floor). FINDING (2026-06-21): the max-from-moment bound (p*A_q)^{1/2q},
# A_q=E_{b!=0}|eta_b|^{2q}, is MONOTONE DECREASING in q — best as q->inf (= M itself, tautological),
# and fractional q<1 give CATASTROPHICALLY worse bounds (q=0.25 -> 10^10). So Harper's better-than-sqrt
# is a LOW-moment / AVERAGE phenomenon; our M is the worst-case MAX, detected only by HIGH moments.
# The mult-chaos/fractional-moment method controls the typical period (sub-iid, C_iid<1) but gives
# NOTHING for the max, which needs the high-moment/deep-depth control = the phase-blind floor = the wall.
# The optimal moment for M<=sqrt(2n log p) is q~log p (the saddle = integer-moment-at-depth-log-p = the
# wall), NOT q<1. CONCLUSION: the most-promising-looking lead REDUCES, for the average-vs-max reason.

import numpy as np
from math import log, sqrt
def is_prime(N):
    if N<2:return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41):
        if N%q==0:return N==q
    d=N-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,N)
        if x in(1,N-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%N
            if x==N-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fac.add(d);m//=d
        d+=1
    if m>1:fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def subgroup(p,n):
    g=primroot(p);w=pow(g,(p-1)//n,p);S=[];x=1
    for _ in range(n):S.append(x);x=x*w%p
    return S
def etas(p,n):
    roots=np.array(subgroup(p,n)); b=np.arange(1,p)
    out=np.empty(p-1)
    BL=20000
    for i in range(0,p-1,BL):
        bb=b[i:i+BL][:,None]
        out[i:i+bb.shape[0]]=np.abs(np.exp(2j*np.pi*((bb*roots[None,:])%p)/p).sum(axis=1))
    return out

print("FRACTIONAL-MOMENT max-bound: M <= (p*A_q)^{1/2q}, A_q=E_{b!=0}|eta_b|^{2q}. Best q minimizes it.")
print("Harper better-than-sqrt lives at q<1; the MAX may need q>1. Which q wins?")
print("="*72)
for n,p in [(16,65537),(32,1048609)]:
    E=etas(p,n); M=E.max()
    print(f"\nn={n} p={p}: actual M={M:.3f} (M/sqrt(n)={M/sqrt(n):.3f}, M/sqrt(n log p)={M/sqrt(n*log(p)):.3f})")
    print(f"  {'q':>5} {'A_q':>12} {'(p A_q)^(1/2q)':>15} {'/M':>7}")
    for q in (0.25,0.5,0.75,1.0,1.5,2.0,3.0,5.0,8.0):
        Aq=np.mean(E**(2*q))
        bound=(p*Aq)**(1/(2*q))
        print(f"  {q:>5.2f} {Aq:>12.2e} {bound:>15.3f} {bound/M:>7.2f}")
print()
print("READING: if the min over q is at q>=1 (and >=n), the fractional moments q<1 give a WORSE max-bound")
print("⟹ mult-chaos/fractional-moment (an AVERAGE/low-moment tool) does NOT help the MAX (needs high moments")
print("= the phase-blind floor). Harper's better-than-sqrt is an AVERAGE phenomenon; M is worst-case = wall.")
