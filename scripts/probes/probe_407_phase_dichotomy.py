#!/usr/bin/env python3
"""SHARPEN the cos sign dichotomy: cos01@b* = +1 (thin/prize) vs -1 (thick).
Map the transition: sweep n across the divisor lattice of p-1 for fixed p,
record cos01@b* and the thickness beta=log_n(p). Find where the sign flips.
Also: is cos EXACTLY +-1 (the two coset sums are real-collinear) for ALL b, or only b*?"""
import numpy as np
from numpy.fft import fft

def gen(p):
    fac=set(); x=p-1; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    g=2
    while not all(pow(g,(p-1)//q,p)!=1 for q in fac): g+=1
    return g

def subgroup(p,n):
    g=gen(p); h=pow(g,(p-1)//n,p)
    return [pow(h,i,p) for i in range(n)]

def cos01_at(p,n,bstar=None):
    H=subgroup(p,n); 
    if len(set(H))!=n: return None
    ind=np.zeros(p)
    for x in H: ind[x]=1.0
    if bstar is None:
        F=np.abs(fft(ind)); F[0]=-1; bstar=int(np.argmax(F)); ratio=F[bstar]/np.sqrt(n)
    else: ratio=None
    if n%2: return None
    sq=sorted({(x*x)%p for x in H}); sqset=set(sq)
    rep=next((x for x in H if x not in sqset),None)
    if rep is None: return None
    coset1=sorted({(rep*x)%p for x in sq})
    w=-2*np.pi/p
    S0=sum(np.exp(1j*w*((bstar*x)%p)) for x in sq)
    S1=sum(np.exp(1j*w*((bstar*x)%p)) for x in coset1)
    if abs(S0)<1e-9 or abs(S1)<1e-9: return (bstar,ratio,float("nan"))
    return (bstar,ratio,(S0*np.conj(S1)).real/(abs(S0)*abs(S1)))

# p with many 2-power divisors AND odd part, to sweep thickness
for p in [40961, 786433, 12289]:
    print(f"\n=== p={p}  (p-1={p-1}, beta=log_n p) ===")
    print(f"{'n':>7} {'beta':>5} {'ratio':>6} {'cos01@b*':>9} {'regime':>7}")
    # all divisors n of p-1 that are even and >=4
    pm1=p-1; divs=sorted(d for d in range(4,pm1) if pm1%d==0)
    # subsample
    show=divs[::max(1,len(divs)//18)]
    for n in show:
        r=cos01_at(p,n)
        if r is None: continue
        bstar,ratio,c=r
        beta=np.log(p)/np.log(n)
        reg = "THIN" if beta>=4 else ("thick" if beta<3.2 else "mid")
        print(f"{n:>7} {beta:>5.2f} {ratio if ratio else 0:>6.3f} {c:>9.4f} {reg:>7}")
