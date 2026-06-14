#!/usr/bin/env python3
"""
The SOLE open inequality: Anom_r(p) <= n^{2r}/p.
Equivalently A_r <= Wick is what we WANT, and since A_r = R_r + Anom - n^{2r}/p with R_r<=Wick,
the skeleton claims  Anom <= n^{2r}/p  suffices.

BUT: is  Anom <= n^{2r}/p  even the RIGHT / TIGHT thing?  Note A_r<=Wick is EXACTLY
  R_r + Anom - n^{2r}/p <= Wick  <=>  Anom <= Wick - R_r + n^{2r}/p.
Since R_r<=Wick, we have Wick-R_r>=0, so  Anom <= n^{2r}/p  is SUFFICIENT but possibly
much stronger than needed. The skeleton picks the clean sufficient form.

KEY adversarial questions:
 (Q1) How tight is Anom <= n^{2r}/p in practice? ratio Anom/(n^{2r}/p).
 (Q2) Is the WEAKER necessary-and-sufficient  A_r <= Wick  what we should test instead?
      Measure A_r/Wick directly (the real target).
 (Q3) At what r does A_r/Wick first exceed 1, as a function of beta=log_n(p)?  i.e. the
      saturation threshold the skeleton's STEP 5 flags. Does the OPTIMIZER r*~log p stay
      BELOW that threshold? (If r* > threshold, the bound A_r<=Wick FAILS at the very r we need!)
"""
import numpy as np, math
from math import comb

def doublefact_odd(m):
    r=1
    while m>0: r*=m; m-=2
    return r
def wick(n,r): return doublefact_odd(2*r-1)*n**r

def primroot(p):
    def pf(m):
        f=set(); d=2
        while d*d<=m:
            while m%d==0: f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        return f
    fs=pf(p-1); g=2
    while any(pow(g,(p-1)//q,p)==1 for q in fs): g+=1
    return g

def roots(n,p):
    g=primroot(p); w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]

def coll_r(mu,p,r):
    base=np.zeros(p,dtype=np.int64)
    for x in mu: base[x%p]+=1
    dist=base.copy()
    for _ in range(r-1):
        dist=np.rint(np.fft.irfft(np.fft.rfft(dist)*np.fft.rfft(base),n=p)).astype(np.int64)
    return int(np.sum(dist.astype(object)**2))

# find primes p ≡ 1 mod n in a target beta range
def primes_cong1(n, lo, hi):
    out=[]
    def isp(m):
        if m<2: return False
        d=2
        while d*d<=m:
            if m%d==0: return False
            d+=1
        return True
    k=((lo)//n)
    while True:
        p=k*n+1; k+=1
        if p<lo:
            continue
        if p>hi: break
        if isp(p): out.append(p)
    return out

print("="*78)
print("(Q1)+(Q2)  Anom/(n^2r/p)  and  A_r/Wick  at controlled beta")
print("="*78)
for n in [8,16,32]:
    print(f"--- n={n} ---")
    # pick primes giving beta close to 4 and to ~2.5 (saturated) and large beta
    targets = []
    for beta in [2.5, 3.0, 4.0]:
        target=int(round(n**beta))
        ps=primes_cong1(n, max(target//2, n+1), target*2)
        if ps:
            # choose closest to target
            p=min(ps,key=lambda x:abs(x-target))
            targets.append((beta,p))
    for beta,p in targets:
        mu=roots(n,p)
        beta_eff=math.log(p)/math.log(n)
        rmax=6 if n<=16 else 5
        rowA=[]; rowAnom=[]
        for r in range(2,rmax+1):
            coll=coll_r(mu,p,r)
            W=wick(n,r)
            DC=(n**(2*r))/p
            Ar=coll-DC
            # Anom = coll - R_r ; reuse ring count
            # (recompute ring R_r quickly via DP only for small)
            rowA.append(Ar/W)
        print(f"  beta_eff={beta_eff:.2f} p={p}:  A_r/Wick for r=2..{rmax}: "
              + "  ".join(f"{v:.3f}" for v in rowA))
print()
print("="*78)
print("(Q3) CRITICAL: optimal r* ~ ln p  vs  saturation threshold where A_r/Wick crosses 1.")
print("     A_r/Wick<=1 must hold AT r=r* for the proof to use the bound there.")
print("="*78)
for n in [8,16,32]:
    for beta in [3.0,4.0]:
        target=int(round(n**beta))
        ps=primes_cong1(n,max(target//2,n+1),target*2)
        if not ps: continue
        p=min(ps,key=lambda x:abs(x-target))
        beta_eff=math.log(p)/math.log(n)
        mu=roots(n,p)
        rstar=max(1,int(round(math.log(p))))
        # find crossover r where A_r/Wick first exceeds 1
        cross=None
        for r in range(1, 9):
            coll=coll_r(mu,p,r); W=wick(n,r); Ar=coll-(n**(2*r))/p
            if Ar>W+1e-9:
                cross=r; break
        print(f"  n={n} beta_eff={beta_eff:.2f} p={p}:  r*≈ln p = {rstar}   "
              f"A_r/Wick first exceeds 1 at r = {cross if cross else '>8 (none in range)'}")
