#!/usr/bin/env python3
"""
#407 ANOMALY SUPPRESSION — combined-axes test at the WORST in-window bad prime.

Result-2 (in-window suppression) was at FIXED r=4. onset_growth tracks the r-axis at a representative
prime. This probe combines both: take an in-window bad prime p (beta~4, p>=n^4), and track the FULL
suppression trajectory  ratio_r = Anom_r(p) / (n^{2r}/p)  for r=2..r*  with r* = round(log p) (the
moment-optimizer depth). If ratio_r <= 1 for ALL r up to r*, suppression survives at the optimizer depth
(the strongest accessible-scale survival statement for the anomaly route at that prime). We also report
A_r/Wick (the actual target) and R_r/Wick (char-0 Lam-Leung floor) for context.

Anom_r = E_r^(p) - E_r^(0); E_r^(0) (ring count) via integer lattice convolution. Exact, FFT integer count.
HONEST: sub-prize p (the prime budget is p~2^128); maps the trajectory, does not prove asymptotic.
"""
import numpy as np, math
from itertools import combinations_with_replacement
from collections import Counter

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True

def primroot(p):
    def pf(mm):
        f=set(); d=2; m=mm
        while d*d<=m:
            while m%d==0: f.add(d); m//=d
            d+=1
        if m>1: f.add(m)
        return f
    fs=pf(p-1); g=2
    while any(pow(g,(p-1)//q,p)==1 for q in fs): g+=1
    return g

def roots_modp(n,p):
    g=primroot(p); w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]

def lattice_vec(ms,n):
    phi=n//2; v=[0]*phi
    for e in ms:
        if e<phi: v[e]+=1
        else: v[e-phi]-=1
    return tuple(v)

def E0_ring(n,r):
    phi=n//2
    base=[lattice_vec((e,),n) for e in range(n)]
    dist=Counter()
    for c in base: dist[c]+=1
    for _ in range(r-1):
        nd=Counter()
        for s,cnt in dist.items():
            for c in base:
                nd[tuple(s[k]+c[k] for k in range(phi))]+=cnt
        dist=nd
    return sum(v*v for v in dist.values())

def Ep(mu,p,r):
    base=np.zeros(p,dtype=np.int64)
    for x in mu: base[x%p]+=1
    fb=np.fft.rfft(base.astype(float))
    res=base.astype(float).copy()
    for _ in range(r-1):
        res=np.fft.irfft(np.fft.rfft(res)*fb,n=p)
    res=np.rint(res).astype(np.int64)
    return int(np.sum(res.astype(object)**2))

def doublefact(m):
    r=1
    while m>0: r*=m; m-=2
    return r
def wick(n,r): return doublefact(2*r-1)*n**r

# worst in-window bad prime found earlier for n=16 r=4: p=76001 (beta=4.05). Use it + a couple neighbors.
CASES = [(16, 76001), (16, 65537), (16, 94529)]
print("="*78)
print("SUPPRESSION TRAJECTORY along r at fixed in-window bad prime (n=16). r* = round(log p), capped at 7 (E0 ring-count tractable).")
print("ratio_r = Anom_r/(n^2r/p);  A_r/Wick = actual target;  suppression survives iff ratio_r<=1 to r*.")
print("="*78)
for n,p in CASES:
    if not is_prime(p): 
        print(f"p={p} not prime, skip"); continue
    mu=roots_modp(n,p)
    beta=math.log(p)/math.log(n)
    rstar=min(7,max(2,round(math.log(p))))
    print(f"\n### n={n} p={p} beta={beta:.2f}  r*=round(log p)={rstar}")
    print(f"{'r':>3} {'Anom_r':>14} {'n^2r/p':>14} {'ratio':>9} {'A_r/Wick':>9} {'verdict':>10}")
    survive=True
    for r in range(2, rstar+1):
        E0=E0_ring(n,r)
        Epp=Ep(mu,p,r)
        anom=Epp-E0
        DC=(n**(2*r))/p
        ratio=anom/DC if DC>0 else float('inf')
        Ar=Epp-DC
        ArW=Ar/wick(n,r)
        ok = ratio<=1+1e-9
        if not ok: survive=False
        print(f"{r:>3} {anom:>14d} {DC:>14.3e} {ratio:>9.4f} {ArW:>9.4f} {'HOLDS' if ok else 'VIOLATED':>10}")
    print(f"  => suppression {'SURVIVES to r* (all ratio<=1)' if survive else 'FAILS before r* (ratio crosses 1)'}")
