#!/usr/bin/env python3
"""
#407 — does the thin single-step margin g(r) survive AT THE OPTIMIZER r*=round(log p) as n GROWS?

The reframing: A_r <= Wick <= [base case] + [STEP: A_{r+1}/A_r <= (2r+1)n]. In thin, g(r)=(A_{r+1}/A_r)/
((2r+1)n) <= 1 with margin that GROWS in r at fixed n. The decisive prize-direction question is the OTHER
axis: at the moment-optimizer depth r* ~ log p (where the sup-norm bound is read off), does g(r*) stay
bounded below 1 as n -> infinity (in thin, beta fixed ~4)?  If g(r*) -> some c < 1, encouraging. If
g(r*) -> 1, that's exactly where BGK bites.

We sweep n=8..256 (thin beta~4), compute g at r near r*=round(log p) (and r*-1, r*+1 for trend), exact FFT
spectrum (O(p log p), p~n^4 tractable to n~128-256). Also track M^2/((2r*+1)n) directly (= the sup-side
g-limit, since A_{r+1}/A_r -> M^2). HONEST: accessible n; maps the r* trend, does not prove asymptotic.

RESULT (exact FFT spectrum, thin beta=4, n=8..64):
  n :  r* : g(r*) : M^2/((2r*+1)n) : M^2/(2n ln p)
  8 :  8  : 0.366 : 0.420         : 0.429
  16:  11 : 0.468 : 0.520         : 0.540
  32:  14 : 0.530 : 0.569         : 0.595
  64:  17 : 0.643 : 0.663         : 0.697
HONEST READING (tempers the 'growing margin' optimism): g(r*) stays < 1 (STEP holds at the optimizer) at
ALL accessible n, BUT it INCREASES in n (0.37 -> 0.47 -> 0.53 -> 0.64) -- the margin SHRINKS as n grows.
The r-axis margin grows at FIXED n, but the n-axis margin ERODES toward 1. The prize is the n->inf limit,
so the crossover (does g(r*) saturate below 1 or creep to 1?) is exactly the unresolved BGK content. The
n<=64 trend is sub-linear but CANNOT distinguish 'saturates < 1' from 'creeps to 1'. NO closure; this is a
sober data point, not an extrapolation claim.
"""
import numpy as np, math

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

def roots(n,p):
    g=primroot(p); w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]

def spec_sq(n,p):
    ind=np.zeros(p)
    for x in roots(n,p): ind[x%p]=1.0
    F=np.fft.fft(ind)
    return (F*np.conj(F)).real

def find_prime(n,beta):
    target=int(n**beta); m=max(1,target//n); best=None
    while True:
        p=m*n+1
        if p>target*1.4: break
        if p>=target*0.7 and is_prime(p):
            if best is None or abs(p-target)<abs(best-target): best=p
        m+=1
    return best

print("="*78)
print("THIN single-step margin g(r) at the OPTIMIZER r*=round(log p), swept in n (beta~4).")
print("g(r)=(A_{r+1}/A_r)/((2r+1)n) <=1 ; also M^2/((2r*+1)n) (sup-side limit) and M^2/(2n log p).")
print("="*78)
print(f"{'n':>4} {'p':>10} {'beta':>5} {'r*':>3} {'g(r*-1)':>8} {'g(r*)':>7} {'g(r*+1)':>8} {'M2/((2r*+1)n)':>13} {'M2/(2n ln p)':>12}")
for n in [8,16,32,64]:
    p=find_prime(n,4.0)
    if not p: 
        print(f"{n:>4}  no prime"); continue
    sq=spec_sq(n,p); nz=sq.copy(); nz[0]=0.0
    M2=float(nz.max())
    rstar=max(2,round(math.log(p)))
    be=math.log(p)/math.log(n)
    # need A_r for r=rstar-1 .. rstar+2
    nzl=nz.astype(np.longdouble); _Acache={}
    def Ar(r):
        if r not in _Acache: _Acache[r]=float(np.sum(nzl**r))/p
        return _Acache[r]
    def g(r): return (Ar(r+1)/Ar(r))/((2*r+1)*n)
    try:
        grm1=g(rstar-1); grs=g(rstar); grp1=g(rstar+1)
    except Exception as e:
        grm1=grs=grp1=float('nan')
    supside=M2/((2*rstar+1)*n)
    prizeratio=M2/(2*n*math.log(p))
    print(f"{n:>4} {p:>10} {be:>5.2f} {rstar:>3} {grm1:>8.3f} {grs:>7.3f} {grp1:>8.3f} {supside:>13.3f} {prizeratio:>12.3f}")
