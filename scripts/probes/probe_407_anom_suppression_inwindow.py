#!/usr/bin/env python3
"""
#407 DECISIVE FOLLOW-UP: bad primes DO reach the prize window (beta_bad grows in n; n=32 r=2 -> beta 4.87).
The orchestrator's 'Anom=0 at prize primes' was a small-n artifact. NOW the real BGK question:

   At in-window bad primes (p in [n^4, ...], Anom_r(p) > 0), is the SUPPRESSION BOUND
        Anom_r(p) <= n^{2r}/p
   (the sufficient condition for A_r <= Wick) actually satisfied?

We test EXACTLY at n=16 r=4 and n=32 r=2 (the cases that reach the window), for ALL bad primes
in [n^4, cap]. Anom_r(p) = E_r^(p) - E_r^(0). We get the bad primes as prime factors of norms
(the onset probe), then for each in-window bad prime compute Anom_r(p) exactly via FFT integer
count and the ratio Anom_r/(n^{2r}/p).

If ratio <= 1 at every in-window bad prime: suppression HOLDS empirically (anomaly route survives
at accessible scale). If ratio > 1 anywhere: suppression VIOLATED -> Anom-route bound is FALSE at a
prize-regime prime = a real constraint lemma (DISPROOF) on the anomaly-suppression closure attempt.

RESULT (hardened, exact, n=16 r=4, ALL 26 in-window bad primes p in [n^4=65536, 1.5e6]):
  suppression Anom_4(p) <= n^8/p HELD at 26/26; TRUE WORST ratio = 0.4757 at p=76001 (beta=4.053).
  => even though bad primes invade the prize window (beta_bad grows in n; see norm-onset probe),
     the anomaly is SUPPRESSED there with ~2x margin. The orchestrator's 'Anom=0 at prize primes'
     (n=8) was a small-n artifact (window clean below r=6 there); the SUFFICIENT condition
     A_r <= Wick survives at the in-window bad primes at this accessible scale. POSITIVE for the
     anomaly route. HONEST CAVEAT: sub-prize-budget primes (p <= 1.5e6); maps the in-window worst
     case at fixed r, does NOT prove the asymptotic (worst prize prime at r~log q, p~2^128 = BGK).
"""
import numpy as np, math
from itertools import combinations_with_replacement

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

def norm_of(c,n):
    phi=n//2; prod=1.0+0j
    for k in range(1,n,2):
        w=np.exp(2j*np.pi*k/n)
        prod*= sum(c[j]*(w**j) for j in range(phi))
    re=prod.real; ri=round(re)
    return int(ri)

def factor_primes(m):
    m=abs(m); fs=set(); d=2
    while d*d<=m:
        while m%d==0: fs.add(d); m//=d
        d+=1 if d==2 else 2
    if m>1: fs.add(m)
    return fs

def Ep(mu,p,r):
    base=np.zeros(p,dtype=np.int64)
    for x in mu: base[x%p]+=1
    fb=np.fft.rfft(base.astype(float))
    res=base.astype(float).copy()
    for _ in range(r-1):
        res=np.fft.irfft(np.fft.rfft(res)*fb,n=p)
    res=np.rint(res).astype(np.int64)
    return int(np.sum(res.astype(object)**2))

def E0_ring(n,r):
    from collections import Counter
    phi=n//2; coords=lattice_vec
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

def bad_primes_in_window(n,r,cap):
    """primes p in [n^4, cap], p = m n + 1, that are r-bad (divide some r-collision-difference norm).
    Vectorized: conjugate matrix W[k,j]=w_k^j (k odd), norms = prod over conjugates of (diff @ W.T)."""
    phi=n//2
    ks=[k for k in range(1,n,2)]
    W=np.array([[np.exp(2j*np.pi*k*j/n) for j in range(phi)] for k in ks])  # (phi_conj, phi)
    msets=list(combinations_with_replacement(range(n),r))
    U=np.array(list(set(lattice_vec(ms,n) for ms in msets)),dtype=np.int64)
    L=len(U); primes=set()
    for i in range(L):
        C=(U[i]-U).astype(np.float64)        # (L,phi)
        norms=np.prod(C @ W.T, axis=1).real  # (L,)
        Nr=np.rint(norms).astype(object)
        for idx in range(L):
            N=int(Nr[idx])
            if N==0: continue
            for pf in factor_primes(N):
                if n**4 <= pf <= cap and pf%n==1 and is_prime(pf):
                    primes.add(pf)
    return sorted(primes)

print("="*80)
print("IN-WINDOW SUPPRESSION TEST: Anom_r(p) <= n^{2r}/p at bad primes p in [n^4, cap]")
print("="*80)

# Default: n=16 r=4 hardened sweep (reproduces 26/26 HELD, worst 0.4757 @ p=76001). cap kept
# at 1.5e6 (FFT-tractable). n=32 r=2 reaches the window even harder (beta_bad=4.87) but needs p~2^25
# FFTs; enable by extending the list if you have the compute.
for n,r,cap in [(16,4,1_500_000)]:
    print(f"\n### n={n} r={r}  n^4={n**4}  n^{{2r}}={n**(2*r)} (log2={2*r*math.log2(n):.0f})  cap={cap}")
    E0=E0_ring(n,r)
    bps=bad_primes_in_window(n,r,cap)
    print(f"  E0(ring)={E0}   #in-window bad primes found={len(bps)}")
    if not bps:
        print("  (none in window under cap)"); continue
    worst=(0,None)
    shown=0
    for p in bps:
        mu=roots_modp(n,p)
        anom=Ep(mu,p,r)-E0
        if anom<=0:  # norm divisibility necessary but the specific alpha may still be ring-zero combo
            continue
        DC=(n**(2*r))/p
        ratio=anom/DC
        beta=math.log(p)/math.log(n)
        if ratio>worst[0]: worst=(ratio,p)
        if shown<8:
            flag="HOLDS" if ratio<=1+1e-9 else "*** VIOLATED ***"
            print(f"    p={p} beta={beta:.2f}  Anom={anom}  n^2r/p={DC:.3e}  ratio={ratio:.4f}  {flag}")
            shown+=1
    if worst[1]:
        v="HOLDS (<=1)" if worst[0]<=1+1e-9 else "VIOLATED (>1)"
        print(f"  WORST in window: ratio={worst[0]:.4f} at p={worst[1]} -> suppression {v}")
