#!/usr/bin/env python3
"""[C8-cosh-mgf-charp-soft] DECISIVE: measure the EFFECTIVE soft constant
   C_eff(y) := 2 log Phi^{nz}(y) / (n y^2),   Phi^{nz}(y) = (1/(q-1)) Sum_{b!=0} cosh(|eta_b| y)
at the Chernoff saddle, vs the floor, and TRACK its scaling to large beta and n.

WHY THIS IS THE CRUX.  The honest Chernoff bound for the max nonzero period is
   M <= inf_y [ log( Sum_{b!=0} cosh(|eta_b| y) ) ] / y
      = inf_y [ log(q-1) + log Phi^{nz}(y) ] / y.
If the SOFT ceiling Phi^{nz}(y) <= exp(C n y^2/2) holds with a CONSTANT C, then
   M <= sqrt( 2 C n log(q-1) ) = floor * sqrt( C * log(q-1)/log m ) = floor * sqrt( C*beta/(beta-1) ).
With C=1 this is floor*sqrt(beta/(beta-1)) ~ 1.155*floor at beta=4 -> WORSE than floor.
=> a CONSTANT C>=1 CANNOT reach the floor through the union-over-all-b Chernoff bound.

BUT the TRUE-periods inf bound came out BELOW the floor (companion probe).  The ONLY way to
reconcile: at the saddle y_chern the EFFECTIVE C_eff(y_chern) must be < (beta-1)/beta < 1, i.e.
the average MGF is strictly sub-Wick because MOST nonzero periods are tiny (~sqrt n), not at the
ceiling.  This probe measures C_eff exactly and asks: as beta,n grow does C_eff stay below the
(beta-1)/beta line (=> mechanism could reach floor) or does it drift up to 1 (=> caps above floor)?

Honesty: this uses the TRUE char-p periods (FFT), so the BOUND is not provable-from-input; the
question is purely DIAGNOSTIC -- is there even ROOM (a sub-(beta-1)/beta C_eff) for a provable
soft-ceiling argument to reach the floor, or is the union-over-b log q penalty structural?
Proper mu_n, multi-prime, p>n^3, never n=q-1.
"""
import math, numpy as np
def isprime(x):
    if x<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if x%q==0:return x==q
    d=x-1;s=0
    while d%2==0:d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        y=pow(a,d,x)
        if y in(1,x-1):continue
        ok=False
        for _ in range(s-1):
            y=y*y%x
            if y==x-1:ok=True;break
        if not ok:return False
    return True
def fac(x):
    f=set();d=2
    while d*d<=x:
        while x%d==0:f.add(d);x//=d
        d+=1
    if x>1:f.add(x)
    return f
def proot(p):
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac(p-1)):return g
def find_prime(n, target):
    p=target-(target%n)+1
    if p<=n+1:p+=n
    for _ in range(5000000):
        if p>n+1 and (p-1)%n==0 and isprime(p):return p
        p+=n
    return None
def periods(p,n):
    g=proot(p);h=pow(g,(p-1)//n,p)
    ind=np.zeros(p);x=1
    for _ in range(n):ind[int(x)]=1.0;x=x*h%p
    return np.abs(np.fft.fft(ind))

print("="*132)
print("C_eff(y)=2 log Phi^{nz}(y)/(n y^2) at the Chernoff saddle.  Phi^{nz}=(1/(q-1))Sum_{b!=0}cosh(|eta_b|y).")
print("If a CONSTANT soft C works, M<=floor*sqrt(C*beta/(beta-1)). To BEAT floor need C_eff(saddle) < (beta-1)/beta.")
print("="*132)
hdr=f"{'n':>5} {'p':>11} {'m':>9} {'beta':>5} {'floor':>8} {'M_true':>8} {'y_chern':>8} {'TRUE_inf':>9} {'inf/floor':>9} {'C_eff@saddle':>12} {'(b-1)/b':>8} {'room?':>6}"
print(hdr)
for n in [8,16,32,64]:
    seen=set()
    tgts=[n**4, n**5, n**6]
    for tg in tgts:
        if tg>8*10**6: continue
        p=find_prime(n,tg)
        if p is None or p in seen or p>8*10**6: continue
        seen.add(p)
        m=(p-1)//n; beta=math.log(p,n)
        absb=periods(p,n); nz=absb[1:]; Mtrue=float(nz.max())
        floor=math.sqrt(2*n*math.log(m))
        q1=len(nz)
        def logsum_cosh(y):
            # log Sum_{b!=0} cosh(|eta_b| y) stably
            a=nz*y
            mx=a.max()
            return mx+math.log(float(np.sum(np.exp(a-mx)+np.exp(-a-mx))))-math.log(2.0)+math.log(2.0)
        # actually Sum cosh = Sum (e^a+e^-a)/2; logsumexp:
        def logsum_cosh2(y):
            a=nz*y
            mx=a.max()
            s=np.sum(np.exp(a-mx))+np.sum(np.exp(-a-mx))
            return mx+math.log(s/2.0)
        def bound(y):
            return logsum_cosh2(y)/y
        ys=np.geomspace(1e-3,4.0,5000)
        vals=[bound(y) for y in ys]
        i=int(np.argmin(vals)); ystar=ys[i]; inf=vals[i]
        # C_eff at the saddle: Phi^{nz}=Sum cosh/(q-1); log Phi = logsumcosh - log(q-1)
        logPhi=logsum_cosh2(ystar)-math.log(q1)
        Ceff=2*logPhi/(n*ystar*ystar)
        bm1=(beta-1)/beta
        room="YES" if Ceff<bm1 else "no"
        print(f"{n:>5} {p:>11} {m:>9} {beta:>5.2f} {floor:>8.3f} {Mtrue:>8.3f} {ystar:>8.3f} {inf:>9.3f} {inf/floor:>9.4f} {Ceff:>12.4f} {bm1:>8.4f} {room:>6}",flush=True)
print()
print("INTERP: 'room?=YES' means C_eff(saddle) < (beta-1)/beta, i.e. the average MGF is sub-Wick ENOUGH that")
print("IF one could prove Phi^{nz}(y)<=exp(C_eff n y^2/2) for that C_eff, the bound would beat the floor.")
print("BUT C_eff<1 is a STATEMENT ABOUT THE AVERAGE, far below the per-b ceiling R_r<=1. The provable input is")
print("R_r<=1 (per-moment, => Phi^{nz}<=exp(ny^2/2), C=1), which gives ONLY 1.155*floor. The gap C_eff vs 1 is")
print("the unclaimed slack: a soft-C proof beating floor MUST control the AVERAGE MGF, not the per-moment ceiling.")
