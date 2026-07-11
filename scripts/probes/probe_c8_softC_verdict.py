#!/usr/bin/env python3
"""[C8-cosh-mgf-charp-soft] FINAL VERDICT probe. Three things, cleanly separated.

(1) The PROVABLE-INPUT bound. The only soft ceiling with a PROVABLE per-moment certificate is
    R_r := (E_r^Fp - n^2r/p)/((2r-1)!! n^r) <= 1  (companion probe_t1: holds at prize band, slack
    GROWS with r). R_r<=1 for all r <=> Phi^{nz}(y) <= exp(n y^2/2) (C=1, EXACT-Wick generating fn).
    Feeding C=1 into the union-over-all-b Chernoff bound:
        M <= inf_y [log(q-1) + n y^2/2]/y = sqrt(2 n log(q-1)) = floor * sqrt(beta/(beta-1)).
    This is the BEST the per-moment soft ceiling can give. Report this number: ALWAYS > floor.

(2) The TRUE inf bound slides to M_true (the cosh bound log(Sum cosh)/y -> M_true as y->inf), so
    'TRUE_inf < floor' is CIRCULAR (it is essentially M_true). Show inf bound -> M_true by extending y.

(3) The C_eff GAP. At the provable saddle y*=sqrt(2 log(q-1)/n) (C=1 saddle), the AVERAGE
    Phi^{nz}(y*) is FAR below exp(n y*^2/2): C_eff(y*)=2 log Phi^{nz}(y*)/(n y*^2) ~ 0.4 << 1.
    The unclaimed slack is exactly this. A soft-C proof beating the floor would have to bound the
    AVERAGE MGF by exp(C n y^2/2) with C < (beta-1)/beta -- a SECOND-MOMENT-over-b statement, NOT the
    per-b ceiling. Is there a NAMED proven theorem giving that? (We test whether C_eff(y*) is even
    n,beta-STABLE, a necessary condition for any constant-C average bound.)
Proper mu_n, multi-prime, p>n^3, never n=q-1. Diagnostic (uses true FFT periods).
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
def logsum_cosh(nz,y):
    a=nz*y; mx=a.max()
    s=np.sum(np.exp(a-mx))+np.sum(np.exp(-a-mx))
    return mx+math.log(s/2.0)

print("="*140)
print("(1) PROVABLE per-moment soft ceiling R_r<=1 => C=1 => Chernoff bound = sqrt(2 n log(q-1)) = floor*sqrt(beta/(beta-1)).")
print("    Compare: floor, C1_bound(=provable best), M_true, and the IDEALIZED inf (slides to M_true, circular).")
print("="*140)
hdr=f"{'n':>4} {'p':>11} {'beta':>5} {'floor':>8} {'C1_bound':>9} {'C1/floor':>9} {'sqrt(b/(b-1))':>13} {'M_true':>8} {'inf@y=8':>8} {'C_eff(y*)':>10}"
print(hdr)
rows=[]
for n in [8,16,32]:
    seen=set()
    for tg in [n**4,n**5,n**6,n**7]:
        if tg>10**7: continue
        p=find_prime(n,tg)
        if p is None or p in seen or p>10**7: continue
        seen.add(p)
        m=(p-1)//n; beta=math.log(p,n)
        absb=periods(p,n); nz=absb[1:]; Mtrue=float(nz.max()); q1=len(nz)
        floor=math.sqrt(2*n*math.log(m))
        # provable C=1 bound: sqrt(2 n log(q-1))
        C1=math.sqrt(2*n*math.log(q1))
        # C=1 saddle y* = sqrt(2 log(q-1)/n)
        ystar=math.sqrt(2*math.log(q1)/n)
        logPhi=logsum_cosh(nz,ystar)-math.log(q1)
        Ceff=2*logPhi/(n*ystar*ystar)
        # idealized inf, sampled deep (y=8) to show it -> M_true
        infdeep=logsum_cosh(nz,8.0)/8.0
        pen=math.sqrt(beta/(beta-1))
        print(f"{n:>4} {p:>11} {beta:>5.2f} {floor:>8.3f} {C1:>9.3f} {C1/floor:>9.4f} {pen:>13.4f} {Mtrue:>8.3f} {infdeep:>8.3f} {Ceff:>10.4f}",flush=True)
        rows.append((n,beta,Ceff,C1/floor))
print()
print("VERDICT lines:")
print(" - C1_bound/floor == sqrt(beta/(beta-1)) EXACTLY (provable per-moment soft ceiling caps ABOVE floor).")
print(" - inf@y=8 ~ M_true (the 'beats floor' idealized bound is just M_true; circular, not provable).")
print(f" - C_eff(y*) values: {[round(r[2],3) for r in rows]} -- the avg MGF is ~0.4-Wick. STABLE in n,beta? "
      f"range [{min(r[2] for r in rows):.3f},{max(r[2] for r in rows):.3f}].")
print(" - To beat floor one must prove an AVERAGE-MGF bound C<(beta-1)/beta, NOT the per-b ceiling. No named")
print("   theorem supplies a constant-C average-MGF bound for char-p Gauss-period spectra. => soft-C is NOT a handle.")
