#!/usr/bin/env python3
"""I031 STEP (b)-iv: the REAL open content after metric flatness.

The metric is flat (probe_i031_metric_flatness_vs_collapse): chaining = union bound over m
indices. So M <= C E sup|G_b| reduces to the per-index sub-Gaussian tail of the directional
period Re(zeta_bar * eta_c), uniform over c, with proxy O(n). The matched Gaussian G_b has
EXACTLY this tail with proxy n (real part of complex Gaussian of variance n => variance n/... ),
so the deterministic->Gaussian comparison holds with bounded C IFF the DETERMINISTIC period's
empirical MGF / tail is sub-Gaussian with a proxy that does NOT inflate with n.

THE TEST (the genuine forced-anomaly risk): measure the worst-direction empirical sub-Gaussian
proxy of the period over the quotient,
   sigma2_hat(n) = max_zeta  sup_{lambda>0} (2/lambda^2) log [ (1/m) sum_c exp(lambda Re(zeta_bar eta_c)) ].
Sub-Gaussian with proxy O(n) <=> sigma2_hat(n)/n BOUNDED. If sigma2_hat/n creeps up with n
(or with the relevant lambda* ~ sqrt(2 log m)/sqrt(n) scale, i.e. at the tail depth that the max
union bound actually probes), the comparison constant inflates = back to BGK. If bounded = handle.

Also report the union-bound prediction M_pred = sqrt(2 sigma2_hat log m) and M_pred/M.
PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3.
"""
import math, numpy as np

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True
def find_prime(mu,beta):
    n=1<<mu; lo=int(n**beta); t=((lo//n)+1)*n+1
    while True:
        if isprime(t): return n,t
        t+=n
def subgroup(p,n):
    fac=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fac.append(x)
    g=None
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): g=c;break
    h=pow(g,(p-1)//n,p)
    H=[pow(h,i,p) for i in range(n)]
    assert len(set(H))==n and pow(h,n//2,p)!=1
    return g,h,H

print("I031 STEP(b)-iv: per-index sub-Gaussian proxy of the period over the quotient.")
print("sigma2_hat/n BOUNDED => comparison constant bounded => handle. Creeps => BGK wall.")
print(f"{'n':>4}{'beta':>5}{'p':>10}{'m':>8}  {'M':>7}{'sig2/n':>8}{'lam*':>7}  {'Mpred':>7}{'Mpred/M':>8}{'floor':>7}{'M/floor':>8}")
NDIRS=24
for mu,beta in [(2,4.0),(3,4.0),(4,4.0),(5,4.0),(6,3.6),(7,3.3)]:
    n,p=find_prime(mu,beta)
    g,h,H=subgroup(p,n)
    w=2*math.pi/p; m=(p-1)//n
    Hn=np.array(H,dtype=np.int64)
    reps=np.array([pow(g,c,p) for c in range(m)],dtype=np.int64)
    sampled = m>40000
    if sampled:
        idx=np.linspace(0,m-1,40000).astype(np.int64); reps=reps[idx]
    # eta_c for all reps (chunked)
    eta=np.empty(len(reps),dtype=np.complex128)
    CH=2000
    for i in range(0,len(reps),CH):
        b=reps[i:i+CH][:,None]
        eta[i:i+CH]=np.exp(1j*w*((b*Hn[None,:])%p)).sum(axis=1)
    M=float(np.abs(eta).max())
    # directional real parts: Re(e^{-i theta} eta) = cos t * Re eta + sin t * Im eta
    thetas=np.linspace(0,2*math.pi,NDIRS,endpoint=False)
    Re=eta.real; Im=eta.imag
    # the tail depth the union-bound max actually probes: lambda* ~ sqrt(2 log m)/sigma ~ sqrt(2 log m / n)
    # scan lambda on a grid bracketing that scale; take the proxy at the max-relevant lambda.
    logm=math.log(m)
    lam_star=math.sqrt(2*logm/n)   # natural scale (proxy ~ n)
    lams=np.array([0.25,0.5,0.75,1.0,1.5,2.0,3.0])*lam_star
    best_sig2=0.0; best_lam=0.0
    for t in thetas:
        proj=math.cos(t)*Re+math.sin(t)*Im   # the m directional values (centered ~ mean small)
        proj=proj-proj.mean()
        for lam in lams:
            # empirical MGF
            a=lam*proj
            amax=a.max()
            mgf=np.exp(a-amax).mean()
            logmgf=amax+math.log(mgf)
            sig2=2.0*logmgf/(lam*lam)
            if sig2>best_sig2:
                best_sig2=sig2; best_lam=lam
    sig2_over_n=best_sig2/n
    Mpred=math.sqrt(2*best_sig2*logm)
    floor=math.sqrt(n*logm)   # sqrt(n log m)
    print(f"{n:>4}{beta:>5.1f}{p:>10}{m:>8}  {M:>7.2f}{sig2_over_n:>8.3f}{best_lam:>7.3f}  {Mpred:>7.2f}{Mpred/M:>8.3f}{floor:>7.2f}{M/floor:>8.3f}{'  (sampled)' if sampled else ''}")
print()
print("sig2/n bounded (~const) across n => sub-Gaussian proxy is O(n) => union bound gives")
print("  M <= sqrt(2 sig2 log m) ~ sqrt(2 c n log m) = the FLOOR (handle real, reduced to this one bound).")
print("Mpred/M >= 1 with bounded ratio => the union-bound prediction is a valid (not loose, not violated) ceiling.")
