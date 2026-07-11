#!/usr/bin/env python3
"""I031 STEP (b)-iv DECISIVE: the deep-tail / forced-anomaly test.

Metric is flat => M <= C E sup|G_b| reduces to: the per-period tail at the depth the union bound
over m indices probes (~ the q^{1/(2r)} moment level, r ~ log m) is sub-Gaussian with proxy O(n),
UNIFORMLY in n. The BGK/Lamzouri wall is EXACTLY that this deep-tail proxy inflates for thin n.

Two depth-faithful measurements (NOT the moderate-lambda MGF, which misses rare events):

(1) EFFECTIVE PROXY AT DEPTH:  the actual max M satisfies M = sqrt(2 sigma_eff^2 log m) by definition
    of sigma_eff = M^2/(2 log m). Sub-Gaussian-at-depth with proxy O(n) <=> sigma_eff^2 / n BOUNDED.
    This reads the proxy OFF THE ACTUAL MAX (the true deep tail), no MGF estimation error.

(2) DETERMINISTIC vs MATCHED-GAUSSIAN max, MANY trials, larger n: ratio M / E sup|G|. The matched
    Gaussian has proxy exactly n at every depth (Gaussian is its own tail), so M/EsupG > 1 and
    GROWING = deterministic deep tail heavier than Gaussian = anomaly = wall. BOUNDED = handle.

Also: vary beta (3.0..4.5) at fixed n to test the di-Benedetto/BGK m-dependence (thinner = harder?).
PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3, NEVER n=p-1.
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

def eta_all(p,n,g,H,cap=200000):
    w=2*math.pi/p; m=(p-1)//n
    Hn=np.array(H,dtype=np.int64)
    reps=np.array([pow(g,c,p) for c in range(m)],dtype=np.int64)
    sampled=m>cap
    if sampled:
        idx=np.linspace(0,m-1,cap).astype(np.int64); reps=reps[idx]
    eta=np.empty(len(reps),dtype=np.complex128); CH=2000
    for i in range(0,len(reps),CH):
        b=reps[i:i+CH][:,None]
        eta[i:i+CH]=np.exp(1j*w*((b*Hn[None,:])%p)).sum(axis=1)
    return eta,m,sampled,reps,Hn,w

print("=== (1) EFFECTIVE PROXY AT DEPTH: sigma_eff^2/n = M^2/(2 n log m). Bounded => handle. ===")
print(f"{'n':>4}{'beta':>5}{'p':>11}{'m':>8}  {'M':>7}{'sig_eff^2/n':>12}{'logm':>7}")
rows=[]
for mu,beta in [(3,4.0),(4,4.0),(5,4.0),(6,4.0),(7,3.6),(8,3.3),(9,3.1)]:
    n,p=find_prime(mu,beta)
    g,h,H=subgroup(p,n)
    eta,m,samp,reps,Hn,w=eta_all(p,n,g,H)
    M=float(np.abs(eta).max()); logm=math.log(m)
    seff2_over_n=M*M/(2*logm)/n
    rows.append((n,beta,p,m,M,seff2_over_n,logm,samp))
    print(f"{n:>4}{beta:>5.1f}{p:>11}{m:>8}  {M:>7.2f}{seff2_over_n:>12.4f}{logm:>7.3f}{'  (samp)' if samp else ''}")

print()
print("=== (2) DETERMINISTIC M vs MATCHED-GAUSSIAN E sup|G| (200 trials). Ratio bounded => handle. ===")
print(f"{'n':>4}{'beta':>5}{'p':>11}{'m':>8}  {'M':>7}{'EsupG':>8}{'M/EsupG':>9}{'maxG':>8}")
rng=np.random.default_rng(11)
for mu,beta in [(3,4.0),(4,4.0),(5,4.0),(6,4.0),(7,3.6)]:
    n,p=find_prime(mu,beta)
    g,h,H=subgroup(p,n)
    eta,m,samp,reps,Hn,w=eta_all(p,n,g,H,cap=15000)
    M=float(np.abs(eta).max())
    # matched Gaussian: G_b = sum_x g_x e_p(b x), g_x iid std complex normal. Phase matrix:
    Ph=np.exp(1j*w*((reps[:,None]*Hn[None,:])%p))   # (R,n)
    T=200; acc=0.0; mxG=0.0
    for _ in range(T):
        gg=(rng.standard_normal(n)+1j*rng.standard_normal(n))/math.sqrt(2)
        v=np.abs(Ph@gg); mx=float(v.max()); acc+=mx
        if mx>mxG: mxG=mx
    EsupG=acc/T
    print(f"{n:>4}{beta:>5.1f}{p:>11}{m:>8}  {M:>7.2f}{EsupG:>8.2f}{M/EsupG:>9.3f}{mxG:>8.2f}{'  (samp)' if samp else ''}")

print()
print("=== (3) beta-sweep at FIXED n=16 (thinner subgroup = larger m = BGK harder regime?) ===")
print(f"{'beta':>5}{'p':>11}{'m':>9}  {'M':>7}{'sig_eff^2/n':>12}{'M/floor':>9}")
n=16
for beta in [3.0,3.5,4.0,4.5,5.0]:
    nn,p=find_prime(4,beta)
    g,h,H=subgroup(p,n)
    eta,m,samp,reps,Hn,w=eta_all(p,n,g,H)
    M=float(np.abs(eta).max()); logm=math.log(m)
    seff2_over_n=M*M/(2*logm)/n
    floor=math.sqrt(n*logm)
    print(f"{beta:>5.1f}{p:>11}{m:>9}  {M:>7.2f}{seff2_over_n:>12.4f}{M/floor:>9.3f}{'  (samp)' if samp else ''}")
print()
print("VERDICT KEYS:")
print(" (1) sig_eff^2/n bounded across n=8..512 => deep-tail proxy O(n) => handle on EXPONENT 1/2.")
print(" (2) M/EsupG bounded => deterministic deep tail tracked by matched Gaussian => comparison valid.")
print(" (3) sig_eff^2/n bounded as beta grows (m grows) => no BGK thin-subgroup inflation in range.")
