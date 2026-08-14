#!/usr/bin/env python3
"""
probe_444_jacobi_hermite_turnover.py  (sol, door-(iv) Lane-2, 2026-06-21)

Verify Shaw's form (D) claim: the OP recurrence coefficients b_k of the empirical
eta-measure follow the HERMITE law  b_k^2 = n*k  up to a TURNOVER depth k*, after
which b_k/sqrt(n k) FALLS (sub-Hermite), with the spectral edge realized near k*
and M ~ sqrt(2 n k*). We measure:
  - the Hermite ratio  R_k = b_k^2 / (n*k)  vs k  (should start ~1, then fall)
  - the turnover depth k* (argmax of b_k, or where R_k drops below ~0.8)
  - M vs sqrt(2 n k*)
This tells us EXACTLY which relation is an empirical/modeled input (-> stated as a
hypothesis in the Lean reduction) vs unconditional. We do NOT formalize anything
not adversarially confirmed.
"""
import numpy as np, math, os

def is_prime(m):
    if m<2: return False
    if m%2==0: return m==2
    i=3
    while i*i<=m:
        if m%i==0: return False
        i+=2
    return True

def find_prime(n,beta):
    t=int(n**beta); p=t-(t%n)+1
    for _ in range(300000):
        if p>n**3 and is_prime(p): return p
        p+=n
    return None

def prime_factors(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def subgroup(n,p):
    for cand in range(2,p):
        h=pow(cand,(p-1)//n,p)
        if len(set(pow(h,j,p) for j in range(n)))==n:
            return [pow(h,j,p) for j in range(n)]
    return None

def eta_re(n,p):
    grp=np.array(subgroup(n,p),dtype=np.int64)
    b=np.arange(1,p,dtype=np.int64); w=2*math.pi/p
    re=np.zeros(p-1); im=np.zeros(p-1); CH=200000
    for i in range(0,len(b),CH):
        bb=b[i:i+CH][:,None]; ph=(bb*grp[None,:])%p; ang=w*ph
        re[i:i+CH]=np.cos(ang).sum(1); im[i:i+CH]=np.sin(ang).sum(1)
    return re, np.sqrt(re*re+im*im)

def jacobi(support,R):
    x=np.asarray(support,float); N=len(x); w=np.ones(N)/N
    R=min(R,N); a=np.zeros(R); beta=np.zeros(R)
    pkm1=np.zeros(N); pk=np.ones(N); nk=(w*pk*pk).sum()
    for k in range(R):
        a[k]=(w*x*pk*pk).sum()/nk
        pkp1=(x-a[k])*pk-(beta[k]*pkm1 if k>0 else 0)
        nkp1=(w*pkp1*pkp1).sum()
        if k+1<R: beta[k+1]=nkp1/nk
        pkm1,pk=pk,pkp1; nk=nkp1
        if nk<=0: R=k+1; a=a[:R]; beta=beta[:R]; break
    return a[:R], np.sqrt(np.maximum(beta[1:R],0.0))  # a, boff

def run(n,beta=4.0):
    p=find_prime(n,beta)
    re,ab=eta_re(n,p); M=ab.max()
    R=max(6,int(2*math.log(p))+3)
    a,bo=jacobi(re,R)
    k=np.arange(1,len(bo)+1)
    Rk=bo**2/(n*k)
    kstar=int(k[np.argmax(bo)])       # argmax depth
    # first k where Hermite ratio drops below 0.8
    drop=np.where(Rk<0.8)[0]
    kturn=int(k[drop[0]]) if len(drop) else None
    print(f"n={n:3d} p={p:>9d} logp={math.log(p):5.2f} M={M:7.3f}")
    print(f"   b_k = {np.array2string(bo[:min(len(bo),14)],precision=2,floatmode='fixed')}")
    print(f"   Hermite R_k=b_k^2/(nk) = {np.array2string(Rk[:min(len(Rk),14)],precision=2,floatmode='fixed')}")
    print(f"   argmax b_k at k*={kstar} (logp/2={math.log(p)/2:.1f}); Hermite-drop(<0.8) at k={kturn}")
    print(f"   sqrt(2 n k*)={math.sqrt(2*n*kstar):.3f}  vs M={M:.3f}  ratio M/sqrt(2nk*)={M/math.sqrt(2*n*kstar):.3f}")
    print(f"   support_cutoff n/4={n/4:.1f}  (k* << n/4 = early turnover? {kstar < n/4})")
    print()

if __name__=="__main__":
    ns=[int(x) for x in os.environ.get('NS','16,32,64').split(',')]
    print("=== form (D): Hermite-law-until-turnover of OP recurrence coeffs ===")
    for n in ns:
        try: run(n)
        except Exception as e: print(f"n={n} ERR {e}\n")
