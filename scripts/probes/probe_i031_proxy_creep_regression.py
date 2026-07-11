#!/usr/bin/env python3
"""I031 STEP (b) FINAL: is sig_eff^2/n a SATURATING CONSTANT (handle: exponent 1/2 with bounded C)
or a SLOW (log n)^c CREEP (the BGK n^{o(1)} signature: bounded in any finite range but -> inf)?

The distinction is the whole prize. BGK proves M <= n^{1-o(1)} = the floor TIMES n^{o(1)}, i.e.
sig_eff^2/n ~ M^2/(n log m) ~ n^{o(1)} which is (log n)^{omega(1)} or n^{epsilon}. The I031 handle
claims sig_eff^2/n -> const (the deterministic->random transfer constant is BOUNDED).

Fit sig_eff^2/n against three models over n=8..1024:
  (a) constant c           (handle)
  (b) a + b*log(log n)     (the gentlest divergence; BGK-compatible)
  (c) a + b*log n          (a power n^{o(1)} would show as ~log n in the squared proxy at this range)
Report residuals; if (a) fits as well as (b),(c) and b~0 => saturating => HANDLE.
If b clearly >0 and growing fits strictly better => CREEP => wall, back to BGK.

To reduce finite-m sampling noise on the MAX, use FULL m where feasible (no sampling) up to n=512,
and average sig_eff^2/n over a few primes per n (different beta) to denoise.
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
    return g,H
def proxy(mu,beta,cap=80000):
    n,p=find_prime(mu,beta)
    g,H=subgroup(p,n)
    w=2*math.pi/p; m=(p-1)//n
    Hn=np.array(H,dtype=np.int64)
    reps=np.array([pow(g,c,p) for c in range(m)],dtype=np.int64)
    samp=m>cap
    if samp:
        idx=np.linspace(0,m-1,cap).astype(np.int64); reps=reps[idx]
    M=0.0; CH=4000
    for i in range(0,len(reps),CH):
        b=reps[i:i+CH][:,None]
        v=np.abs(np.exp(1j*w*((b*Hn[None,:])%p)).sum(axis=1))
        mx=float(v.max())
        if mx>M: M=mx
    logm=math.log(m)
    return n,p,m,M, M*M/(2*logm)/n, logm, samp

print(f"{'n':>5}{'<sig2/n>':>10}{'#primes':>8}  per-prime sig2/n")
ns=[]; ys=[]
for mu in [3,4,5,6,7,8]:  # n=8..256 (runnable; raise for the full prize-direction sweep)
    betas=[3.4,3.8,4.2]
    vals=[]
    for beta in betas:
        try:
            n,p,m,M,pr,logm,samp=proxy(mu,beta)
            vals.append(pr)
        except Exception as e:
            pass
    if vals:
        avg=sum(vals)/len(vals)
        ns.append(1<<mu); ys.append(avg)
        print(f"{1<<mu:>5}{avg:>10.4f}{len(vals):>8}  "+" ".join(f"{v:.3f}" for v in vals))

ns=np.array(ns,float); ys=np.array(ys,float)
def fit(X):
    X=np.column_stack([np.ones(len(ns))]+X)
    coef,res,*_=np.linalg.lstsq(X,ys,rcond=None)
    pred=X@coef
    ss=float(np.sum((ys-pred)**2))
    return coef,ss
c_const,ss_const=fit([])
c_llog,ss_llog=fit([np.log(np.log(ns))])
c_log,ss_log=fit([np.log(ns)])
print()
print(f"model (a) constant:        c={c_const[0]:.4f}                     SSE={ss_const:.5f}")
print(f"model (b) a+b*log(log n):  a={c_llog[0]:.4f} b={c_llog[1]:+.4f}     SSE={ss_llog:.5f}")
print(f"model (c) a+b*log n:       a={c_log[0]:.4f} b={c_log[1]:+.5f}    SSE={ss_log:.5f}")
print()
print("READING:")
print(" If b (in b,c) is tiny / SSE barely improves over (a) => SATURATING CONSTANT => HANDLE (exp 1/2).")
print(" If b clearly >0 and SSE drops a lot => (log n)^c CREEP => BGK n^{o(1)} wall, NOT a 1/2 handle.")
