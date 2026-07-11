#!/usr/bin/env python3
"""ADVERSARIAL VERIFY of the I031 Step(b) 'handle' claim (sig_eff^2/n bounded => exponent 1/2).

The result claims isHandle=true: the deterministic->Gaussian transfer constant sig_eff^2/n is
BOUNDED. But it ALSO honestly flags a knife-edge: a slow loglog-n creep (= BGK n^{o(1)} wall) fits
~3x better than a pure constant over n=8..128. The danger the verifier must stress: the 'bounded
constant' is a small-n artifact and the proxy is genuinely creeping (back to BGK).

THREE INDEPENDENT TESTS the prior probes did NOT run:

(A) DISCRETE SLOPE between consecutive octaves: delta_k = y(2^{k+1}) - y(2^k).
    Pure constant => delta_k ~ 0 (noise). loglog creep => delta_k > 0 but DECREASING
    (since d/dk loglog(2^k) = 1/(k ln2 . ln k)... shrinks). log-n creep => delta_k ~ const > 0.
    n^eps power => delta_k GROWING. This is model-free: just look at whether the increments
    persist, shrink, or grow at the LARGEST n we can reach.

(B) MANY-PRIME DENOISE at each n (5 primes, varied beta) with the FULL m (no sampling up to a cap),
    extended one octave past the prior n=128 to n=256, to halve the regression's finite-range bias.

(C) THE PRIZE EXTRAPOLATION SANITY: fit loglog & log models on n<=64 ONLY, predict n=128,256, and
    check the held-out residual. If the loglog model that 'fits best' in-sample also predicts the
    held-out points, the creep is real-and-slow (knife-edge honest). If a constant predicts the
    held-out points just as well, the creep is an in-sample overfit (=> handle stronger than claimed).

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

def find_primes(mu,betas):
    """Return several distinct primes for n=2^mu at the given beta targets, all p>>n^3."""
    n=1<<mu; out=[]
    for beta in betas:
        lo=int(n**beta); t=((lo//n)+1)*n+1
        cnt=0
        while cnt<1:
            if isprime(t):
                out.append(t); cnt+=1
            t+=n
    return n,out

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
    assert len(set(H))==n and pow(h,n//2,p)!=1, "bad subgroup (n=p-1 trap?)"
    return g,H

def proxy(p,n,g,H,cap=120000):
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
    return m,M, M*M/(2*logm)/n, samp

print("ADVERSARIAL: sig_eff^2/n with 5 primes/n, n=8..256, FULL m where feasible.")
print(f"{'n':>5}{'<sig2/n>':>10}{'std':>8}{'#p':>4}  per-prime")
betas=[3.2,3.6,4.0,4.4,4.8]
ns=[]; ys=[]
for mu in [3,4,5,6,7,8]:
    n,primes=find_primes(mu,betas)
    vals=[]
    for p in primes:
        try:
            g,H=subgroup(p,n)
            m,M,pr,samp=proxy(p,n,g,H)
            vals.append(pr)
        except AssertionError:
            pass
    if vals:
        avg=sum(vals)/len(vals); sd=float(np.std(vals))
        ns.append(1<<mu); ys.append(avg)
        print(f"{1<<mu:>5}{avg:>10.4f}{sd:>8.4f}{len(vals):>4}  "+" ".join(f"{v:.3f}" for v in vals))

ns=np.array(ns,float); ys=np.array(ys,float)

print()
print("=== (A) DISCRETE OCTAVE SLOPES delta_k = y(2^{k+1})-y(2^k) ===")
print("  const=>~0(noise) | loglog=>+ & SHRINKING | log=>+ & flat | power=>GROWING")
for i in range(len(ns)-1):
    print(f"  n {int(ns[i]):>4}->{int(ns[i+1]):>4}:  delta = {ys[i+1]-ys[i]:+.4f}")

print()
print("=== (B) FULL-RANGE FITS ===")
def fit(cols, y, X_ns):
    X=np.column_stack([np.ones(len(X_ns))]+cols)
    coef,_,*_=np.linalg.lstsq(X,y,rcond=None)
    pred=X@coef; ss=float(np.sum((y-pred)**2))
    return coef,ss
c0,s0=fit([],ys,ns)
c1,s1=fit([np.log(np.log(ns))],ys,ns)
c2,s2=fit([np.log(ns)],ys,ns)
print(f"  (a) const:       c={c0[0]:.4f}                SSE={s0:.5f}")
print(f"  (b) a+b loglogn: a={c1[0]:.4f} b={c1[1]:+.4f}   SSE={s1:.5f}")
print(f"  (c) a+b logn:    a={c2[0]:.4f} b={c2[1]:+.5f}  SSE={s2:.5f}")

print()
print("=== (C) HELD-OUT: fit on n<=64, predict n=128,256 ===")
tr = ns<=64
trn, trY = ns[tr], ys[tr]
def fit_pred(cols_train, cols_all):
    Xtr=np.column_stack([np.ones(trn.shape[0])]+cols_train)
    coef,_,*_=np.linalg.lstsq(Xtr,trY,rcond=None)
    Xall=np.column_stack([np.ones(len(ns))]+cols_all)
    return Xall@coef, coef
pc, _=fit_pred([], [])
pl, _=fit_pred([np.log(np.log(trn))],[np.log(np.log(ns))])
pg, _=fit_pred([np.log(trn)],[np.log(ns)])
print(f"  {'n':>5}{'actual':>9}{'const':>9}{'loglog':>9}{'logn':>9}")
for i in range(len(ns)):
    tag=" (held)" if ns[i]>64 else ""
    print(f"  {int(ns[i]):>5}{ys[i]:>9.4f}{pc[i]:>9.4f}{pl[i]:>9.4f}{pg[i]:>9.4f}{tag}")
ho = ns>64
if ho.sum()>0:
    print(f"  held-out SSE:  const={float(np.sum((ys[ho]-pc[ho])**2)):.5f}"
          f"  loglog={float(np.sum((ys[ho]-pl[ho])**2)):.5f}"
          f"  logn={float(np.sum((ys[ho]-pg[ho])**2)):.5f}")

print()
print("VERDICT:")
print(" - (A) octave slopes shrinking-toward-0 AND (C) constant predicts held-out as well as loglog")
print("   => the 'creep' is in-sample overfit, the BOUNDED-CONSTANT (handle) reading is the honest one.")
print(" - (A) slopes persistent/flat AND (C) loglog/logn strictly beats const out-of-sample")
print("   => genuine slow creep = BGK n^{o(1)} wall; isHandle is OPTIMISTIC (knife-edge, not a handle).")
