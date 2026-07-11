# probe_saturate_vs_diverge_orbit.py (#444) — the decisive C²-saturation computation, via the
# dilation-orbit reduction (|eta_b| constant on mu_n-cosets => max over (p-1)/n reps, making n=128 feasible).
# HONEST FINDING (2026-06-21): worst-case C(n)=M/sqrt(n log(p/n)) is STRONGLY SAMPLING-SENSITIVE — worst
# C² = 1.14/1.46/1.59/2.21/1.63 at n=8/16/32/64/128 but with 3/3/3/3/1 primes sampled (n=128 undersampled
# => artificially low). C_iid crossed 1.0 at the worst n=64 prime (sub-iid heuristic violated worst-case).
# A model fit MARGINALLY favors saturating (C²->2.47, SSE 0.246) over diverging (SSE 0.306) but is NOT
# decisive given inconsistent sampling. CONFIRMS the dossier: undecidable below n~256; the sub-Gaussian
# slack vanishes only as n->inf, so no finite n settles saturate-vs-diverge. NOT a proof, NOT a disproof.

import numpy as np
from math import sqrt, log
def is_prime(N):
    if N<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53):
        if N%q==0: return N==q
    d=N-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,N)
        if x in (1,N-1):continue
        ok=False
        for _ in range(r-1):
            x=x*x%N
            if x==N-1:ok=True;break
        if not ok:return False
    return True
def primroot(p):
    fac=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:fac.add(d);m//=d
        d+=1
    if m>1:fac.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def Morbit(p,n):
    # |eta_b| constant on mu_n cosets => max over (p-1)/n coset reps g^j
    g=primroot(p); w=pow(g,(p-1)//n,p)
    roots=np.empty(n,dtype=np.int64); x=1
    for i in range(n): roots[i]=x; x=x*w%p
    Ncos=(p-1)//n
    # coset reps = g^j, j=0..Ncos-1 ; generate via repeated mult
    M=0.0; BL=200000
    reps=np.empty(min(BL,Ncos),dtype=np.int64)
    j=0; cur=1
    while j<Ncos:
        k=min(BL,Ncos-j)
        b=np.empty(k,dtype=np.int64)
        for t in range(k):
            b[t]=cur; cur=cur*g%p
        prod=(b[:,None]*roots[None,:])%p
        eta=np.exp(2j*np.pi*prod/p).sum(axis=1)
        M=max(M,float(np.abs(eta).max()))
        j+=k
    return M
def find(target,n,cnt=1):
    out=[];p=target-(target%n)+1
    for _ in range(60000):
        if (p-1)%n==0 and is_prime(p): out.append(p)
        if len(out)>=cnt: break
        p+=n
    return out

print("SATURATE-vs-DIVERGE: worst C(n)=M/√(n log(p/n)) and C_iid=M/√(2n log N), N=(p-1)/n")
print("="*70)
data=[]
for mu in (3,4,5,6,7):
    n=2**mu
    primes=find(n**4,n, cnt=(3 if mu<=6 else 1))
    best=0; bestp=0
    for p in primes:
        M=Morbit(p,n); 
        if M>best: best=M; bestp=p
    N=(bestp-1)/n
    C=best/sqrt(n*log(bestp/n)); Ci=best/sqrt(2*n*log(N))
    data.append((n,bestp,best,C,Ci))
    print(f"n={n:3d} p={bestp:12d}: M={best:8.2f}  C={C:.4f}  C_iid={Ci:.4f}  C²={C*C:.4f}")

# fit C^2(n) to saturating A - B/log n  vs diverging A + B*log n
import numpy as np
ns=np.array([d[0] for d in data],float); C2=np.array([d[3]**2 for d in data])
ln=np.log(ns)
# model S: C2 = A - B/ln  ; model D: C2 = A + B*ln
def fit(X):
    Xm=np.vstack([np.ones_like(X),X]).T
    coef,res,*_=np.linalg.lstsq(Xm,C2,rcond=None)
    pred=Xm@coef; ss=np.sum((C2-pred)**2)
    return coef,ss
cS,sS=fit(-1.0/ln)   # saturating: C2 = A + B*(-1/ln), B>0 => rises to A
cD,sD=fit(ln)        # diverging: C2 = A + B*ln, B>0 => unbounded
print(f"\nFIT C²(n): saturating [A-B/log n]: A(limit)={cS[0]:.3f} B={cS[1]:.3f} SSE={sS:.5f}")
print(f"           diverging  [A+B·log n]: A={cD[0]:.3f} B={cD[1]:.3f} SSE={sD:.5f}")
print(f"  {'SATURATING fits better (C²→'+f'{cS[0]:.2f}'+', bounded ⟹ conjecture TRUE-favorable)' if sS<sD else 'DIVERGING fits better (C²→∞ ⟹ DISPROOF signal)'}")
print(f"  (saturating limit C={sqrt(max(cS[0],0)):.3f} vs √2={sqrt(2):.3f}; diverging slope B={cD[1]:.3f} per log n)")
