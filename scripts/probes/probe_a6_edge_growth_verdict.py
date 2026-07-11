#!/usr/bin/env python3
"""
A6 VERDICT — does the normalized-period-measure support EDGE E_n = M/sqrt(n)
stay BOUNDED (=> constant crack) or grow like sqrt(log(p/n)) (=> Johnson)?

From probe_a6_even_moment_growth we learned:
 (i) nu_{n,p} (periods / sqrt(n)) converges in moments to a p-INDEPENDENT limit
     nu_n as p->inf at fixed n  (L^{2k} columns flat in p).  <- genuine new fact
 (ii) BUT the L^{2k} norms keep climbing with k (no saturation), and faster for
      larger n: the limiting measure is HEAVY-TAILED with an edge E_n that GROWS.

The SSS/moment-LP angle would crack the wall ONLY if E_n <= C absolute.
Here we measure E_n = max|eta|/sqrt(n) directly across n and check its growth
law against sqrt(log(p/n)) (Johnson) vs constant (crack).

Decisive regression: fit M ~ a * sqrt(n) * sqrt(log(p/n)) + b * sqrt(n).
If the sqrt(log) coefficient a is significantly > 0 and the data needs it,
A6 reduces to Johnson (the log is REAL, not absorbable by the integer trace).
"""
import math
import numpy as np
from sympy import isprime

def primitive_root(p):
    phi=p-1; fac=set(); x=phi; d=2
    while d*d<=x:
        while x%d==0: fac.add(d); x//=d
        d+=1
    if x>1: fac.add(x)
    for g in range(2,p):
        if all(pow(g,phi//q,p)!=1 for q in fac): return g

def Mval(p,n):
    m=(p-1)//n; g=primitive_root(p); N=p-1
    B=int(math.isqrt(N))+1
    low=[1]*B; cur=1
    for b in range(B): low[b]=cur; cur=cur*g%p
    gB=cur; A=(N+B-1)//B
    low=np.array(low,dtype=object)
    eta=np.zeros(m); twop=2.0*math.pi/p; cur=1
    for a in range(A):
        b0=a*B; bc=min(B,N-b0)
        if bc<=0: break
        res=((cur*low[:bc])%p).astype(np.float64)
        np.add.at(eta,np.arange(b0,b0+bc)%m,np.cos(twop*res))
        cur=cur*gB%p
    return float(np.max(np.abs(eta)))

def find_primes(n,count,pmin):
    res=[]; t=pmin//n+1
    while len(res)<count:
        p=1+n*t
        if isprime(p): res.append(p)
        t+=1
    return res

if __name__=="__main__":
    print("=== A6 VERDICT: edge growth E_n = M/sqrt(n) vs sqrt(log(p/n)) ===\n")
    rows=[]
    for mu in [2,3,4,5,6,7]:
        n=2**mu
        for c in [50, 2000, 30000]:
            pmin=min(c*n**3, 3*10**7)
            for p in find_primes(n,1,pmin):
                M=Mval(p,n)
                sn=math.sqrt(n); logr=math.log(p/n)
                En=M/sn
                rows.append((p,n,M,En,logr,math.sqrt(logr)))
                print(f"n={n:4d} p={p:>10} p/n^3={p/n**3:8.0f}  M={M:8.3f}  "
                      f"E_n=M/sqn={En:6.3f}  sqrt(log(p/n))={math.sqrt(logr):6.3f}  "
                      f"E_n/sqrt(log)={En/math.sqrt(logr):6.3f}")
    print()
    # regression: M = a*sqrt(n)*sqrt(log(p/n)) + b*sqrt(n)
    A=np.array([[math.sqrt(r[1])*r[5], math.sqrt(r[1])] for r in rows])
    y=np.array([r[2] for r in rows])
    coef,res,rk,sv=np.linalg.lstsq(A,y,rcond=None)
    pred=A@coef
    ss_res=np.sum((y-pred)**2); ss_tot=np.sum((y-np.mean(y))**2)
    print(f"FIT  M = a*sqrt(n*log(p/n)) + b*sqrt(n):  a={coef[0]:.4f}  b={coef[1]:.4f}  R^2={1-ss_res/ss_tot:.5f}")
    # constant-only model M = C*sqrt(n):
    Cfit=np.sum(y*np.sqrt([r[1] for r in rows]))/np.sum([r[1] for r in rows])
    pred2=Cfit*np.sqrt([r[1] for r in rows])
    r2c=1-np.sum((y-pred2)**2)/ss_tot
    print(f"FIT  M = C*sqrt(n) only:                  C={Cfit:.4f}            R^2={r2c:.5f}")
    print()
    print("VERDICT: if a>0 with high R^2 and the constant-only R^2 is poor, the")
    print("sqrt(log(p/n)) term is REAL -> E_n grows -> A6 reduces to JOHNSON (periods")
    print("too spread). The integer-trace structure does NOT cap the max at C*sqrt(n).")
