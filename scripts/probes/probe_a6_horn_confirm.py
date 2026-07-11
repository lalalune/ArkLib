#!/usr/bin/env python3
"""
A6 HORN CONFIRMATION — at a FIXED ratio p/n^3 (so p>>n^3 honestly throughout),
push n and regress the saturated edge E_n = M/sqrt(n) against sqrt(log n).

If E_n ~ a*sqrt(log n) + b with a>0 and good fit, the periods are spread on the
Johnson scale: when n,p co-grow (prize regime), M ~ sqrt(n log) = JOHNSON, and the
Schur-Siegel-Smyth integer-trace structure gives NO sub-Johnson lever.

We must keep p>>n^3 (honesty) AND p large enough that E_n is near-saturated.
Use p/n^3 ~ a few hundred (saturation gap shown small there for n up to 32).
For larger n that forces big p (n=256 -> p~1e9). We push as far as feasible and
report the saturation caveat for the largest n.
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
    g=primitive_root(p); m=(p-1)//n; N=p-1
    B=int(math.isqrt(N))+1; low=[1]*B; cur=1
    for b in range(B): low[b]=cur; cur=cur*g%p
    gB=cur; A=(N+B-1)//B; low=np.array(low,dtype=object)
    eta=np.zeros(m); twop=2.0*math.pi/p; cur=1
    for a in range(A):
        b0=a*B; bc=min(B,N-b0)
        if bc<=0: break
        res=((cur*low[:bc])%p).astype(np.float64)
        np.add.at(eta,np.arange(b0,b0+bc)%m,np.cos(twop*res))
        cur=cur*gB%p
    return float(np.max(np.abs(eta)))

def find_prime(n,pmin):
    t=pmin//n+1
    while True:
        p=1+n*t
        if isprime(p): return p
        t+=1

if __name__=="__main__":
    print("=== A6 HORN CONFIRM: E_n vs sqrt(log n) at fixed p/n^3 ~ 300 ===\n")
    rows=[]
    ratio=300
    for mu in [2,3,4,5,6,7,8]:
        n=2**mu
        pmin=ratio*n**3
        if pmin>2*10**9:  # feasibility cap
            print(f"   n={n}: p~{pmin:.1e} too large to walk; skipping"); continue
        p=find_prime(n,pmin)
        M=Mval(p,n); En=M/math.sqrt(n)
        rows.append((n,En,p))
        print(f"   n={n:4d} p={p:>11} p/n^3={p/n**3:6.0f}  M={M:9.3f}  E_n={En:7.4f}"
              f"  sqrt(log n)={math.sqrt(math.log(n)):.4f}")
    print()
    n_arr=np.array([r[0] for r in rows],dtype=float)
    E_arr=np.array([r[1] for r in rows])
    # fit E = a*sqrt(log n)+b
    Xl=np.vstack([np.sqrt(np.log(n_arr)),np.ones_like(n_arr)]).T
    cl,_,_,_=np.linalg.lstsq(Xl,E_arr,rcond=None)
    predl=Xl@cl; r2l=1-np.sum((E_arr-predl)**2)/np.sum((E_arr-E_arr.mean())**2)
    # fit E = const
    cconst=E_arr.mean(); r2c=1-np.sum((E_arr-cconst)**2)/np.sum((E_arr-E_arr.mean())**2)
    # fit E = a*(log n)^{1/2} vs E = a*log n (to distinguish sqrt-log from log)
    Xll=np.vstack([np.log(n_arr),np.ones_like(n_arr)]).T
    cll,_,_,_=np.linalg.lstsq(Xll,E_arr,rcond=None)
    predll=Xll@cll; r2ll=1-np.sum((E_arr-predll)**2)/np.sum((E_arr-E_arr.mean())**2)
    print(f"FIT E_n = a*sqrt(log n)+b :  a={cl[0]:.4f} b={cl[1]:.4f}  R^2={r2l:.5f}")
    print(f"FIT E_n = a*(log n)+b     :  a={cll[0]:.4f} b={cll[1]:.4f}  R^2={r2ll:.5f}")
    print(f"FIT E_n = const           :  c={cconst:.4f}                R^2={r2c:.5f}")
    print()
    print("If sqrt(log n) fit dominates const fit (a>0, R^2 high), E_n grows on the")
    print("JOHNSON scale -> A6 reduces to Johnson. (large-n rows undersaturated => E_n")
    print("is an UNDER-estimate there, so true growth >= measured -> conclusion robust.)")
