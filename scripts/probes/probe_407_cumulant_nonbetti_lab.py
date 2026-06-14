#!/usr/bin/env python3
"""
#407 cumulant-deep-nonbetti LAB.

Object: m=(p-1)/n real Gauss periods eta_i = sum_{x in mu_n} e_p(b_i x), one per coset of mu_n.
Normalized X_i = eta_i / sqrt(n) (variance ~1). Cumulant kappa_r = (1/m sum X_i^{2r})/(2r-1)!!.
M = max_i |eta_i|; floor target M <= sqrt(2 n ln m) <=> kappa_r <=~1 to depth r*~ln m.

We probe NON-Betti structure of the period multiset to see which deep-cumulant route has a chance:

(A) cross-parity self-improving descent  : level set S_lambda additive structure in Z/m (g-dilate)
(B) hypercontractivity / log-Sobolev      : is the period sequence a low-degree function of an
                                            independent base? (Walsh/character expansion degree)
(C) tower martingale increments           : eta over mu_n vs mu_{n/2}; is eta_{2n} - "parent" a
                                            bounded martingale increment? track increment moments
(D) SOS / positive-definiteness           : is sum X^{2r} - (2r-1)!! m  expressible <=0 via the
                                            exact even-moment recursion (Newton/cumulant) ?

We also directly measure the TRUE cumulants c_r (not just the ratio): a sub-Gaussian / Gaussian
measure has c_r=0 for r>=2 (in the cumulant sense), kappa_r->1. We test how fast the cumulants
of the period measure decay vs depth and vs m, to see if a tail/MGF (Cramer) bound is reachable.
"""
import cmath, math
import numpy as np

def is_prime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def factorize(m):
    s=set();d=2
    while d*d<=m:
        while m%d==0:s.add(d);m//=d
        d+=1
    if m>1:s.add(m)
    return s

def order_n_gen(p,n):
    F=factorize(p-1)
    for h in range(2,p):
        if all(pow(h,(p-1)//q,p)!=1 for q in F): return pow(h,(p-1)//n,p)
    return None

def periods(p,n,g, want_reps=False):
    mu=[pow(g,i,p) for i in range(n)]
    m=(p-1)//n
    seen=set(); reps=[]
    b=1
    while len(reps)<m and b<p:
        if b not in seen:
            reps.append(b)
            for x in mu: seen.add(b*x%p)
        b+=1
    etas=[]
    for b in reps:
        s=0j
        for x in mu:
            s+=cmath.exp(2j*cmath.pi*(b*x%p)/p)
        etas.append(s.real)   # eta is real (since -1 in mu_n)
    if want_reps:
        return np.array(etas), reps, mu
    return np.array(etas)

def find_prime(n, beta, fft=None):
    lo=int(n**beta); p=lo+(1-lo)%n
    while p<int(n**(beta+0.6)):
        if is_prime(p):
            return p
        p+=n
    return None

def dfac2(r):
    x=1
    for i in range(1,r+1): x*=(2*i-1)
    return x

def cumulants_from_moments(mu_central):
    """mu_central[k] = E[X^k] (raw central since mean 0). Return cumulants c_1..c_K via recursion."""
    K=len(mu_central)-1
    c=[0.0]*(K+1)
    # moments m[n]; cumulants via m[n]=sum_{k=1}^n C(n-1,k-1) c[k] m[n-k]
    m=mu_central
    for nn in range(1,K+1):
        s=m[nn]
        for k in range(1,nn):
            s-= math.comb(nn-1,k-1)*c[k]*m[nn-k]
        c[nn]=s
    return c

print("="*100)
print("CUMULANT-DEEP-NONBETTI LAB")
print("="*100)

for n in (16,32,64):
    p=find_prime(n,4.0)
    g=order_n_gen(p,n)
    etas,reps,mu=periods(p,n,g,want_reps=True)
    m=len(etas)
    X=etas/math.sqrt(n)
    M=np.max(np.abs(etas))
    rstar=max(2,int(round(math.log(p))))
    print(f"\n--- n={n} p={p} m={m} (log2 m={math.log2(m):.1f}) r*={rstar} ---")
    # cumulant ratios
    print(" r:   kappa_r=mu_2r/(2r-1)!!     true even cumulant c_2r (normalized)")
    raw_central=[1.0,0.0]  # m0,m1
    for k in range(2, 2*rstar+1):
        raw_central.append(float(np.mean(X**k)))
    cums=cumulants_from_moments(raw_central)
    for r in range(1, rstar+1):
        mu2r=float(np.mean(X**(2*r)))
        kap=mu2r/dfac2(r)
        c2r=cums[2*r] if 2*r<len(cums) else float('nan')
        print(f" {r:2d}:   {kap:10.4f}                  {c2r:12.5f}")
    print(f"  M/sqrt(2n ln m) = {M/math.sqrt(2*n*math.log(m)):.4f}   M/sqrt(n) = {M/math.sqrt(n):.4f}")
    # variance & kurtosis check
    print(f"  var(X)={np.var(X):.4f}  kurt(X)=E X^4={np.mean(X**4):.4f} (Gaussian=3)")
