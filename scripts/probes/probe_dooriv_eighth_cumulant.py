#!/usr/bin/env python3
"""
probe_dooriv_eighth_cumulant.py (#444, door-(iv) marginal moment ladder)
Single-prime 8th normalized connected cumulant g4 of the period field. NOISY at the 8th moment
(dominated by the few largest |eta_b| in the sample). Apparent single-prime 'growth' is a sampling
artifact -- see probe_dooriv_eighth_cumulant_multiprime.py for the decisive multi-prime check that
shows g4 is finite-size NOISE (sd dominates mean, sign flips prime-to-prime). DO NOT over-read a
single-prime 8th-order number. No axiom-clean 8th-order vanishing claimed (data too noisy).
"""
import numpy as np
def isprime(m):
    if m<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if m%q==0: return m==q
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1): continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: break
        else: return False
    return True
def prr(p):
    phi=p-1;fac=set();t=phi;d=2
    while d*d<=t:
        while t%d==0: fac.add(d);t//=d
        d+=1
    if t>1: fac.add(t)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in fac): return g
def fp(n,beta=4.0):
    lo=max(round(n**beta),n**3+1);p=lo-(lo%n)+1
    if p<=lo:p+=n
    while not isprime(p):p+=n
    return p
# 8th connected cumulant g4 = (m8 -28 m6 m2 -35 m4^2 +420 m4 m2^2 -630 m2^4)/m2^4  (centered, odd kappa=0)
def cums(x):
    x=np.asarray(x,float);xc=x-x.mean()
    m2=(xc**2).mean();m4=(xc**4).mean();m6=(xc**6).mean();m8=(xc**8).mean()
    k8=m8-28*m6*m2-35*m4**2+420*m4*m2**2-630*m2**4
    return k8/m2**4
print("n  p  g4(8th cumulant)")
for n in (16,32,64,128):
    p=fp(n);g=prr(p);m=(p-1)//n
    H=np.array([pow(g,(m*j)%(p-1),p) for j in range(n)],dtype=object)
    tp=2*np.pi/p
    mr=120000
    if m<=mr: ts=range(m)
    else: ts=np.random.default_rng(5).choice(m,mr,replace=False)
    et=np.empty(len(list(ts) if hasattr(ts,'__len__') else range(m)))
    ts=list(ts) if not hasattr(ts,'__len__') else ts
    et=np.empty(len(ts))
    for i,t in enumerate(ts):
        b=pow(g,int(t),p)
        res=((int(b)*H)%p).astype(np.float64)
        et[i]=np.cos(tp*res).sum()
    print(f"{n} {p} {cums(et):+.4f}")
