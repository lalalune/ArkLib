#!/usr/bin/env python3
"""Lean geomean tower probe: smaller beta (~2) so m=(p-1)/n is small; full exact max."""
import numpy as np, math
def is_prime(x):
    if x<2:return False
    i=2
    while i*i<=x:
        if x%i==0:return False
        i+=1
    return True
def find_prime(n,lo):
    p=lo+((1-lo)%n)
    if p<3:p+=n
    while not is_prime(p):p+=n
    return p
def primroot(p):
    m=p-1;fs=[];d=2;mm=m
    while d*d<=mm:
        if mm%d==0:
            fs.append(d)
            while mm%d==0:mm//=d
        d+=1
    if mm>1:fs.append(mm)
    g=2
    while True:
        if all(pow(g,(p-1)//f,p)!=1 for f in fs):return g
        g+=1
def Mmax(p,sub,g):
    sub=np.array(sub,dtype=np.int64);n=len(sub)
    gn=pow(g,n,p);m=(p-1)//n;best=0.0;b=1
    bs=np.empty(m,dtype=np.int64)
    for i in range(m):
        bs[i]=b;b=(b*gn)%p
    # vectorize over cosets in chunks
    for b in bs:
        ang=2*math.pi*((b*sub)%p)/p
        v=abs(np.cos(ang).sum()+1j*np.sin(ang).sum())
        if v>best:best=v
    return best
for L in [8,9,10]:
    nL=2**L
    p=find_prime(nL, nL*nL+nL)  # beta~2, m~nL small
    g=primroot(p)
    prev=None;logsum=0;steps=0;ratios=[]
    for k in range(2,L+1):
        n=2**k
        zeta=pow(g,(p-1)//n,p)
        sub=[pow(zeta,i,p) for i in range(n)]
        M=Mmax(p,sub,g)
        if prev:
            logsum+=math.log(M/prev);steps+=1;ratios.append(M/prev)
        prev=M
    gm=math.exp(logsum/steps)
    Ms=prev/math.sqrt(nL)
    print(f"p={p} beta={math.log(p)/math.log(nL):.2f} n={nL}: geomean_ratio={gm:.4f} max={max(ratios):.4f} min={min(ratios):.4f} (sqrt2={math.sqrt(2):.4f}) M/sqrtn={Ms:.3f} ratios={[round(r,3) for r in ratios]}",flush=True)
