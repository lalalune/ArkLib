#!/usr/bin/env python3
"""geomean tower at beta~2.5-3 (between prize-ish and tractable), L up to 9, exact max."""
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
    for _ in range(m):
        ang=2*math.pi*((b*sub)%p)/p
        v=abs(np.cos(ang).sum()+1j*np.sin(ang).sum())
        if v>best:best=v
        b=(b*gn)%p
    return best
for (L,beta) in [(7,2.7),(8,2.6),(9,2.5)]:
    nL=2**L
    p=find_prime(nL, int(nL**beta))
    g=primroot(p)
    prev=None;logsum=0;steps=0;ratios=[]
    for k in range(2,L+1):
        n=2**k
        zeta=pow(g,(p-1)//n,p)
        sub=[pow(zeta,i,p) for i in range(n)]
        M=Mmax(p,sub,g)
        if prev: logsum+=math.log(M/prev);steps+=1;ratios.append(M/prev)
        prev=M
    gm=math.exp(logsum/steps)
    bb=math.log(p)/math.log(nL)
    print(f"p={p} beta={bb:.2f} n={nL}: geomean={gm:.4f} (sqrt2={math.sqrt(2):.4f}) M/sqrt(n log(p/n))={prev/math.sqrt(nL*math.log(p/nL)):.4f}",flush=True)
