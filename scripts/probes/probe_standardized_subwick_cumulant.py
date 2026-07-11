#!/usr/bin/env python3
import math
import numpy as np
def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
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
        if isprime(t) and t!=n+1: return n,t
        t+=n
def df(k):
    p=1
    for j in range(1,2*k,2): p*=j
    return p
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
    return [pow(h,i,p) for i in range(n)]
print("Standardized NONZERO-period cumulants, proper regime (FFT). var = |eta_b|^2 over b!=0.")
print(f"{'n':>4} {'p':>9} {'beta':>4} {'m':>7} | {'mean':>7} {'k4/n2':>9} {'k4+3n2':>8} | R2   R3   R4   R5  (<1=subWick)")
for mu,beta in [(4,3.2),(4,4.1),(5,3.2),(5,4.1),(6,3.3),(6,4.0),(7,3.2)]:
    n,p=find_prime(mu,beta)
    S=subgroup(p,n)
    if len(set(S))!=n: continue
    m=(p-1)//n
    # indicator of subgroup, FFT to get eta_b = sum_x e_p(b x) = conj? eta_b = DFT of indicator at -b
    ind=np.zeros(p)
    for x in S: ind[x]=1.0
    eta=np.fft.fft(ind)          # eta[b]=sum_x ind[x] e^{-2pi i b x/p}; magnitude same
    mag2=np.abs(eta[1:p])**2     # b=1..p-1 (drop b=0 DC)
    mean=mag2.mean()
    c2=((mag2-mean)**2).mean()
    c3=((mag2-mean)**3).mean()
    c4=((mag2-mean)**4).mean()
    k4=c4-3*c2*c2
    Rr={r: (mag2**r).mean()/(df(r)*n**r) for r in range(2,6)}
    print(f"{n:>4} {p:>9} {beta:>4.1f} {m:>7} | {mean:>7.2f} {k4/(n*n):>9.3f} {k4/(n*n)+3:>8.4f} | "
          + " ".join(f"{Rr[r]:.3f}" for r in range(2,6)))
