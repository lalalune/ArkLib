#!/usr/bin/env python3
"""Does the EsymmFiber coset-union supply reach the census pin band a0=rm+1?
Exact scan. n=2^mu*m, k_c=(r-2)m+1, a0=rm+1; construction at band a needs
d|a, d|n, d>=a-k_c+1; supply = C(n/d, a/d). Verdict governed by m: m=1 (FFT) -> poly,
m>=2 -> exp. Reproduces PINBAND-SUPPLY-PROBE.md."""
from math import comb, log2
def divisors(x):
    ds=[]; i=1
    while i*i<=x:
        if x%i==0: ds+=[i,x//i]
        i+=1
    return sorted(set(ds))
def max_supply(mu,m,r):
    n=(2**mu)*m; kc=(r-2)*m+1; a0=r*m+1; best=0.0; arg=None
    for a in range(a0, n+1):
        fl=a-kc+1
        for d in divisors(a):
            if d<fl or n%d: continue
            nn,s=n//d,a//d
            if 1<=s<=nn:
                lg=sum(log2((nn-i)/(i+1)) for i in range(min(s,nn-s)))
                if lg>best: best,arg=lg,(a,d,s,nn)
    return n,kc,a0,best,arg
if __name__=="__main__":
    print("rho   mu  m   n        a0       log2(supply)  verdict  witness")
    for rho in [0.5,0.25,0.125,0.0625]:
        for mu in [10,12]:
            for m in [1,2,4]:
                n=(2**mu)*m; r=round((rho*n-1)/m+2)
                if r<2: continue
                N,kc,a0,best,arg=max_supply(mu,m,r)
                v="EXP" if best>128 else ("poly" if best<32 else "MID")
                print(f"{rho:<5} {mu:<3} {m:<3} {N:<8} {a0:<8} {best:>10.1f}    {v:<6} {arg}")
