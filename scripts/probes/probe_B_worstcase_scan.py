# Serious refutation scan: worst B/sqrt(2n log p) over MANY primes, larger n.
# Uses eta_b constant on cosets of mu_n  => B = max over m=(p-1)/n cosets, O(p) per prime.
import math, cmath
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def Bval(p,n):
    g0=primroot(p); m=(p-1)//n
    # powers pe[k]=exp(2pi i g0^k /p), k=0..p-2
    pe=[0.0]*(p-1); x=1
    for k in range(p-1):
        pe[k]=cmath.exp(2j*math.pi*x/p); x=x*g0%p
    best=0.0
    P1=p-1
    for i in range(m):
        s=0j; idx=i
        for j in range(n):
            s+=pe[idx]; idx+=m
            if idx>=P1: idx-=P1
        a=abs(s)
        if a>best: best=a
    return best
for n,PMAX in [(64,40000),(128,80000),(256,250000)]:
    worst=0.0; worstp=0; cnt=0
    p=n+1
    while p<PMAX:
        if isprime(p):
            B=Bval(p,n); r=B/math.sqrt(2*n*math.log(p)); cnt+=1
            if r>worst: worst=r; worstp=p
        p+=n
    print(f"n={n:<4} scanned {cnt} primes <{PMAX}:  worst B/sqrt(2n log p) = {worst:.4f} @ p={worstp}   (B={worst*math.sqrt(2*n*math.log(worstp)):.1f}, sqrt(n)={math.sqrt(n):.1f}, B/sqrt(n)={worst*math.sqrt(2*math.log(worstp)):.2f})",flush=True)
