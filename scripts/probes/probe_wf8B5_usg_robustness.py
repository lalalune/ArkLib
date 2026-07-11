# Decisive test: does ULTRA-SUB-GAUSSIANITY (m_r log-concave, ALL r) hold for the period RV
# across MANY n and primes, INCLUDING deep r ~ ln q, and is there ANY violation?
# If it holds universally and we can cite type-L => done. If it FAILS at some (n,p) => obstruction
# to the type-L route (period RV is NOT type L) and W3-anti is not reducible to USG.
import math
from math import pi, cos, log
def isp(n):
    if n<2:return False
    d=2
    while d*d<=n:
        if n%d==0:return False
        d+=1
    return True
def fp(n,lo):
    p=lo+((1+n-lo%n)%n)
    if p<=2:p+=n
    while True:
        if p>2 and p%n==1 and isp(p):return p
        p+=n
def proot(p):
    m=p-1;fs=[];d=2
    while d*d<=m:
        if m%d==0:
            fs.append(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fs.append(m)
    g=2
    while True:
        if all(pow(g,(p-1)//f,p)!=1 for f in fs):return g
        g+=1
def etas(n,p):
    g=proot(p);h=pow(g,(p-1)//n,p)
    mu=[pow(h,j,p) for j in range(n)]
    m=(p-1)//n;gn=pow(g,n,p)
    eta=[];b=1
    for _ in range(m):
        re=sum(cos(2*pi*((b*x)%p)/p) for x in mu)
        eta.append(re);b=(b*gn)%p
    return eta,m
def df(r):
    p=1
    for k in range(1,r+1):p*=(2*k-1)
    return p
print("Testing USG (m_r log-concave) across n and multiple primes per n:")
any_fail=False
for n in [8,16,32,64]:
    los=[1000*n, 50000*n, 200000*n]
    for lo in los:
        p=fp(n,lo);eta,m=etas(n,p)
        Ms=[sum(e**(2*r) for e in eta)/m for r in range(0,12)]
        ms=[Ms[r]/(df(r)*n**r) for r in range(0,12)]
        # USG: ms log-concave: ms[r]^2 >= ms[r-1] ms[r+1]
        worst=1e9; failr=-1
        for r in range(1,10):
            d=ms[r]*ms[r]-ms[r-1]*ms[r+1]  # want >=0
            rel=d/(ms[r-1]*ms[r+1])
            if rel<worst: worst=rel; 
            if rel< -1e-9: failr=r; any_fail=True
        # also m1<=1 (USG base)
        print(f"  n={n:3} p={p:>11} lnq={log(p):4.1f} | m1={ms[1]:.4f} | USG worstRelMargin(>=0)={worst:+.3e} {'FAIL@'+str(failr) if failr>0 else 'OK'}")
print("ANY USG FAILURE:", any_fail)
