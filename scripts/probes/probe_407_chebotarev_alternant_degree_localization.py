#!/usr/bin/env python3
"""
For n=4: which (X-1)-Taylor coefficient of the minor polynomial is the LOWEST nonzero one?
The in-tree crux GeneralizedVandermondeNonzeroModP reads the lowest-order Taylor coeff.
For n=3 it is degree 3 (= Sum_sigma sign*C(s_sigma,3)).  My probe found the degree-n coeff
VANISHES for n>=4.  So we scan Taylor degree d = n, n+1, n+2, ... and find the first NONZERO,
then check if THAT coefficient factors as c*Vr*Vc (or Vr*Vc*symmetric).

minorExp e_{i,j} is a NAT.  The minor poly is  detPoly = det( X^{e_{i,j}} )  (entrywise X-powers).
Its (X-1)-Taylor coeff at degree d is  Sum_sigma sign(sigma) * C(s_sigma, d),  s_sigma=sum_i e_{i,sigma i}
(NAT).  We need the ACTUAL nat exponents e_{i,j}, not just mod p.  Use the in-tree minorExp:
e_{i,j} = (something) with e mod p = -(ci_j ri_i).  But C(s,d) as a NAT depends on the nat s.
To probe the FIELD value of the Taylor coeff we still only need s_sigma mod p IF we use
d! C(s,d) = descending factorial (poly in s) -> works mod p from s mod p.  Good.

So: T_d (mod p) = (1/d!) Sum_sigma sign(sigma) * prod_{t=0}^{d-1}(S_sigma - t),  S_sigma = sum_i -(ci_{sigma i} ri_i) mod p.
Find first d>=n with T_d != 0 (generically), then study its factorization.
"""
import itertools, random

def descfact(s,d,p):
    r=1
    for t in range(d): r=(r*((s-t)%p))%p
    return r
def Vand(v,p):
    n=len(v); r=1
    for i in range(n):
        for j in range(i+1,n): r=(r*((v[i]-v[j])%p))%p
    return r
def Td(ri,ci,n,d,p):
    total=0
    for sigma in itertools.permutations(range(n)):
        sign=1
        for a in range(n):
            for b in range(a+1,n):
                if sigma[a]>sigma[b]: sign=-sign
        S=0
        for i in range(n): S=(S-(ci[sigma[i]]*ri[i]))%p
        total=(total+sign*descfact(S,d,p))%p
    nf=1
    for t in range(1,d+1): nf*=t
    return (total*pow(nf%p,p-2,p))%p

def run(n,p,seed=0):
    random.seed(seed)
    ri=random.sample(range(p),n); ci=random.sample(range(p),n)
    Vr=Vand(ri,p); Vc=Vand(ci,p)
    while Vr==0 or Vc==0:
        ri=random.sample(range(p),n); ci=random.sample(range(p),n)
        Vr=Vand(ri,p); Vc=Vand(ci,p)
    row=[]
    for d in range(0, 3*n):
        row.append(Td(ri,ci,n,d,p))
    # lowest nonzero degree
    low=next((d for d,v in enumerate(row) if v!=0), None)
    return row, low, (ri,ci,Vr,Vc)

if __name__=="__main__":
    for n in (3,4,5):
        print(f"=== n={n} ===")
        lows=[]
        for p in (13,17,19,23,29):
            row,low,_=run(n,p,seed=p+n)
            lows.append(low)
            nz=[(d,v) for d,v in enumerate(row) if v!=0][:6]
            print(f"  p={p}: lowest-nonzero Taylor degree = {low};  first nonzero (deg,val): {nz}")
        print(f"  => lowest-nonzero degree across primes: {set(lows)}  (n(n-1)/2 = {n*(n-1)//2})")
