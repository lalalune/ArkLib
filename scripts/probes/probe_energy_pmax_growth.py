# P_max(n): largest prime p ≡ 1 mod n dividing a quadruple cyclotomic norm
# N(zeta^i+zeta^j-zeta^k-zeta^l). Only p ≡ 1 mod n matter (else mu_n not in F_p).
# Above P_max(n), E_{F_p}(mu_n) = 3n(n-1) clean. Translation: fix i=0.
from itertools import product
from collections import Counter

def det_int(M):
    n=len(M); M=[r[:] for r in M]; sign=1; prev=1
    for k in range(n-1):
        if M[k][k]==0:
            piv=next((r for r in range(k+1,n) if M[r][k]),None)
            if piv is None: return 0
            M[k],M[piv]=M[piv],M[k]; sign=-sign
        for i in range(k+1,n):
            for j in range(k+1,n):
                M[i][j]=(M[i][j]*M[k][k]-M[i][k]*M[k][j])//prev
        prev=M[k][k]
    return sign*M[n-1][n-1]

def rp(e,h):
    s=1
    while e>=h: e-=h; s=-s
    return s,e

def norm(i,j,k,l,h):
    v=[0]*h
    for e,c in ((i,1),(j,1),(k,-1),(l,-1)):
        s,ee=rp(e%(2*h),h); v[ee]+=c*s
    M=[[0]*h for _ in range(h)]
    for col in range(h):
        for t in range(h):
            if v[t]:
                s,ee=rp(t+col,h); M[ee][col]+=s*v[t]
    return det_int(M)

def big_prime_factors_1modn(x,n):
    x=abs(x); out=set(); d=2
    while d*d<=x:
        while x%d==0:
            if d%n==1 and d>n: out.add(d)
            x//=d
        d+=1
    if x>1 and x%n==1 and x>n: out.add(x)
    return out

for n in (8,16,32):
    h=n//2
    bad=set(); mx=0
    for i in range(1):           # fix i=0 (translation invariance)
        for j,k,l in product(range(n),repeat=3):
            if {0,j}=={k,l}: continue
            N=norm(0,j,k,l,h)
            if N==0: continue
            mx=max(mx,abs(N))
            bad|=big_prime_factors_1modn(N,n)
    P=sorted(bad)
    print(f"n={n:>3}: bad primes (≡1 mod n, divide a norm) = {P}")
    print(f"       P_max={P[-1] if P else None}  | max|norm|={mx}=~4^{h}  "
          f"| P_max ≈ n^{(__import__('math').log(P[-1])/__import__('math').log(n)):.2f}" if P else "")
