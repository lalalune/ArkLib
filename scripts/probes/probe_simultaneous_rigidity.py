#!/usr/bin/env python3
"""NOVEL-A simultaneous-rigidity: single relation e_1=0 is char-p FLOPPY (NOVEL-C) but the simultaneous
odd system e_1=e_3=...=e_{2r-1}=0 (r conditions) is char-p RIGID. Mechanism: bad config = sign vector
eps in {+-1}^{2k} <=> f(x)=sum eps_i x^i (deg<2k, +-1 coeffs); conditions f(zeta^j)=0, j=1,3,..,2r-1.
char-0: f(zeta)=0 => f=0 (deg<phi(4k)=2k). char-p single: p | f(zeta), bad primes up to (2k)^{2k}.
char-p simult: p | gcd(f(zeta),f(zeta^3),...) => bad primes ~ 2^{2k/r}; for r=k/2 that's ~16 < 4k <= p."""
import itertools
def isp(x):
    if x<2:return False
    d=2
    while d*d<=x:
        if x%d==0:return False
        d+=1
    return True
def proot(p,n):
    for c in range(2,p):
        h=pow(c,(p-1)//n,p)
        if pow(h,n,p)==1 and pow(h,n//2,p)!=1: return h
def scan(k, r, BOUND):
    n=4*k; reps=2*k; odd=[2*t+1 for t in range(r)]
    EPS=list(itertools.product([1,-1],repeat=reps))
    maxbad=0; nbad=0; scanned=0
    p=n+1
    while p<BOUND:
        if isp(p):
            z=proot(p,n); zp=[pow(z,t,p) for t in range(n)]
            cnt=0
            for eps in EPS:
                ok=True
                for j in odd:
                    if sum(eps[i]*zp[(i*j)%n] for i in range(reps))%p!=0: ok=False;break
                if ok: cnt+=1
            scanned+=1
            if cnt>0: maxbad=p; nbad+=1
        p+=n
    print(f" k={k} r={r} ({reps} signs, conds e_1..e_{2*r-1}=0): {scanned} primes<{BOUND}; max bad prime={maxbad}; #bad={nbad}",flush=True)
print("single (r=1, floppy) vs simultaneous (r=2 and r=k/2, rigid):")
scan(4,1,2000); scan(4,2,2000)
scan(6,1,8000); scan(6,2,8000); scan(6,3,8000)
scan(8,2,3000); scan(8,4,3000)
