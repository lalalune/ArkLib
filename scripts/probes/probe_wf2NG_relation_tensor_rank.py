#!/usr/bin/env python3
"""
wf-NG (#407): Polynomial method BEYOND diagonal slice-rank. Part 1.

Confirm N0(mu_n, r) = #{(x_1..x_r) in mu_n^r : sum x_i = 0} agrees char-0 vs char-p in the
clean regime and tracks Wick scale, NOT trivial n^{r-1}. This is the exact §407 open object.
"""
import itertools, numpy as np

def is_prime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    i = 3
    while i*i <= m:
        if m % i == 0: return False
        i += 2
    return True

def smallest_clean_prime(n, beta=5):
    target = n**beta
    p = target - (target % n) + 1
    if p <= n: p += n
    while not (p > n and is_prime(p) and (p-1) % n == 0):
        p += n
    return p

def factorize(m):
    f=set(); d=2
    while d*d<=m:
        while m%d==0: f.add(d); m//=d
        d+=1
    if m>1: f.add(m)
    return f

def primitive_root(p):
    if p==2: return 1
    fac=factorize(p-1)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac): return g
    raise RuntimeError

def mu_n(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    S=[]; x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    assert len(set(S))==n
    return S

def N0_exact_Fp(p,n,r):
    S=mu_n(p,n); dp=np.zeros(p,dtype=object); dp[0]=1
    for _ in range(r):
        ndp=np.zeros(p,dtype=object)
        for s in S: ndp+=np.roll(dp,s)
        dp=ndp
    return int(dp[0])

def N0_exact_C(n,r):
    d=n//2
    def rv(k):
        v=[0]*d; s=1; kk=k%n
        while kk>=d: kk-=d; s=-s
        v[kk]=s; return tuple(v)
    roots=[rv(k) for k in range(n)]
    from collections import defaultdict
    dp=defaultdict(int); dp[tuple([0]*d)]=1
    for _ in range(r):
        ndp=defaultdict(int)
        for vec,c in dp.items():
            for r0 in roots:
                ndp[tuple(a+b for a,b in zip(vec,r0))]+=c
        dp=ndp
    return dp[tuple([0]*d)]

def dblfact_odd(k):
    res=1
    while k>0: res*=k; k-=2
    return res

if __name__=="__main__":
    print("=== wf-NG part1: N0(mu_n,r) char-0 vs char-p vs Wick vs trivial ===")
    print(f"{'n':>4} {'r':>3} {'p':>10} {'N0_Fp':>10} {'N0_C':>10} {'match':>6} {'Wick':>8} {'trivial n^(r-1)':>16}")
    for n in [4,8,16]:
        for r in [2,3,4,5,6]:
            if n==16 and r>4: continue
            p=smallest_clean_prime(n)
            a=N0_exact_Fp(p,n,r); b=N0_exact_C(n,r)
            wick = dblfact_odd(r-1)*n**(r//2) if r%2==0 else "-"
            print(f"{n:>4} {r:>3} {p:>10} {a:>10} {b:>10} {str(a==b):>6} {str(wick):>8} {n**(r-1):>16}")
