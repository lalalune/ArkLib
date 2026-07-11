import numpy as np
from math import log, sqrt
def isprime(n):
    if n<2: return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37,41,43]:
        if n%q==0: return n==q
    d=n-1;r=0
    while d%2==0: d//=2;r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,n)
        if x==1 or x==n-1: continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if h==1 or pow(h,n//2,p)==1: continue
        S=set();x=1
        for _ in range(n):x=(x*h)%p;S.add(x)
        if len(S)==n:return sorted(S)
    return None
def E2_exact(p,n):
    # E2 = #{a+b=c+d in mu_n} = sum_t r(t)^2 where r(t)=#{(a,b):a+b=t}
    S=subgroup(p,n)
    if S is None: return None,None
    Sset=set(S)
    from collections import Counter
    r=Counter()
    for a in S:
        for b in S:
            r[(a+b)%p]+=1
    E2=sum(v*v for v in r.values())
    # excess over Wick/Sidon value 3n^2-3n (char-0 antipodal energy for n even)
    wick=3*n*n-3*n
    return E2, E2-wick
print("E2(mu_n) exact, excess over Wick 3n^2-3n (char-0 Sidon value); n even")
print(f"{'n':>4} {'p':>7} {'idx':>5} {'E2':>10} {'3n^2-3n':>9} {'excess':>8} {'exc/n':>7} {'type'}")
cases=[(8,41),(8,137),(8,8209),(16,257),(16,4129),(16,65537),(32,577),(32,32801),
       (64,4289),(64,65537),(64,262337),(128,33409),(128,131713)]
for n,p in cases:
    if (p-1)%n: continue
    E2,exc=E2_exact(p,n)
    if E2 is None: continue
    op=p-1
    while op%2==0: op//=2
    typ="FERMAT/2pow" if op==1 else ("mild" if op<n else "generic")
    print(f"{n:4d} {p:7d} {(p-1)//n:5d} {E2:10d} {3*n*n-3*n:9d} {exc:8d} {exc/n:7.2f} {typ}")
