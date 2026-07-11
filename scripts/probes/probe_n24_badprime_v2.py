"""
N24 test: do the bad primes p~n^4 concentrate at HIGH v2(p-1)/Fermat-like primes, leaving GENERIC
(minimal-v2) primes GOOD? W_r = E_r(F_p)-E_r(char0) via the period spectrum (feasible for deep r).
E_r(F_p) = (1/p) sum_b |eta_b|^{2r}; W_r=0 iff E_r(F_p)=E_r(char0). Classify primes near n^4 by v2(p-1).
"""
import math
from collections import Counter
def isprime(m):
    if m<2:return False
    for q in(2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in(2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in(1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def subgroup(p,n):
    e=(p-1)//n
    for c in range(2,p):
        h=pow(c,e,p)
        if pow(h,n,p)==1 and len({pow(h,i,p) for i in range(n)})==n:
            return [pow(h,i,p) for i in range(n)]
def v2(x):
    k=0
    while x%2==0: k+=1;x//=2
    return k
def Er_modp(p,n,r):
    """E_r(F_p) = #{(x1..xr,y1..yr): sum x=sum y} via convolution counts of r-fold sumset multiplicities."""
    S=subgroup(p,n)
    # r-fold sumset multiplicity: c_r[v] = #{(a1..ar) in S^r: sum=v}. E_r = sum_v c_r[v]^2.
    c=Counter({0:1})
    for _ in range(r):
        nc=Counter()
        for v,m in c.items():
            for x in S: nc[(v+x)%p]+=m
        c=nc
    return sum(m*m for m in c.values())

n=16
# char-0 E_r closed forms (in-tree): E_2=2n^2-n? use big-prime reference instead for safety
import sys
bigp=1
q=10**9
while True:
    q+=1
    if q%n==1 and isprime(q): bigp=q; break
E0={r:Er_modp(bigp,n,r) for r in (2,3,4)}
print(f"n={n}: char-0 (p={bigp}) E_2={E0[2]} E_3={E0[3]} E_4={E0[4]}")
print()
print(f"Scanning primes p=1 mod {n} near n^4={n**4}, W_r=E_r(F_p)-E_r(char0), classified by v2(p-1):")
print(f"{'p':>8} {'v2(p-1)':>7} {'W_2':>6} {'W_3':>6} {'W_4':>8} {'good(all 0)?':>12}")
cnt=0
for p in range(n**4-2000, n**4+8000):
    if p%n==1 and isprime(p):
        Ws={r:Er_modp(p,n,r)-E0[r] for r in (2,3,4)}
        good = all(w==0 for w in Ws.values())
        print(f"{p:>8} {v2(p-1):>7} {Ws[2]:>6} {Ws[3]:>6} {Ws[4]:>8} {str(good):>12}")
        cnt+=1
        if cnt>=18: break
