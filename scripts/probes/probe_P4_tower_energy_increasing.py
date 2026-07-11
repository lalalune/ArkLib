# probe_P4_tower_energy_increasing.py (#444)
# REFUTES the tower-induction proof route (P4): E_r/Wick_r is INCREASING in n (not decreasing).
# Exact (least prime p>n^4, n|p-1): E_r/Wick_r < 1 (bound HOLDS at every tested n,r) but at fixed r it
# rises with n toward 1 (r=2: .875/.938/.969 at n=8/16/32; r=6: .131/.374/.711). At fixed n it falls in r
# (RSC r^{-d/2}). These balance so E_r/Wick -> 1 (margin -> 0) exactly at the saddle r~ln p = the wall.
# So tower-induction (which needs monotone DECREASING in n) cannot work; the vanishing saddle margin is open.

import math
from collections import Counter
def is_prime(m):
    if m<2:return False
    for q in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if m%q==0:return m==q
    d=m-1;r=0
    while d%2==0:d//=2;r+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        x=pow(a,d,m)
        if x==1 or x==m-1:continue
        for _ in range(r-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True
def least_prime(n):
    k=n**3+1
    while True:
        p=k*n+1
        if p>n**4 and is_prime(p):return p
        k+=1
def proot(p):
    f=set();m=p-1;d=2
    while d*d<=m:
        while m%d==0:f.add(d);m//=d
        d+=1
    if m>1:f.add(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in f):return g
def Er(n,rmax):
    p=least_prime(n);g=proot(p);h=pow(g,(p-1)//n,p)
    mu=[pow(h,j,p) for j in range(n)]
    c=Counter({0:1});out=[]
    for r in range(1,rmax+1):
        nc=Counter()
        for s,ct in c.items():
            for x in mu: nc[(s+x)%p]+=ct
        c=nc
        out.append(sum(v*v for v in c.values()))
    return out
def wick(n,r):
    w=1
    for j in range(1,r+1): w*=(2*j-1)
    return w*n**r
print("E_r/Wick_r  (is it monotone DECREASING in n? P4 tower-induction needs that)")
print(f"{'r':>3}", *[f'n={n:<8}' for n in [8,16,32]])
E={n:Er(n,6) for n in [8,16,32]}
for r in range(1,7):
    row=[E[n][r-1]/wick(n,r) for n in [8,16,32]]
    print(f"{r:>3}", *[f'{x:.4f}    ' for x in row], "  <- increasing in n" if row[0]<row[1]<row[2] else "")
print()
print("=> E_r/Wick is < 1 (bound HOLDS) but INCREASING in n toward 1 (margin SHRINKS).")
print("   P4 tower-induction (needs monotone DECREASING) REFUTES; and the margin -> 0 as n->inf IS the wall.")
