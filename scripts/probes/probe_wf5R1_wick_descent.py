#!/usr/bin/env python3
# per-level energy ratio E_s(mu_n)/E_s(mu_{n/2}) vs Wick-required 2^s; and global W=E_s/Wick
from collections import defaultdict
import sympy
def dfact(k):
    r=1
    while k>0: r*=k; k-=2
    return r
def N0_exact(S,p,r):
    dist={0:1}
    for _ in range(r):
        nd=defaultdict(int)
        for s,c in dist.items():
            for x in S: nd[(s+x)%p]+=c
        dist=nd
    return dist.get(0,0)
def subgroup(p,n):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p)
    S=[];x=1
    for _ in range(n): S.append(x); x=(x*h)%p
    return sorted(set(S))
print("per-level ratio E_s(n)/E_s(n/2) vs Wick-scale 2^s; W_n=E_s(n)/Wick(n)")
print(f"{'n':>4}{'s':>3}{'E_s(n)/E_s(n/2)':>17}{'2^s':>7}{'W_n':>8}{'W_{n/2}':>9}")
for mu in [4,5]:
    n=2**mu
    p=sympy.nextprime(n**4)
    while (p-1)%n!=0: p=sympy.nextprime(p)
    G=subgroup(p,n); H=subgroup(p,n//2)
    for s in range(2,5):
        r=2*s
        eg=N0_exact(G,p,r); eh=N0_exact(H,p,r)
        ratio=eg/eh
        wn=eg/(dfact(2*s-1)*n**s); wh=eh/(dfact(2*s-1)*(n//2)**s)
        print(f"{n:>4}{s:>3}{ratio:>17.3f}{2**s:>7}{wn:>8.3f}{wh:>9.3f}")
    print()
