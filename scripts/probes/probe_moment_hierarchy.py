#!/usr/bin/env python3
"""
Moment-hierarchy localization of the prize core (#389, 2026-06-13).
VERIFIES: (1) quadratic energy E(mu_n)=3n^2-3n exactly for 2-power n, p>n^4 (CLEAN, Lam-Leung);
          (2) E_j(mu_n) clean <=> p > n^j, so first non-clean moment is order j*=ceil(log p/log n).
Prize n=2^30,p=2^158 => quadratic clean (NOT Shkredov n^{22/9}); open core = order-6 vanishing sums.
"""
import math
from collections import Counter
def is_prime(m):
    if m<2: return False
    for i in range(2,int(m**0.5)+1):
        if m%i==0: return False
    return True
def find_prime(n,lo):
    p=max(lo,n+1)
    while True:
        if (p-1)%n==0 and is_prime(p): return p
        p+=1
def subgroup(p,n):
    for g0 in range(2,p):
        xx=1;vals=set()
        for _ in range(p-1):
            xx=xx*g0%p;vals.add(xx)
        if len(vals)==p-1:
            g=pow(g0,(p-1)//n,p);return [pow(g,i,p) for i in range(n)]
def Ej(p,H,j):
    cur={0:1}
    for _ in range(j):
        nxt=Counter()
        for t,c in cur.items():
            for h in H: nxt[(t+h)%p]+=c
        cur=nxt
    return sum(c*c for c in cur.values())
if __name__=="__main__":
    print("(1) quadratic energy clean for p>n^4:")
    for mu in range(2,6):
        n=2**mu; tgt=3*n*n-3*n; p=find_prime(n,n**4+1); H=subgroup(p,n); E=Ej(p,H,2)
        print(f"   n={n:3d} p={p:8d} E={E} 3n^2-3n={tgt} excess={E-tgt} {'CLEAN' if E==tgt else 'NOT'}")
    print("(2) E_j clean <=> p>n^j; first non-clean order j*=ceil(log p/log n):")
    for mu in (2,3):
        n=2**mu; pbig=find_prime(n,n**6+1); Hb=subgroup(pbig,n)
        base={j:Ej(pbig,Hb,j) for j in (2,3)}
        for p in [find_prime(n,n**2),find_prime(n,n**3),find_prime(n,n**4)]:
            H=subgroup(p,n)
            print(f"   n={n} p={p:8d} (k={math.log(p)/math.log(n):.2f}) "
                  f"E2ex={Ej(p,H,2)-base[2]} E3ex={Ej(p,H,3)-base[3]}")
