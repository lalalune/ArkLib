#!/usr/bin/env python3
"""Confirm q-dependence of interior delta* using DETERMINISTIC structured centers
only (power words x^j|_D, j=deg+1..2n), no random sampling. Report a=5 incidence
(the critical level just above the supercode's trivial distance) per prime.
"""
from itertools import combinations

def primitive_root(p):
    fac=[]; m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g

def subgroup(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    D=[]; x=1
    for _ in range(n): D.append(x); x=x*h%p
    return D

def main():
    n=16; deg=3; B=16; a=5
    print(f"n={n} supercode deg<={deg} B={B}  critical agreement a={a}",flush=True)
    primes=[97,113,193,241,257,337,353,401,433,449,577,641,673,769]
    for p in primes:
        D=subgroup(p,n)
        inv=[pow(x,p-2,p) if x else 0 for x in range(p)]
        subs=list(combinations(range(n),deg+1))
        W=[]
        for sub in subs:
            row=[]
            for i in range(n):
                wi={}
                for s in sub:
                    num=1; den=1; xi=D[i]; xs=D[s]
                    for t in sub:
                        if t==s: continue
                        num=num*((xi-D[t])%p)%p
                        den=den*((xs-D[t])%p)%p
                    wi[s]=num*inv[den]%p
                row.append(wi)
            W.append(row)
        best=0; arg=None
        for j in range(deg+1, 2*n+1):
            u=tuple(pow(x,j,p) for x in D)
            polys=set()
            for si,sub in enumerate(subs):
                Wi=W[si]
                w=tuple(sum(u[s]*Wi[i][s] for s in sub)%p for i in range(n))
                if sum(1 for i in range(n) if w[i]==u[i])>=a: polys.add(w)
            if len(polys)>best: best=len(polys); arg=j
        cross = "delta*<0.6875 (I>B)" if best>B else "delta*=0.6875 (I<=B)"
        print(f"  p={p:4d}: I(a=5)={best:4d} via x^{arg:<3}  -> {cross}",flush=True)
main()
