#!/usr/bin/env python3
"""
A3 window-map: full incidence profile across ALL radii for SMOOTH mu_n vs RANDOM,
to map exactly where incidence = n (budget-binding) sits relative to halfJ / J,
and confirm thickness-invariance across the WHOLE (halfJ,J) window (rule-3).
n=4,k=2 and n=6,k=4 (n-k=2, exact-feasible). Single moderate prime each.
"""
from itertools import product, combinations
from math import sqrt
import random
import sympy
random.seed(7)

def smooth_domain(p,n):
    g=sympy.primitive_root(p); h=pow(g,(p-1)//n,p); return [pow(h,i,p) for i in range(n)]
def random_domain(p,n): return random.sample(range(1,p),n)
def rref(mat,p):
    m=[r[:] for r in mat]; rows=len(m); cols=len(m[0]) if m else 0; piv=[]; r=0
    for c in range(cols):
        pr=next((i for i in range(r,rows) if m[i][c]%p),None)
        if pr is None: continue
        m[r],m[pr]=m[pr],m[r]; inv=pow(m[r][c],p-2,p); m[r]=[(x*inv)%p for x in m[r]]
        for i in range(rows):
            if i!=r and m[i][c]%p:
                f=m[i][c]; m[i]=[(a-f*b)%p for a,b in zip(m[i],m[r])]
        piv.append(c); r+=1
        if r==rows: break
    return m[:r],piv
def nullspace(mat,p):
    red,piv=rref(mat,p); cols=len(mat[0]); free=[c for c in range(cols) if c not in piv]; basis=[]
    for f in free:
        v=[0]*cols; v[f]=1
        for r,c in enumerate(piv): v[c]=(-red[r][f])%p
        basis.append(v)
    return basis
def solve_particular(H,s,p):
    rows=[H[i]+[s[i]] for i in range(len(H))]; red,piv=rref(rows,p); n=len(H[0]); w=[0]*n
    for r,c in enumerate(piv):
        if c==n: raise ValueError
        w[c]=red[r][n]
    return w
def ext_from(word,S,xs,k,p):
    if len(S)<=k: return True
    base,rest=S[:k],S[k:]
    for j in rest:
        val=0
        for a in base:
            num,den=1,1
            for b in base:
                if b!=a: num=num*((xs[j]-xs[b])%p)%p; den=den*((xs[a]-xs[b])%p)%p
            val=(val+word[a]*num*pow(den,p-2,p))%p
        if val!=word[j]%p: return False
    return True
def profile(p,n,k,xs):
    G=[[pow(x,j,p) for x in xs] for j in range(k)]; H=nullspace(G,p)
    subsets=[S for size in range(k+1,n+1) for S in combinations(range(n),size)]
    synd=list(product(range(p),repeat=n-k)); ext={}
    for s in synd:
        w=solve_particular(H,list(s),p); mask=0
        for bit,S in enumerate(subsets):
            if ext_from(w,list(S),xs,k,p): mask|=1<<bit
        ext[s]=mask
    adm={}
    for m in range(k+1,n+1):
        am=0
        for bit,S in enumerate(subsets):
            if len(S)>=m: am|=1<<bit
        adm[m]=am
    dirs=set()
    for s1 in synd:
        if not any(s1): continue
        fnz=next(x for x in s1 if x); inv=pow(fnz,p-2,p)
        dirs.add(tuple((x*inv)%p for x in s1))
    best={m:0 for m in adm}
    for s0 in synd:
        e0=ext[s0]
        for s1 in dirs:
            nj=~(e0&ext[s1])
            for m,am in adm.items():
                cnt=sum(1 for gg in range(p) if ext[tuple((a+gg*b)%p for a,b in zip(s0,s1))]&nj&am)
                if cnt>best[m]: best[m]=cnt
    return best

for (n,k,p) in [(4,2,29),(6,4,19)]:
    rho=k/n; halfJ=(1-sqrt(rho))/2; J=1-sqrt(rho)
    bS=profile(p,n,k,smooth_domain(p,n)); bR=profile(p,n,k,random_domain(p,n))
    print(f"\nn={n} k={k} p={p} rho={rho:.3f} budget=n={n} halfJ={halfJ:.3f} J={J:.3f}")
    print(f"  m  delta  zone        smoothIncid randomIncid  vs-budget(n)")
    for m in sorted(bS,reverse=True):
        d=1-m/n
        z = "<halfJ" if d<halfJ-1e-9 else "(halfJ,J)" if d<J-1e-9 else "[J,cap)" if d<(1-rho)-1e-9 else ">=cap"
        vb = "==n" if bS[m]==n else ("<=n" if bS[m]<=n else ">n")
        thin = "==" if bS[m]==bR[m] else ("S<R" if bS[m]<bR[m] else "S>R")
        print(f"  {m}  {d:.3f}  {z:<10}  {bS[m]:>6}     {bR[m]:>6}      {vb} [{thin}]")
print("\nDONE")
