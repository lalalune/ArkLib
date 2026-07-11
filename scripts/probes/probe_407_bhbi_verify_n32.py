#!/usr/bin/env python3
"""Adversarial verify the n=32 height-1 relation claim. Print the actual witness + check
omega is a genuine primitive 32nd root (omega^16 = -1, omega^32 = 1), half-basis N=16,
and that the relation is a TRUE subset relation Σ ±ω^j ≡ 0 mod p. Rule-6: a height-1 relation
is a strong claim; confirm it's not a degenerate/non-primitive omega or a code bug."""
import numpy as np, random, math
def prim(p,m):
    e=(p-1)//(1<<m); rr=random.Random(p)
    for _ in range(1000):
        b=rr.randrange(2,p); c=pow(b,e,p)
        if pow(c,(1<<m)//2,p)==p-1: return c
def lll_float(B, delta=0.99):
    B=B.astype(np.float64).copy(); n=B.shape[0]
    def gso(B):
        n=B.shape[0]; Bs=np.zeros_like(B); mu=np.zeros((n,n))
        for i in range(n):
            Bs[i]=B[i].copy()
            for j in range(i):
                d=np.dot(Bs[j],Bs[j]); mu[i][j]=np.dot(B[i],Bs[j])/d if d else 0.0; Bs[i]-=mu[i][j]*Bs[j]
        return Bs,mu
    Bs,mu=gso(B); k=1; it=0
    while k<n and it<100000:
        it+=1
        for j in range(k-1,-1,-1):
            if abs(mu[k][j])>0.5: B[k]-=round(mu[k][j])*B[j]; Bs,mu=gso(B)
        if np.dot(Bs[k],Bs[k])>=(delta-mu[k][k-1]**2)*np.dot(Bs[k-1],Bs[k-1]): k+=1
        else: B[[k,k-1]]=B[[k-1,k]]; Bs,mu=gso(B); k=max(k-1,1)
    return np.rint(B).astype(np.int64)

for p,m in [(1179649,5),(1048609,5)]:
    n=1<<m; N=1<<(m-1)
    w=prim(p,m)
    print(f"\n=== n={n} p={p} omega={w} ===")
    print(f"  omega^32 mod p = {pow(w,32,p)} (must=1); omega^16 = {pow(w,16,p)} (must={p-1}); omega^8={pow(w,8,p)}(must NOT be ±1)")
    a=[pow(w,j,p) for j in range(N)]
    # are the half-basis powers DISTINCT? (degenerate if collision)
    print(f"  half-basis distinct: {len(set(a))==N}  (N={N})")
    B=np.zeros((N+1,N+1),dtype=np.float64)
    for j in range(N): B[j,j]=1.0; B[j,N]=p*a[j]
    B[N,N]=p*p
    R=lll_float(B)
    found=[]
    for row in R:
        g=[int(x) for x in row[:N]]
        if any(g) and sum(c*x for c,x in zip(g,a))%p==0:
            found.append((max(abs(c) for c in g), tuple(g)))
    found.sort()
    if found:
        h,g=found[0]
        s_int=sum(c*x for c,x in zip(g,a))
        print(f"  shortest: height={h} g={g}")
        print(f"  EXACT integer Σ g_j ω^j = {s_int} = {s_int//p}·p (mod p = {s_int%p})")
        nz=sum(1 for c in g if c!=0)
        print(f"  support (nonzero coeffs) = {nz} of N={N}")
