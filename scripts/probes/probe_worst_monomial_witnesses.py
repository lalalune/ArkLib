#!/usr/bin/env python3
"""Identify the EXACT 2 witness polynomials in the list at s=n/2 for w(x)=x^(n/2)."""
import itertools
from sympy import isprime, primitive_root

def find_prime(n, lower):
    p = lower - (lower % n) + 1
    if p <= lower: p += n
    while not isprime(p): p += n
    return p

def subgroup_mu(p, n):
    g = primitive_root(p); h = pow(g,(p-1)//n,p)
    e=[]; cur=1
    for _ in range(n): e.append(cur); cur=cur*h%p
    return e

def poly_eval(c,x,p):
    r=0
    for coef in reversed(c): r=(r*x+coef)%p
    return r

def lagrange(points,p):
    k=len(points); coeffs=[0]*k
    for i,(xi,yi) in enumerate(points):
        num=[1]; den=1
        for j,(xj,_) in enumerate(points):
            if j==i: continue
            new=[0]*(len(num)+1)
            for d,c in enumerate(num):
                new[d]=(new[d]-c*xj)%p; new[d+1]=(new[d+1]+c)%p
            num=new; den=den*(xi-xj)%p
        scale=yi*pow(den,p-2,p)%p
        for d in range(len(num)): coeffs[d]=(coeffs[d]+num[d]*scale)%p
    while len(coeffs)>1 and coeffs[-1]==0: coeffs.pop()
    return tuple(coeffs)

for (n,k) in [(8,2),(16,2),(16,4),(32,2)]:
    p=find_prime(n, n**3*50); mu=subgroup_mu(p,n); half=n//2
    w={x:pow(x,half,p) for x in mu}
    found={}
    for combo in itertools.combinations(mu,k):
        c=lagrange([(x,w[x]) for x in combo],p)
        d=len(c)-1
        while d>0 and c[d]==0: d-=1
        if d>=k: continue
        agree=sum(1 for x in mu if poly_eval(c,x,p)==w[x])
        if agree>=half: found[c]=agree
    # render constants: 1 and p-1 are the +1 / -1 constants
    desc=[]
    for c,a in found.items():
        if len(c)==1:
            v=c[0]
            label = "+1" if v==1 else ("-1" if v==p-1 else f"const={v}")
            desc.append(f"[{label}, agree={a}]")
        else:
            desc.append(f"[deg{len(c)-1} poly, agree={a}]")
    print(f"n={n:3d} k={k} p={p}: {len(found)} witnesses -> {desc}")
