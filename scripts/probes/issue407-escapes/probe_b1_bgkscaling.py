#!/usr/bin/env python3
"""
B1 SETTLING EXPERIMENT (comment 100 vs 125): is the worst far-direction max-agreement
  (a) q-INDEPENDENT  (genuine off-BGK, demand-side count, prize-closeable)   or
  (b) GROWS with index m=(p-1)/n  (BGK in combinatorial clothing -> the wall)?

We fix n and k, fix a DIRECTION class, and sweep many primes p == 1 mod n with growing index m.
For each prime: worst-over-gamma max-agreement of x^a+gamma x^b vs RS[k] over mu_n.

Direction classes:
  - LOW   : a=k, b=0   (lowest far monomial x^k against a constant codeword; comment 125's binding family)
  - LOW2  : a=k, b=k-1 (low, d=1)
  - HIGH  : a near n/2  imprimitive (comment 100's e2-locus, must check correlation)
  - WORST : the empirical argmax over all (a,b) at this prime

BGK signature: maxS - (deg-or-floor) ~ c*sqrt(n*log m). Flat => q-independent.
"""
import itertools, math
import numpy as np
from sympy import isprime, factorint, nextprime

def primes_1modn(n, count, start=None):
    out=[]; p = start or (n+1)
    # ensure p == 1 mod n
    r=p%n
    if r!=1: p += (1-r)%n
    while len(out)<count:
        if p%n==1 and isprime(p): out.append(p)
        p+=n
    return out

def generator(p):
    fac=list(factorint(p-1).keys())
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): return c

def mu_n(p,n):
    g0=generator(p); w=pow(g0,(p-1)//n,p)
    return [pow(w,j,p) for j in range(n)], w

def max_agreement(fv,xs,k,p):
    n=len(xs)
    if k>=n: return n
    xa=np.array(xs,dtype=object); fa=np.array(fv,dtype=object)
    best=k
    for T in itertools.combinations(range(n),k):
        Tl=list(T); vals=np.zeros(n,dtype=object)
        for t in Tl:
            xt=xs[t]; num=np.ones(n,dtype=object); den=1
            for s in Tl:
                if s==t: continue
                num=(num*((xa-xs[s])%p))%p; den=(den*((xt-xs[s])%p))%p
            vals=(vals+(fv[t]*num)%p*pow(den%p,p-2,p))%p
        agree=int(np.sum(vals%p==fa%p))
        if agree>best:
            best=agree
            if best==n: return n
    return best

def worst_over_gamma(a,b,xs,k,p,sample=60):
    G=list(range(1,p))
    if len(G)>sample:
        step=max(1,(p-1)//sample); G=list(range(1,p,step))
    best=0;bg=None
    for g in G:
        fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(len(xs))]
        s=max_agreement(fv,xs,k,p)
        if s>best: best=s;bg=g
    return best,bg

def main():
    print("="*120)
    print("B1 BGK-scaling: worst max-agreement vs INDEX m=(p-1)/n for fixed direction classes")
    print("="*120)
    for (n,k) in [(8,2),(12,3),(16,4)]:
        rho=k/n; sqrtnk=math.sqrt(n*k)
        ps=primes_1modn(n, 8, start=n*3+1)  # growing index
        print(f"\n### n={n} k={k} rho={rho:.3f} sqrt(nk)={sqrtnk:.2f} ###")
        print(f"{'p':>9} {'m':>7} | {'LOW(a=k,b=0)':>13} {'LOW2(k,k-1)':>12} {'HIGH(~n/2)':>11} {'WORST-all':>10} (worst dir)")
        for p in ps:
            xs,w=mu_n(p,n); m=(p-1)//n
            low,_=worst_over_gamma(k,0,xs,k,p)
            low2,_=worst_over_gamma(k,max(0,k-1),xs,k,p)
            ah=n//2 if n//2>k else k+1; bh=ah-1
            high,_=worst_over_gamma(ah,bh,xs,k,p)
            # worst over all directions (a in [k,n), b<a)
            bestall=0; bd=None
            for a in range(k,n):
                for b in range(0,a):
                    s,g=worst_over_gamma(a,b,xs,k,p,sample=40)
                    if s>bestall: bestall=s; bd=(a,b,math.gcd(a-b,n))
            print(f"{p:>9} {m:>7} | {low:>13} {low2:>12} {high:>11} {bestall:>10}  {bd}")

if __name__=="__main__":
    main()
