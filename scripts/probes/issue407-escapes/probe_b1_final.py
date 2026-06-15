#!/usr/bin/env python3
"""
B1 FINAL consolidated probe. Three analyses, incremental flushed output.
  A) Realizability lever: realizable max|S| vs count-level sparse budget G_circ (worst direction).
  B) Worst-direction identity: which (a,b,d) binds; low-exponent vs imprimitive.
  C) BGK index-scaling: does worst max-agreement grow with index m=(p-1)/n?
"""
import itertools, math, sys
import numpy as np
from sympy import isprime, factorint

def find_prime(n,want_min):
    p=max(want_min,n+1); r=p%n
    if r!=1: p+=(1-r)%n
    while True:
        if p%n==1 and isprime(p): return p
        p+=n

def primes_1modn(n,count,start):
    out=[];p=start;r=p%n
    if r!=1: p+=(1-r)%n
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
    xa=np.array(xs,dtype=object); fa=np.array(fv,dtype=object); best=k
    for T in itertools.combinations(range(n),k):
        Tl=list(T); vals=np.zeros(n,dtype=object)
        for t in Tl:
            xt=xs[t]; num=np.ones(n,dtype=object); den=1
            for s in Tl:
                if s==t: continue
                num=(num*((xa-xs[s])%p))%p; den=(den*((xt-xs[s])%p))%p
            vals=(vals+(fv[t]*num)%p*pow(den%p,p-2,p))%p
        ag=int(np.sum(vals%p==fa%p))
        if ag>best:
            best=ag
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

def kernel_vec(M,t,p):
    A=[[x%p for x in r] for r in M]; R=len(A)
    pivot_cols=[]; r=0
    for c in range(t):
        piv=None
        for rr in range(r,R):
            if A[rr][c]%p!=0: piv=rr;break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]
        inv=pow(A[r][c]%p,p-2,p); A[r]=[(x*inv)%p for x in A[r]]
        for rr in range(R):
            if rr!=r and A[rr][c]%p!=0:
                f=A[rr][c]%p; A[rr]=[(A[rr][cc]-f*A[r][cc])%p for cc in range(t)]
        pivot_cols.append(c); r+=1
        if r==R: break
    free=[c for c in range(t) if c not in pivot_cols]
    if not free: return None
    fc=free[0]; cvec=[0]*t; cvec[fc]=1
    for ri,pc in enumerate(pivot_cols): cvec[pc]=(-A[ri][fc])%p
    return cvec

def G_circ(a,b,xs,k,p):
    """max #roots in mu_n of ANY nonzero poly supported on {0..k-1,a,b} (count-level budget)."""
    E=sorted(set(list(range(k))+[a,b])); t=len(E)
    V=[[pow(x,e,p) for e in E] for x in xs]; n=len(xs); best=0
    for B in itertools.combinations(range(n),t-1):
        cvec=kernel_vec([V[i] for i in B],t,p)
        if cvec is None: continue
        cnt=sum(1 for x in range(n) if sum(V[x][j]*cvec[j] for j in range(t))%p==0)
        if cnt>best: best=cnt
        if best==n: break
    return best,t

def secA_realizability(out):
    print("="*100,file=out); print("(A) REALIZABILITY LEVER: realiz max|S| vs count-level G_circ at WORST direction",file=out); out.flush()
    for (n,k) in [(8,2),(8,4),(12,3),(16,4)]:
        if k>=n-1: continue
        p=find_prime(n,n*40+1); xs,w=mu_n(p,n); mm=(p-1)//n; rho=k/n
        print(f"\n### n={n} k={k} p={p} m={mm} rho={rho:.3f} sqrt(nk)={math.sqrt(n*k):.2f} ###",file=out); out.flush()
        rows=[]
        for a in range(k,n):
            for b in range(0,a):
                d=math.gcd(a-b,n)
                R,_=worst_over_gamma(a,b,xs,k,p)
                Gc,t=G_circ(a,b,xs,k,p)
                rows.append((a,b,d,R,Gc,t))
        rows.sort(key=lambda r:-r[3])
        print("  top by realizable maxS:",file=out)
        for r in rows[:6]:
            print(f"    a={r[0]} b={r[1]} d={r[2]} realiz={r[3]} Gcirc={r[4]} t={r[5]} gap(Gc-R)={r[4]-r[3]}",file=out)
        wR=max(rows,key=lambda r:r[3]); wG=max(rows,key=lambda r:r[4]); mg=max(rows,key=lambda r:r[4]-r[3])
        print(f"  >>> maxRealiz={wR[3]} @(a={wR[0]},b={wR[1]},d={wR[2]}); maxGcirc={wG[4]} @(a={wG[0]},b={wG[1]}); "
              f"GAP at worst-realiz dir={wR[4]-wR[3]}; max-gap-anywhere={mg[4]-mg[3]} @(a={mg[0]},b={mg[1]})",file=out)
        print(f"      vs sqrt(nk)={math.sqrt(n*k):.2f}  k+1={k+1}  s=n/d={n//wR[2]}",file=out); out.flush()

def secC_bgkscaling(out):
    print("\n"+"="*100,file=out); print("(C) BGK INDEX-SCALING: worst max-agreement vs index m=(p-1)/n per direction class",file=out); out.flush()
    for (n,k) in [(8,2),(12,3)]:
        rho=k/n; ps=primes_1modn(n,9,n*3+1)
        print(f"\n### n={n} k={k} rho={rho:.3f} sqrt(nk)={math.sqrt(n*k):.2f} ###",file=out)
        print(f"{'p':>9} {'m':>6} | LOW(k,0) LOW2(k,k-1) HIGH(n/2) WORSTall (worstdir)",file=out); out.flush()
        for p in ps:
            xs,w=mu_n(p,n); mm=(p-1)//n
            low,_=worst_over_gamma(k,0,xs,k,p,50)
            low2,_=worst_over_gamma(k,max(0,k-1),xs,k,p,50)
            ah=n//2 if n//2>k else k+1; bh=ah-1
            high,_=worst_over_gamma(ah,bh,xs,k,p,50)
            bestall=0;bd=None
            for a in range(k,n):
                for b in range(0,a):
                    s,_=worst_over_gamma(a,b,xs,k,p,30)
                    if s>bestall: bestall=s;bd=(a,b,math.gcd(a-b,n))
            print(f"{p:>9} {mm:>6} |   {low:>3}     {low2:>3}        {high:>3}      {bestall:>3}   {bd}",file=out); out.flush()

if __name__=="__main__":
    with open("/tmp/b1_final_out.txt","w") as out:
        secA_realizability(out)
        secC_bgkscaling(out)
        print("\nDONE",file=out); out.flush()
    print("done")
