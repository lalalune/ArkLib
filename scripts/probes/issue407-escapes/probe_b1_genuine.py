#!/usr/bin/env python3
"""
B1 GENUINE-direction probe (correlated-trap excluded).

A direction (a,b) is CORRELATED/degenerate if on mu_n it folds via x^{n/2}=-1 so that the line
x^a+gamma x^b is delta-close to RS[k] for ALL gamma (the 'never validate on x^{n/2}=+-1' trap,
comment 100). Operationally: a direction is GENUINE if it is FAR (no full saturation) for at least
some gamma, AND its agreement set genuinely cliffs. We use the strict test:

  genuine(a,b)  iff   for the worst gamma, the max-agreement is STRICTLY less than n
                      AND not reducible: NOT( (a mod (n/2) < k) and (b mod (n/2) < k) ).

We then, among GENUINE directions only:
  - find worst realizable maxS  and its G_circ (count budget): is realizability slack?  (gap)
  - classify worst genuine dir as LOW-exponent (a,b < n/2, primitive) vs IMPRIMITIVE (d=gcd>=2)
  - report scaling vs sqrt(nk), k+1, s=n/d, deg b.
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

def worst_over_gamma(a,b,xs,k,p,sample=80):
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
    A=[[x%p for x in r] for r in M]; R=len(A); pivot_cols=[]; r=0
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
    E=sorted(set(list(range(k))+[a,b])); t=len(E)
    V=[[pow(x,e,p) for e in E] for x in xs]; n=len(xs); best=0
    for B in itertools.combinations(range(n),t-1):
        cvec=kernel_vec([V[i] for i in B],t,p)
        if cvec is None: continue
        cnt=sum(1 for x in range(n) if sum(V[x][j]*cvec[j] for j in range(t))%p==0)
        if cnt>best: best=cnt
        if best==n: break
    return best,t

def is_correlated(a,b,n,k):
    nh=n//2
    # reducible-to-low on each half-coset
    return (a%nh < k) and (b%nh < k)

def main():
    out=open("/tmp/b1_genuine_out.txt","w")
    def P(*x): print(*x,file=out); out.flush()
    P("="*100); P("B1 GENUINE-direction analysis (correlated trap excluded)");
    for (n,k) in [(8,2),(12,3),(16,4)]:
        if k>=n-1: continue
        p=find_prime(n,n*40+1); xs,w=mu_n(p,n); mm=(p-1)//n; rho=k/n
        P(f"\n### n={n} k={k} p={p} m={mm} rho={rho:.3f} sqrt(nk)={math.sqrt(n*k):.2f} k+1={k+1} ###")
        genuine=[]; correlated=[]
        for a in range(k,n):
            for b in range(0,a):
                d=math.gcd(a-b,n)
                R,g=worst_over_gamma(a,b,xs,k,p)
                rec=(a,b,d,R,g)
                if is_correlated(a,b,n,k) or R==n:
                    correlated.append(rec)
                else:
                    genuine.append(rec)
        genuine.sort(key=lambda r:-r[3])
        P(f"  #genuine={len(genuine)} #correlated/saturated={len(correlated)}")
        P("  top GENUINE directions by realizable maxS (with count budget Gcirc):")
        for rec in genuine[:8]:
            a,b,d,R,g=rec
            Gc,t=G_circ(a,b,xs,k,p)
            cls="LOW" if (a<n//2 and b<n//2) else f"IMPRIM(d={d})"
            P(f"    a={a} b={b} d={d} [{cls}] realizMaxS={R} Gcirc={Gc} gap={Gc-R}  vs sqrt(nk)={math.sqrt(n*k):.1f} k+1={k+1} s=n/d={n//d}")
        if genuine:
            wR=genuine[0]; a,b,d,R,g=wR
            Gc,t=G_circ(a,b,xs,k,p)
            P(f"  >>> WORST GENUINE: a={a} b={b} d={d} realizMaxS={R} Gcirc={Gc} GAP={Gc-R}")
    P("\nDONE"); out.close()
    print("done")

if __name__=="__main__":
    main()
