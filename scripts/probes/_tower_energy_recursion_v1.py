#!/usr/bin/env python3
"""
TOWER ENERGY RECURSION probe (#444, 2026-06-19) — seed for the high-moment machinery.

eta_b(mu_{2N}) = eta_b(mu_N) + eta_{gb}(mu_N), g a primitive 2N-th root (coset rep of mu_N in mu_{2N}).
=> E_r(mu_{2N}) := (1/p) sum_b |eta_b(mu_{2N})|^{2r}  is a twisted self-correlation of the mu_N spectrum.

If the two halves (A_b=eta_b(mu_N), A_{gb}) are INCOHERENT on average, the 2r-th moment of the sum
has variance-adding behaviour => per-level factor ~ 2^r, and iterating over log2(n) levels from the
char-0 base gives E_r(mu_n) ~ 2^{r log2 n} = n^r = the Wick target = the AIC.

TEST: the per-level ratio  Q_r(N) := E_r(mu_{2N}) / (2^r E_r(mu_N)).
- Q_r ~ 1 (bounded, ideally ->1)  =>  recursion is tight, coherence O(1), AIC would follow.
- Q_r growing in r or per level  =>  coherence accumulates (the wall).
Also report E_r(mu_N)/Wick_N (Wick_N=(2r-1)!! N^r) to see sub-Gaussianity along the tower,
and the cross-correlation term directly.

All exact-ish (IEEE double) over a single p with 2^A | p-1, p ~ (2^A)^4 (thin at the TOP level).
"""
import sys, math
import numpy as np

def isprime(m):
    if m<2:return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37,41,43,47):
        if m%q==0:return m==q
    d=m-1;s=0
    while d%2==0:d//=2;s+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,m)
        if x in (1,m-1):continue
        for _ in range(s-1):
            x=x*x%m
            if x==m-1:break
        else:return False
    return True

def fp(mod,lo):
    p=lo-(lo%mod)+1
    if p<=lo:p+=mod
    while not isprime(p):p+=mod
    return p

def gen(p):
    pf=set();mm=p-1;d=2
    while d*d<=mm:
        while mm%d==0:pf.add(d);mm//=d
        d+=1
    if mm>1:pf.add(mm)
    g=2
    while any(pow(g,(p-1)//q,p)==1 for q in pf):g+=1
    return g

def df(k):
    r=1.0
    while k>1:r*=k;k-=2
    return r

def eta_all(p, N, g0):
    """eta_b(mu_N) for all b in F_p (length p), mu_N = <g0^{(p-1)/N}>."""
    h=pow(g0,(p-1)//N,p)
    mun=np.empty(N,dtype=np.int64);x=1
    for i in range(N):mun[i]=x;x=x*h%p
    b=np.arange(p)
    eta=np.empty(p,dtype=np.float64);tp=2*math.pi/p;CH=2048
    for s in range(0,p,CH):
        blk=b[s:s+CH]
        prod=(blk[:,None]*mun[None,:])%p
        eta[s:s+CH]=np.cos(tp*prod).sum(axis=1)
    return eta

def Er(eta, p, r):
    return float(np.sum(eta.astype(np.float64)**(2*r)))/p

def run(A, R=6):
    n=1<<A
    p=fp(n, n**4)              # p ~ n^4, 2^A | p-1 (mod=n=2^A ensures n|p-1; we need 2n|p-1 too)
    # ensure 2n | p-1 for the top doubling:
    while (p-1)%(2*n)!=0 or not isprime(p): p=fp(2*n, p+1)
    g0=gen(p)
    print(f"=== top n={n} p={p} (beta={math.log(p)/math.log(n):.2f}) ===")
    print(f"  per-level ratio Q_r(N)=E_r(mu_2N)/(2^r E_r(mu_N)); want Q_r~1 (bounded => recursion tight => AIC)")
    # build eta for each level 2,4,...,n (and 2n? top is n; levels N=2..n)
    levels=[1<<j for j in range(1,A+1)]
    etas={N: eta_all(p,N,g0) for N in levels}
    header="  level N ->2N | "+" ".join(f"Q_{r}" for r in range(1,R+1))
    print(header)
    for j in range(len(levels)-1):
        N=levels[j]; N2=levels[j+1]
        row=[]
        for r in range(1,R+1):
            e1=Er(etas[N],p,r); e2=Er(etas[N2],p,r)
            Q=e2/((2**r)*e1) if e1>0 else float('nan')
            row.append(Q)
        print(f"   {N:5d}->{N2:<5d} | "+" ".join(f"{q:5.3f}" for q in row))
    # sub-Gaussianity along the tower at top level
    print(f"  E_r(mu_n)/Wick_n (Wick=(2r-1)!! n^r) at top n={n}:")
    et=etas[n]
    print("    "+"  ".join(f"r={r}:{Er(et,p,r)/(df(2*r-1)*n**r):.3f}" for r in range(1,R+1)))
    print()

if __name__=='__main__':
    for A in ([int(a) for a in sys.argv[1:]] or [4,5,6]):
        run(A, R=6)
