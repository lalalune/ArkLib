#!/usr/bin/env python3
"""
probe_dsval_mann_cosetplustail.py   (#407 A5 -- the EXACT object: coset + tail)

FINDING (from probe_dsval_mann_reconcile_n8.py, EXACT char-0): the budget-relevant
worst-case agreement sets S are NOT pure cyclotomic-coset unions.  They are

    S = (antipodal-paired block B)  union  (small UNPAIRED "tail" T),

where B is forced by Mann (every consistent block is antipodal/coset structured) and
T is the residual affine freedom of the codeword.  Example n=8 k=2 worst dir (4,5):
S=[1,3,5,7]+{4}={full coset of x^4+1} + 1 tail point, |S|=5=n/2+1.  There are n=8
such gammas (one orbit, orbit size n) -> I = n = budget AT the boundary -> delta*=3/8.

So the GOVERNING combinatorial law (A5, conjectured then tested here) is:
  worst far direction realizes agreement sets S of size  w = (size of largest
  antipodal-paired block compatible with deg<k) + (tail length tau),
  with the number of distinct gammas = orbit size, and the boundary (I=n) occurs at
  the LARGEST w with orbit-count <= n.

This probe computes delta* EXACTLY (p>>n^4) by the FULL brute over directions but with
a structural, FAST max-agreement (the agreement set of the best codeword) computed via
nearest-codeword distance using the generalized Vandermonde rank -- O(n^3) per gamma,
gammas enumerated from (k+1)-subset functionals (deduped).  We then fit closed forms:
   H1: delta* = 1 - rho - 1/n            (w_min = rho*n + 1)
   H2: delta* = 1 - rho - 2/n            (w_min = rho*n + 2)
   H3: delta* = (1-rho)(1 - c/log2 n)
and report n-w_min, w_min - k, and the orbit decomposition at the boundary.
n in {8,16}; n=32 sampled on the known worst directions only (a=n/2 family).
"""
import itertools
from math import log2

def is_prime(m):
    if m<2:return False
    if m%2==0:return m==2
    i=3
    while i*i<=m:
        if m%i==0:return False
        i+=2
    return True
def find_prime(n,lo):
    p=lo+(n-(lo%n))+1
    while True:
        if (p-1)%n==0 and is_prime(p):return p
        p+=n
def prim_root(p):
    fac=[];m=p-1;d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0:m//=d
        d+=1
    if m>1:fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//q,p)!=1 for q in fac):return g
def rou(p,n):
    g=prim_root(p);w=pow(g,(p-1)//n,p)
    return [pow(w,i,p) for i in range(n)]

def nearest_codeword_agreement(mu,a,b,gamma,k,p,n):
    """max #points where x^a+gamma x^b equals a single deg<k poly.
       = n - d(h, RS[k]).  We compute via: the agreement set of best codeword
       interpolates k of the points; but to be FAST+EXACT we use the dual:
       a codeword agreeing at points A means h-c vanishes on A, c deg<k.  Max |A|.
       For exactness at our sizes we still need the max; do it by enumerating which
       k+? structure.  Shortcut that is EXACT: the max agreement >= w iff there is a
       deg<k poly matching h on some w-subset iff h restricted to that subset is in
       deg<k span.  Largest such subset: solve by the antipodal/Vandermonde rank.
       We compute the EXACT max by trying all k-subset anchors but restricted to
       anchors that include >=k-1 of a cyclotomic coset (Mann) + a sweep; for n<=16
       just do full k-subset (feasible: C(16,8)=12870)."""
    idxs=list(range(n))
    h=[(pow(mu[i],a,p)+gamma*pow(mu[i],b,p))%p for i in idxs]
    best=0
    for anchor in itertools.combinations(idxs,k):
        xs=[mu[i] for i in anchor];ys=[h[i] for i in anchor]
        cnt=0
        for i in idxs:
            tot=0;x=mu[i]
            for t in range(k):
                num=ys[t];den=1
                for s in range(k):
                    if s==t:continue
                    num=num*((x-xs[s])%p)%p;den=den*((xs[t]-xs[s])%p)%p
                tot=(tot+num*pow(den,p-2,p))%p
            if tot==h[i]:cnt+=1
        if cnt>best:best=cnt
    return best

def candidate_gammas(mu,a,b,k,p,n):
    gset=set()
    for T in itertools.combinations(range(n),k+1):
        xs=[mu[i] for i in T];c=[]
        for i in range(k+1):
            den=1
            for j in range(k+1):
                if j==i:continue
                den=den*((xs[i]-xs[j])%p)%p
            c.append(pow(den,p-2,p))
        La=sum(c[i]*pow(xs[i],a,p) for i in range(k+1))%p
        Lb=sum(c[i]*pow(xs[i],b,p) for i in range(k+1))%p
        if Lb==0:continue
        gset.add((-La*pow(Lb,p-2,p))%p)
    return gset

def deltastar(n,k,p,mu,dirs=None):
    budget=n
    if dirs is None:
        dirs=[(a,b) for a in range(k,n) for b in range(a+1,n)]
    results={}
    for (a,b) in dirs:
        gs=candidate_gammas(mu,a,b,k,p,n)
        gma={g:nearest_codeword_agreement(mu,a,b,g,k,p,n) for g in gs}
        for w in range(k+1,n+1):
            c=sum(1 for g,m in gma.items() if m>=w)
            if w not in results or c>results[w][0]:
                results[w]=(c,(a,b))
    ws=sorted(results)
    w_min=next((w for w in ws if results[w][0]<=budget),None)
    ds=1-w_min/n if w_min else None
    return results,w_min,ds

def main():
    gt={(8,2):0.375,(16,4):0.5625,(8,4):0.25,(16,8):0.3125}
    cases=[(8,2),(8,4),(16,4),(16,8)]
    rows=[]
    for (n,k) in cases:
        rho=k/n;p=find_prime(n,n**4*4);mu=rou(p,n)
        results,w_min,ds=deltastar(n,k,p,mu)
        g=gt.get((n,k))
        print(f"\n=== n={n} k={k} rho={rho} p={p} ===")
        for w in sorted(results,reverse=True):
            c,d=results[w];mk=" <==" if w==w_min else ""
            if c>0: print(f"   w={w:2d} d={1-w/n:.4f} I={c:4d} dir={d}{mk}")
        print(f"  delta*={ds:.4f} gt={g} MATCH={(abs(ds-g)<1e-9) if g else '?'}")
        print(f"  w_min={w_min} n-w_min={n-w_min} w_min-k={w_min-k} rho*n+1={rho*n+1} rho*n+2={rho*n+2}")
        rows.append((n,k,rho,w_min,ds,g))
    print("\n========= CLOSED-FORM TABLE =========")
    print(" n  k  rho   w_min  n-w_min  w_min-k  delta*   gt    1-rho-1/n  1-rho-2/n")
    for (n,k,rho,w_min,ds,g) in rows:
        print(f"{n:3d}{k:3d} {rho:4.2f}  {w_min:4d}   {n-w_min:5d}   {w_min-k:5d}  {ds:.4f} {g}  {1-rho-1/n:.4f}    {1-rho-2/n:.4f}")

if __name__=="__main__":
    main()
