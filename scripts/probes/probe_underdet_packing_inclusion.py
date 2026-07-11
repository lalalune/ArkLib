#!/usr/bin/env python3
"""
UNDER-DET lane (#444), PART 4 — the INCLUSION packing bound on #pinnedScalars at the binding band.

Established (push c5258ae16): distinct pinned scalars' agreement sets share only DEGENERATE overlap;
their non-degenerate cores are disjoint. The crude consequence #pinnedScalars <= C(n,k+1) is loose.

TIGHTER LEVER (this probe): each pinned scalar owns an agreement set A_g of size >= a (the binding
band). Distinct A_g, A_g' overlap NON-degenerately in <= k points. If we strip each A_g down to a
representative NON-degenerate core of size (a) and note the cores are pairwise (k)-bounded-overlap,
a standard inclusion / fractional-packing bound gives:
    #pinned * (a - k) <= |union of cores| <= n
  ==> #pinned <= n / (a - k).
At the binding band a ~ n/2 and rate k ~ n/4: a-k ~ n/4 ==> #pinned <= 4, a CONSTANT (matches the
probe collapse #pinned=1). At general rho=k/n: #pinned <= n/((1/2 - rho)n) = 1/(1/2 - rho) = O(1).

So the distinct-gamma count is BOUNDED BY A CONSTANT at the binding band (window-interior), under the
SET-DISJOINTNESS-MODULO-k packing — the sharing face cannot inflate #pinned beyond O(1). That O(1)
distinct-gamma cap, fed through epsMCA_le_of_pinnedScalars_card_le, gives epsMCA <= O(1)/p, i.e.
delta* PINNED AT THE CEILING with no window-interior gap FROM THIS FACE. (Beyond-Johnson, if any,
remains the per-gamma BGK char-sum magnitude, NOT the distinct-gamma COUNT.)

THIS PROBE verifies the inclusion bound numerically: for stacks with multiple pinned scalars, check
   #pinned <= n / (a - k)   (and the sharper |union of agreement sets| <= n with <=k overlaps).
Exact mod p, PROPER mu_n, p>>n^3, multi-prime, NEVER n=q-1.
"""
import itertools, random
from math import comb

def prime_factors(n):
    fs=set(); d=2
    while d*d<=n:
        while n%d==0: fs.add(d); n//=d
        d+=1
    if n>1: fs.add(n)
    return fs

def find_prime(n, lo):
    p=lo; p+=(1-p)%n
    if p<3: p=n+1
    while True:
        if p>2 and p%n==1 and all(p%d for d in range(2,int(p**0.5)+1)): return p
        p+=n

def find_g(p,n):
    for h in range(2,20000):
        x=pow(h,(p-1)//n,p)
        if pow(x,n,p)==1 and all(pow(x,n//q,p)!=1 for q in prime_factors(n)): return x
    raise ValueError

def ddiff(vals,T,xs,p):
    acc=0
    for i in T:
        den=1
        for j in T:
            if i!=j: den=den*((xs[i]-xs[j])%p)%p
        acc=(acc+vals[i]*pow(den,-1,p))%p
    return acc

def agreement_set(w,xs,p,k):
    """maximal set on which w is deg<k: seed from a zero-residual (k+1)-tuple, interpolate deg<k
    through k of its pts, collect all matching coords (= agreementSet of that explainer = maximal)."""
    n=len(xs); best=set()
    for T in itertools.combinations(range(n),k+1):
        if ddiff(w,T,xs,p)==0:
            ctx=list(T)[:k]
            def interp(x):
                s=0
                for a in ctx:
                    num=1; den=1
                    for b in ctx:
                        if a!=b: num=num*((x-xs[b])%p)%p; den=den*((xs[a]-xs[b])%p)%p
                    s=(s+w[a]*num*pow(den,-1,p))%p
                return s
            S=set(i for i in range(n) if w[i]==interp(xs[i]))
            if len(S)>len(best): best=S
    return best

def run(n,k,beta_lo,n_stacks=8):
    p=find_prime(n,max(beta_lo,n**3)); g=find_g(p,n)
    xs=[pow(g,i,p) for i in range(n)]
    a=n//2
    random.seed(11); rows=[]
    for trial in range(n_stacks):
        if trial==0:
            u0=[pow(x,n//2,p) for x in xs]; u1=[pow(x,n//2-1,p) for x in xs]; lbl="binder"
        elif trial==1:
            # plant a deep shared structure: two deg<k pencils crossing -> try to force >1 pinned
            c0=[random.randrange(p) for _ in range(k)]; c1=[random.randrange(p) for _ in range(k)]
            u0=[sum(c*pow(x,j,p) for j,c in enumerate(c0))%p for x in xs]
            u1=[sum(c*pow(x,j,p) for j,c in enumerate(c1))%p for x in xs]; lbl="degpencil"
        else:
            u0=[random.randrange(p) for _ in range(n)]; u1=[random.randrange(p) for _ in range(n)]; lbl=f"rand{trial}"
        Tlist=list(itertools.combinations(range(n),k+1))
        e0={T:ddiff(u0,T,xs,p) for T in Tlist}; e1={T:ddiff(u1,T,xs,p) for T in Tlist}
        cand=set((-e0[T]*pow(e1[T],-1,p))%p for T in Tlist if e1[T]!=0)
        pinned={}
        for gamma in cand:
            w=[(u0[i]+gamma*u1[i])%p for i in range(n)]
            A=agreement_set(w,xs,p,k)
            if len(A)>=a:
                nd=any(not(e0[T]==0 and e1[T]==0) for T in itertools.combinations(sorted(A),k+1))
                if nd: pinned[gamma]=A
        npinned=len(pinned)
        union=set().union(*pinned.values()) if pinned else set()
        bound = (n//(a-k)) if a-k>0 else n
        ok = npinned <= bound
        rows.append((lbl,npinned,len(union),a,k,bound,ok))
    return p,rows

if __name__=="__main__":
    for n in [8,12,16]:
        for k in [2]:
            p,rows=run(n,k,n**3)
            print(f"\n=== n={n} k={k} a={n//2} p={p}  inclusion bound n/(a-k)={n//(n//2-k) if n//2-k>0 else 'inf'} ===")
            print(f"  {'stack':>9} {'#pinned':>8} {'|union|':>8} {'a':>3} {'k':>3} {'n/(a-k)':>8} {'<=bound?':>8}")
            for lbl,npn,un,a,k_,bd,ok in rows:
                print(f"  {lbl:>9} {npn:>8} {un:>8} {a:>3} {k_:>3} {bd:>8} {str(ok):>8}")
