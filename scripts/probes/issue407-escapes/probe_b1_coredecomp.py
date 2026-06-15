#!/usr/bin/env python3
"""
B1 CORE/EXCESS decomposition at the worst GENUINE direction.

For the worst genuine direction (a,b,gamma) with agreement set S (size = realizMaxS):
  - coset core = largest mu_d'-coset-union subset of S (the Kambire/BGK bad-side part)
  - ragged excess = |S| - |core|  (the part R-thin/SparseRaggedExcessBound bounds)

Decisive question: is the BINDING |S| dominated by the CORE (=> R-thin's excess bound is
vacuous for the prize; the prize quantity is the core = BGK) or by the EXCESS (=> R-thin matters)?

We compute the ACTUAL agreement set S for the worst (a,b,gamma) found, then find its largest
mu_d'-coset-union subcore by checking, for each divisor d'|n with d'>1, the largest union of full
mu_d'-cosets contained in S.
"""
import itertools, math
from sympy import isprime, factorint

def find_prime(n,want_min):
    p=max(want_min,n+1); r=p%n
    if r!=1: p+=(1-r)%n
    while True:
        if p%n==1 and isprime(p): return p
        p+=n
def generator(p):
    fac=list(factorint(p-1).keys())
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): return c
def mu_n(p,n):
    g0=generator(p); w=pow(g0,(p-1)//n,p)
    return [pow(w,j,p) for j in range(n)], w

def max_agreement_set(fv,xs,k,p):
    """return (best_size, best_agreement_index_set) over deg<k polys."""
    n=len(xs)
    if k>=n: return n, set(range(n))
    best=k; bestS=set(range(k))
    for T in itertools.combinations(range(n),k):
        Tl=list(T); ag=set()
        for j in range(n):
            xj=xs[j]; val=0
            for t in Tl:
                term=fv[t]; xt=xs[t]
                for s in Tl:
                    if s==t: continue
                    term=(term*((xj-xs[s])%p))%p
                    term=(term*pow((xt-xs[s])%p,p-2,p))%p
                val=(val+term)%p
            if val==fv[j]%p: ag.add(j)
        if len(ag)>best: best=len(ag); bestS=ag
    return best, bestS

def coset_core(Sidx, n):
    """largest mu_d'-coset-union subset of S (indices in Z/n). cosets of mu_d' = arithmetic
       progressions of step n/d' ... mu_d' = {w^{(n/d')*t}}; its cosets are i + (n/d')*Z mod n.
       For each divisor d'>1 of n, group indices by residue mod (n/d'); a full coset present iff
       all d' members of that residue class (the mu_d'-coset has size d') are in S.
       mu_{d'} has order d', its coset reps are step (n/d'). The coset of index i = {i + (n/d')*t mod n: t}
       size = d'. Count max over d'>1 of #indices in S that lie in fully-present cosets."""
    Sset=set(Sidx); best=0; bestd=1
    divs=[d for d in range(2,n+1) if n%d==0]
    for dprime in divs:
        step=n//dprime
        covered=0
        for i in range(step):  # residue classes mod step; each class = one mu_dprime coset of size dprime
            coset=set((i+step*t)%n for t in range(dprime))
            if coset<=Sset:
                covered+=len(coset)
        if covered>best: best=covered; bestd=dprime
    return best, bestd

def main():
    print("="*100)
    print("B1 CORE/EXCESS decomposition at WORST GENUINE direction")
    # worst genuine dirs found earlier (correlation-excluded):
    cases=[(8,2,(4,2)),(12,3,(8,4)),(12,3,(9,5)),(12,3,(10,6))]
    for (n,k,(a,b)) in cases:
        p=find_prime(n,n*40+1); xs,w=mu_n(p,n)
        # find worst gamma for this dir
        bestsize=0;bestset=None;bg=None
        G=range(1,p)
        if p>200: G=range(1,p,max(1,(p-1)//120))
        for g in G:
            fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
            sz,S=max_agreement_set(fv,xs,k,p)
            if sz>bestsize: bestsize=sz;bestset=S;bg=g
        core,cd=coset_core(bestset,n)
        excess=bestsize-core
        print(f"  n={n} k={k} dir a={a} b={b} (d={math.gcd(a-b,n)}) gamma={bg}: "
              f"|S|={bestsize}  coset-core={core}(mu_{cd})  ragged-EXCESS={excess}  "
              f"| sqrt(nk)={math.sqrt(n*k):.1f} k+1={k+1} s=n/d={n//math.gcd(a-b,n)}")
    print("DONE")

if __name__=="__main__":
    main()
