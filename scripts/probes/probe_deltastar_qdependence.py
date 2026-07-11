#!/usr/bin/env python3
"""#389/#400 DECISIVE: is interior delta*(C,eps*) q-dependent at fixed (n,k,B)?
If yes, no (rho,B)-only closed formula (Johnson/entropy delta_ent) can EXACTLY
pin delta*.  We measure, per proper-subgroup prime p (n|p-1, p>17 so mu_n!=F_p^*),
the max agreement-list size of the dim-(k+1) supercode at each agreement a, and
read the crossing amin = min a with incidence <= B.  delta*(p)=1-amin/n.
"""
import sys, random
from itertools import combinations

def primitive_root(p):
    fac=[]; m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.append(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.append(m)
    for g in range(2,p):
        if all(pow(g,(p-1)//f,p)!=1 for f in fac): return g

def subgroup(p,n):
    g=primitive_root(p); h=pow(g,(p-1)//n,p)
    D=[]; x=1
    for _ in range(n): D.append(x); x=x*h%p
    return D

def main():
    n=16; k=2; deg=k+1; B=n
    print(f"n={n} k={k} supercode deg<={deg} B={B}",flush=True)
    primes=[97,113,193,241,257,337]
    for p in primes:
        D=subgroup(p,n)
        inv=[0]*p
        for x in range(1,p): inv[x]=pow(x,p-2,p)
        # precompute, for each (deg+1)-subset S, the Lagrange basis coeffs L_{S,s}(i)
        # so interp value at coord i = sum_s u[s]*W[S][i][s].  Precompute W once (u-indep).
        subs=list(combinations(range(n),deg+1))
        # W[si][i] = dict s->weight
        def weight(sub,i):
            res={}
            for s in sub:
                num=1; den=1; xi=D[i]; xs=D[s]
                for t in sub:
                    if t==s: continue
                    num=num*((xi-D[t])%p)%p
                    den=den*((xs-D[t])%p)%p
                res[s]=num*inv[den]%p
            return res
        W=[[weight(sub,i) for i in range(n)] for sub in subs]
        rnd=random.Random(p)
        # centers: power words x^j and random deg<=deg+1 combos
        cands=[]
        for j in range(deg+1,deg+5):
            cands.append(tuple(pow(x,j,p) for x in D))
        for _ in range(40):
            c=[rnd.randrange(p) for _ in range(deg+2)]
            cands.append(tuple(sum(c[e]*pow(x,e,p) for e in range(deg+2))%p for x in D))
        # per agreement a, max over centers of #distinct deg<=deg polys agreeing>=a
        results={}
        for a in range(n,deg,-1):
            best=0
            for u in cands:
                polys=set()
                for si,sub in enumerate(subs):
                    Wi=W[si]
                    w=tuple(sum(u[s]*Wi[i][s] for s in sub)%p for i in range(n))
                    ag=0
                    for i in range(n):
                        if w[i]==u[i]: ag+=1
                    if ag>=a: polys.add(w)
                if len(polys)>best: best=len(polys)
            results[a]=best
        ok=[a for a in results if results[a]<=B]
        amin=min(ok) if ok else n
        print(f"  p={p:4d}: amin(inc<=B)={amin} delta*={1-amin/n:.4f} | " +
              " ".join(f"{a}:{results[a]}" for a in range(n,deg,-1)),flush=True)
main()
