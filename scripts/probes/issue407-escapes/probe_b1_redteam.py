#!/usr/bin/env python3
"""
RED-TEAM of B1 'binding = antipodal coset core' claim.
Properly exclude ALL degenerate directions: a dir (a,b) is degenerate if L=x^a+gamma x^b
is a function of x^g for some g>1 (g=gcd(a,b,n)) i.e. constant on mu_{n/g}-fibers, OR if the
agreeing codeword is forced trivial. We measure, per genuine direction, the largest |S| AND
whether it is a coset-union (excess 0) or genuinely ragged (excess>0). 
Key: is the MAX |S| over genuine dirs achieved by a coset-union or by a ragged set?
And: does requiring excess>0 give |S| <= sqrt(nk)? (the only thing R-thin needs)
"""
import math, itertools
from sympy import isprime, factorint
def find_prime(n,wm):
    p=max(wm,n+1); r=p%n
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
    Sset=set(Sidx); best=0; bestd=1
    for dprime in [d for d in range(2,n+1) if n%d==0]:
        step=n//dprime; covered=0
        for i in range(step):
            coset=set((i+step*t)%n for t in range(dprime))
            if coset<=Sset: covered+=len(coset)
        if covered>best: best=covered; bestd=dprime
    return best, bestd
def L_distinct(a,b,g,xs,p):
    return len(set((pow(x,a,p)+g*pow(x,b,p))%p for x in xs))

for (n,k) in [(8,2),(16,4),(16,6)]:
    p=find_prime(n,n*40+1); xs,w=mu_n(p,n); rho=k/n
    print(f"\n### n={n} k={k} p={p} rho={rho:.3f} sqrt(nk)={math.sqrt(n*k):.2f} ###")
    # over ALL dirs and worst gamma, record |S|, excess, distinct-vals, gcd(a,b,n)
    results=[]
    for a in range(k,n):
        for b in range(0,a):
            best=0;bestS=None;bg=None
            G=range(1,p) if p<=200 else range(1,p,max(1,(p-1)//100))
            for g in G:
                fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
                sz,S=max_agreement_set(fv,xs,k,p)
                if sz>best: best=sz;bestS=S;bg=g
            core,cd=coset_core(bestS,n); excess=best-core
            nd=L_distinct(a,b,bg,xs,p)
            gg=math.gcd(math.gcd(a,b),n)
            results.append((a,b,best,core,cd,excess,nd,gg))
    # genuine = L takes "many" distinct values (not folded): nd > n/2 say, and gg==1
    genuine=[r for r in results if r[6]>n//2 and r[7]==1]
    degen=[r for r in results if not(r[6]>n//2 and r[7]==1)]
    print(f"  ALL dirs: max|S|={max(r[2] for r in results)}")
    if genuine:
        gmax=max(genuine,key=lambda r:r[2])
        print(f"  GENUINE (nd>{n//2}, gcd(a,b,n)=1): {len(genuine)} dirs, max|S|={gmax[2]} at a={gmax[0]} b={gmax[1]} core={gmax[3]}(mu_{gmax[4]}) excess={gmax[5]} nd={gmax[6]}")
        # among genuine, are the max-|S| ones coset-unions (excess 0) or ragged?
        gen_ragged=[r for r in genuine if r[5]>0]
        gen_coset=[r for r in genuine if r[5]==0]
        print(f"    genuine coset-union(excess0): {len(gen_coset)}, max|S|={max((r[2] for r in gen_coset),default=0)}")
        print(f"    genuine ragged(excess>0):     {len(gen_ragged)}, max|S|={max((r[2] for r in gen_ragged),default=0)}, max-excess={max((r[5] for r in gen_ragged),default=0)}")
    else:
        print("  NO genuine dirs by this test")
