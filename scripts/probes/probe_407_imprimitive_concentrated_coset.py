#!/usr/bin/env python3
"""
THE INVERSE-LO LAW (candidate): for the monomial far-line direction (x^a, x^b), j=b-a,
the highly-concentrated bad gammas (those with max_agreement >= n/2, the explosion level)
form ONE coset of mu_{n/gcd(j,n)}, hence number EXACTLY n/gcd(j,n).

Test across all monomial directions; record #{gamma : max_agree >= threshold} and the
coset structure. The inverse-LO bound: #concentrated gamma <= n/gcd(j,n) <= n.
"""
import itertools
from math import gcd
from collections import defaultdict

def isprime(x):
    if x<2:return False
    for d in range(2,int(x**0.5)+1):
        if x%d==0:return False
    return True
def setup(n,plo):
    p=plo
    while not(p%n==1 and isprime(p)):p+=1
    for cand in range(2,p):
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in (2,3,5,7) if n%q==0):
            return p,cand,[pow(cand,i,p) for i in range(n)]

n=16;k=4;r=10
p,gg,mu=setup(n,200000)
combos=list(itertools.combinations(range(n),n-r))
def ddk(vals,pts,k,p):
    xs=pts[:k+1];vs=list(vals[:k+1])
    for j in range(1,k+1):
        for i in range(k,j-1,-1):
            vs[i]=(vs[i]-vs[i-1])*pow((xs[i]-xs[i-j])%p,p-2,p)%p
    return vs[k]
def in_RS(vals,pts,k,p):
    s=len(pts)
    if s<=k:return True
    for st in range(s-k):
        if ddk(vals[st:st+k+1],pts[st:st+k+1],k,p)!=0:return False
    return True
def mv(b):return [pow(x,b,p) for x in mu]
def concentrated_gammas(u0,u1,mult_thresh):
    gam=defaultdict(int)
    for R in combos:
        pts=[mu[i] for i in R];u0R=[u0[i] for i in R];u1R=[u1[i] for i in R]
        if in_RS(u1R,pts,k,p):continue
        a0=ddk(u0R,pts,k,p);a1=ddk(u1R,pts,k,p)
        if a1%p==0:continue
        g=(-a0*pow(a1,p-2,p))%p
        if in_RS([(u0R[i]+g*u1R[i])%p for i in range(len(R))],pts,k,p):
            gam[g]+=1
    return {g:m for g,m in gam.items() if m>=mult_thresh and g!=0}

def is_coset(gammas, n):
    """is the set a coset of mu_d for some d|n? return d if so."""
    gs=sorted(gammas)
    if len(gs)<=1: return len(gs)
    g0=gs[0]
    ratios=set((g*pow(g0,p-2,p))%p for g in gs)
    # check ratios form mu_d
    for d in [1,2,4,8,16]:
        mud=set(pow(gg,(p-1)//d*i if False else 0,p) for i in range(d))  # placeholder
    # simpler: all ratios r satisfy r^|gs|=1 and there are |gs| of them = mu_{|gs|}
    m=len(gs)
    allone = all(pow(rr,m,p)==1 for rr in ratios)
    return (m if allone and len(ratios)==m else 0)

print(f"p={p} n={n} k={k} r={r}; concentrated bad gammas (mult>=8, excl gamma=0):")
print(f"{'(a,b)':>10} {'j':>3} {'gcd':>3} {'#conc':>5} {'coset-mu_d':>10} {'n/gcd':>6}")
seen=set()
for a in range(k,n):
    for b in range(k,n):
        if a==b: continue
        if (b,a) in seen: continue
        seen.add((a,b))
        conc=concentrated_gammas(mv(a),mv(b),8)
        if not conc: continue
        d=is_coset(set(conc.keys()), n)
        jj=(b-a)%n
        print(f"{('('+str(a)+','+str(b)+')'):>10} {jj:>3} {gcd(jj,n):>3} {len(conc):>5} {('mu_'+str(d) if d else 'NOT-coset'):>10} {n//gcd(jj,n):>6}")
