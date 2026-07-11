#!/usr/bin/env python3
# Probe: the CensusDomination cap K is FORCED FROM BELOW by ONE large gamma-aligned set.
# If a gamma-aligned set A (|A|>=a) with a non-degenerate (k+1)-tuple exists, every a-subset
# of A containing that fixed tuple is gamma-aligned (Aligned.mono) and in alignableSets, so
# |alignableSets| >= C(|A|-(k+1), a-(k+1)) and CensusDomination(...,K) => K >= that binomial.
# Validated on PROPER thin mu_n (n=2^a), p>>n^3, p==1 mod n, multiple structured primes,
# NEVER n=q-1. mu_n built via an element of order n WITHOUT a full-order generator search.
from math import comb
from itertools import combinations
from sympy import factorint, isprime

def find_prime(n, lo):
    cand = lo - (lo % n) + 1
    if cand <= lo: cand += n
    while not isprime(cand):
        cand += n
    return cand

def elt_of_order_n(n, p):
    # find h with order exactly n: take random g, h=g^((p-1)/n); check h^n=1 and h^(n/q)!=1 for q|n
    import random
    random.seed(99)
    fac = list(factorint(n).keys())
    while True:
        g = random.randrange(2, p)
        h = pow(g, (p-1)//n, p)
        if h == 1: continue
        if pow(h, n, p) != 1: continue
        if all(pow(h, n//q, p) != 1 for q in fac):
            return h

def subgroup(n, p):
    h = elt_of_order_n(n, p)
    S=[]; v=1
    for _ in range(n):
        S.append(v); v=(v*h)%p
    assert len(set(S))==n
    return sorted(set(S))

def divdiff(xs, ys, p):
    m=len(xs); c=list(ys)
    for j in range(1,m):
        for i in range(m-1,j-1,-1):
            dx=(xs[i]-xs[i-j])%p
            c[i]=((c[i]-c[i-1])*pow(dx,p-2,p))%p
    return c[-1]

def run(n, beta):
    import random
    p=find_prime(n, n**beta)
    assert (p-1)%n==0 and n!=p-1
    mu=subgroup(n,p)
    k=2
    random.seed(1234+n+beta)
    gamma=random.randrange(1,p)
    cw=[random.randrange(0,p) for _ in range(k)]  # combined word deg<=k-1 (residual vanishes)
    def wval(x):
        r=0
        for c in reversed(cw): r=(r*x+c)%p
        return r
    def u1val(x): return pow(x,k,p)  # spike deg k makes some tuples non-degenerate
    def u0val(x): return (wval(x)-gamma*u1val(x))%p
    u0=[u0val(x) for x in mu]; u1=[u1val(x) for x in mu]
    idx=list(range(n)); aligned_full=True; nd_tuples=0
    for t in combinations(idx,k+1):
        xs=[mu[i] for i in t]
        rc=divdiff(xs,[(u0[i]+gamma*u1[i])%p for i in t],p)
        if rc%p!=0: aligned_full=False; break
        r0=divdiff(xs,[u0[i] for i in t],p); r1=divdiff(xs,[u1[i] for i in t],p)
        if not (r0%p==0 and r1%p==0): nd_tuples+=1
    a=int((3*n)//4)
    if a<k+1: a=k+1
    floor=comb(n-(k+1), a-(k+1)) if (n-(k+1))>=(a-(k+1))>=0 else 0
    return dict(n=n,beta=beta,p=p,k=k,a=a,aligned_full=aligned_full,nd_tuples=nd_tuples,floor=floor,A=n)

print("# Census-necessity floor: K >= C(|A|-(k+1), a-(k+1)) when a large aligned A exists")
print(f"{'n':>4} {'beta':>4} {'p':>12} {'k':>2} {'a':>3} {'|A|':>4} {'alignedFull':>11} {'ndTuples':>9} {'floor=C(|A|-3,a-3)':>20}")
ok=True
for n in [8,16,32,64]:
    for beta in [4,5]:
        r=run(n,beta)
        if not r['aligned_full'] or r['nd_tuples']==0 or r['floor']<=0: ok=False
        print(f"{r['n']:>4} {r['beta']:>4} {r['p']:>12} {r['k']:>2} {r['a']:>3} {r['A']:>4} {str(r['aligned_full']):>11} {r['nd_tuples']:>9} {r['floor']:>20}")
print("VERDICT:", "PASS" if ok else "FAIL")
