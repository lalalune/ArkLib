#!/usr/bin/env python3
"""
FAST orbit engine (growth-numerics task): cache left_null(P) per orbit-rep R (independent of
a,b), reuse across all (a,b). Verified against the exact engine.
"""
import sys, itertools, time
from math import gcd
sys.path.insert(0, '/Users/shawwalters/ethereumroadmap/upstream/lean-research/ArkLib/scripts/probes')
from prize_workspace import subgroup, isprime

def find_prime_cong1(n, lo):
    p = lo + (1 - lo) % n
    while True:
        if p > 2 and p % n == 1 and isprime(p): return p
        p += n

def _rref(rows, p):
    rows=[r[:] for r in rows]; m=len(rows); nc=len(rows[0]) if m else 0; pr=0
    for c in range(nc):
        sel=next((r for r in range(pr,m) if rows[r][c]%p),None)
        if sel is None: continue
        rows[pr],rows[sel]=rows[sel],rows[pr]
        inv=pow(rows[pr][c],p-2,p); rows[pr]=[(x*inv)%p for x in rows[pr]]
        for r in range(m):
            if r!=pr and rows[r][c]%p:
                f=rows[r][c]; rows[r]=[(rows[r][j]-f*rows[pr][j])%p for j in range(nc)]
        pr+=1
        if pr==m: break
    return rows
def left_null(V,p):
    m=len(V); k=len(V[0]) if m else 0
    aug=[V[i][:]+[1 if j==i else 0 for j in range(m)] for i in range(m)]
    return [[row[k+j]%p for j in range(m)] for row in _rref(aug,p)
            if all(x%p==0 for x in row[:k]) and any(x%p for x in row[k:])]

def action_perms(S,p,n):
    idx={v:i for i,v in enumerate(S)}
    return [tuple(idx[(c*S[i])%p] for i in range(n)) for c in S]

def mun_orbit_reps(n, size, perms):
    seen=set(); reps=[]
    for R in itertools.combinations(range(n), size):
        Rf=frozenset(R)
        if Rf in seen: continue
        for perm in perms:
            seen.add(frozenset(perm[i] for i in R))
        reps.append(R)
    return reps

def mu_d_elements(S,p,n,d):
    return [x for x in S if pow(x,d,p)==1]

def build_rep_cache(S,p,k,reps):
    """For each rep R compute P (left-null of V_R)."""
    cache=[]
    for R in reps:
        V=[[pow(int(S[i]),j,p) for j in range(k)] for i in R]
        P=left_null(V,p)
        if not P: continue
        cache.append((R,P))
    return cache

def Spows(S,p,n):
    return [[pow(int(S[i]),e,p) for i in range(n)] for e in range(n)]

def Dstar_for_r(S,p,k,r,perms,SP):
    n=len(S); size=n-r
    if size<=k: return p,(None,None),True
    reps=mun_orbit_reps(n,size,perms)
    cache=build_rep_cache(S,p,k,reps)
    # precompute mu_d for each possible d (divisor of n)
    mud={d:mu_d_elements(S,p,n,d) for d in range(1,n+1) if n%d==0}
    best=(-1,None,False)
    for b in range(k,size):
        Sb=SP[b]
        for a in range(n):
            if a==b: continue
            Sa=SP[a]
            diff=(a-b)%n
            d = n // gcd(n, diff if diff!=0 else n)
            cosetgrp = mud[d]
            good=set(); sat=False
            for (R,P) in cache:
                rows=len(P)
                pa=[0]*rows; pb=[0]*rows
                for t in range(rows):
                    Pt=P[t]; sa=0; sb=0
                    for ii in range(size):
                        i=R[ii]; c=Pt[ii]
                        if c:
                            sa+=c*Sa[i]; sb+=c*Sb[i]
                    pa[t]=sa%p; pb[t]=sb%p
                # find first nonzero pb
                i0=-1
                for t in range(rows):
                    if pb[t]: i0=t; break
                if i0<0:
                    if all(x==0 for x in pa): sat=True; break
                    continue
                gg=(-pa[i0]*pow(pb[i0],p-2,p))%p
                ok=True
                for t in range(rows):
                    if (pa[t]+gg*pb[t])%p!=0: ok=False; break
                if ok:
                    for u in cosetgrp: good.add(gg*u%p)
            if sat: return p,(a,b),True
            if len(good)>best[0]: best=(len(good),(a,b),False)
    return best[0],best[1],best[2]

if __name__=='__main__':
    for (n,k,rs) in [(8,2,[3,4,5]),(16,4,[8,9,10])]:
        p=find_prime_cong1(n,200003); S=subgroup(p,n); perms=action_perms(S,p,n); SP=Spows(S,p,n)
        for r in rs:
            mx,st,sat=Dstar_for_r(S,p,k,r,perms,SP)
            print(f"n={n} k={k} r={r}: D*={'SAT' if sat else mx} binder={st}")
