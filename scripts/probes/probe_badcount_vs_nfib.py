#!/usr/bin/env python3
"""
PROBE (#389): resolve the PROFILE-INEQUALITY FORK at the shallow past-Johnson band.

Earlier (probe_profile_inequality.py): the PLAIN RS list at a=3 exceeds N_fib (n=16: 17 vs 7).
Fork: is the actual MCA #bad-scalar count (the quantity that controls ε_mca/δ*) bounded by
  (A) ~ the plain list (=> floor LARGER than N_fib at the shallow band), or
  (B) ~ N_fib via the concentration mechanism (tower-extremality holds for the right object)?

We compute the WORST-CASE #bad directly from the mcaEvent definition over mu_n and compare to
N_fib(n,a) and to the plain worst-case list. #bad(u0,u1,a) = #{gamma : (u0+gamma*u1) agrees with a
deg<k codeword on a set S, |S|>=a, AND (u0,u1) is NON-JOINT on S (u1|S not on any codeword over >=a
points)}. Hill-climb (u0,u1) to maximize. N_fib(n,a)=C(n/2-a%2, a//2).
"""
import math, random
from itertools import product

def cw(co,D,p):
    o=[]
    for x in D:
        v=0;xp=1
        for c in co: v=(v+c*xp)%p; xp=(xp*x)%p
        o.append(v)
    return tuple(o)
def all_cws(D,k,p): return [cw(co,D,p) for co in product(range(p),repeat=k)]

def best_agreement_set(vals, C, a):
    """returns (max_agreement, an agreement set S as frozenset) — early exit not needed for small."""
    n=len(vals); best=0; bestS=None
    for c in C:
        S=[i for i in range(n) if c[i]==vals[i]]
        if len(S)>best: best=len(S); bestS=frozenset(S)
    return best, bestS

def u1_joint_on(u1, C, S, a):
    """does u1 restricted to S agree with SOME codeword on >= a points of S?"""
    Sl=sorted(S)
    for c in C:
        if sum(1 for i in Sl if c[i]==u1[i])>=a: return True
    return False

def badcount(u0,u1,C,p,a):
    n=len(u0); bad=0
    for g in range(p):
        vals=[(u0[i]+g*u1[i])%p for i in range(n)]
        agr,S=best_agreement_set(vals,C,a)
        if agr<a: continue
        if u1_joint_on(u1,C,S,a): continue   # joint -> not MCA-bad
        bad+=1
    return bad

def maxbad(D,k,p,a,rs,cl,rng):
    C=all_cws(D,k,p); n=len(D); best=0
    for _ in range(rs):
        u0=[rng.randrange(p) for _ in range(n)]; u1=[rng.randrange(p) for _ in range(n)]
        cur=badcount(u0,u1,C,p,a)
        for _ in range(cl):
            # tweak a coordinate of u0 or u1
            if rng.random()<0.5: w,u=0,u0
            else: w,u=1,u1
            i=rng.randrange(n); old=u[i]; u[i]=rng.randrange(p)
            nb=badcount(u0,u1,C,p,a)
            if nb>=cur: cur=nb
            else: u[i]=old
        best=max(best,cur)
    return best

def mun(p,n):
    if (p-1)%n: return None
    def od(x):
        o=1;c=x%p
        while c!=1:c=(c*x)%p;o+=1
        return o
    g=next((c for c in range(2,p) if od(c)==p-1),None)
    if g is None: return None
    b=pow(g,(p-1)//n,p);d=sorted({pow(b,i,p) for i in range(n)})
    return d if len(d)==n else None

def Nfib(n,a): return math.comb(n//2-(a%2), a//2)

def run(p,n,k,a,rs,cl,sd=0):
    D=mun(p,n)
    if D is None: print(f"(p={p} n={n}: no mu_n)",flush=True); return
    mb=maxbad(D,k,p,a,rs,cl,random.Random(sd))
    nf=Nfib(n,a)
    fork = "FORK-A: #bad>N_fib (floor LARGER than tower)" if mb>nf else "FORK-B: #bad<=N_fib (tower bounds #bad)"
    print(f"p={p} n={n} k={k} a={a}: maxbad(MCA)={mb}  N_fib(tower)={nf}  => {fork}",flush=True)

if __name__=="__main__":
    run(p=97, n=8,  k=2, a=3, rs=14, cl=16)
    run(p=193,n=8,  k=2, a=3, rs=12, cl=16)
    run(p=97, n=16, k=2, a=3, rs=6,  cl=20)
    print("===BADDONE===",flush=True)
