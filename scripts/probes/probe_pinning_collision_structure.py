#!/usr/bin/env python3
# Follow-up: the REAL slack in the packing bound is gamma-COLLISIONS (distinct subsets -> same gamma),
# NOT coset-rigidity of subsets. Measure the collision multiplicity structure & whether the COLLIDING
# subsets (those pinning a high-multiplicity gamma) are coset-structured / share algebraic structure.
import itertools
from collections import defaultdict
from math import comb

def isprime(m):
    if m<2: return False
    if m%2==0: return m==2
    d=3
    while d*d<=m:
        if m%d==0: return False
        d+=2
    return True
def find_prime(n,beta):
    t=((n**beta//n)+1)*n+1
    while not isprime(t): t+=n
    return t
def gen_sub(p,n):
    cof=(p-1)//n
    def order(a):
        o=1;x=a%p
        while x!=1: x=(x*a)%p;o+=1
        return o
    for c in range(2,p):
        h=pow(c,cof,p)
        if h!=1 and order(h)==n: return h
def inv(a,p): return pow(a,p-2,p)

def run(n,beta,r,is2):
    M=1; A=r*M; B=(r-1)*M; k=(r-2)*M+1 if r>=2 else 1; a=k+1
    if a>n: return
    p=find_prime(n,beta); g=gen_sub(p,n); mu=[pow(g,i,p) for i in range(n)]
    g2t=defaultdict(list)
    for S in itertools.combinations(range(n),a):
        pts=[mu[i] for i in S]
        u0=[pow(x,A,p) for x in pts]; u1=[pow(x,B,p) for x in pts]
        def topdd(v):
            dd=list(v)
            for lv in range(1,len(v)):
                dd=[((dd[i+1]-dd[i])*inv((pts[i+lv]-pts[i])%p,p))%p for i in range(len(v)-lv)]
            return dd[0]
        d1=topdd(u1)%p
        if d1==0: continue
        gS=(-(topdd(u0))*inv(d1,p))%p
        g2t[gS].append(S)
    mult=defaultdict(int)
    for gS,subs in g2t.items(): mult[len(subs)]+=1
    realized=len(g2t)
    half=n//2
    prize=(2**r)*comb(half,r) if is2 and r<=half else None
    # do high-multiplicity gammas have coset-structured colliding subset-UNIONS?
    coset_collide=0; tot_multi=0
    for gS,subs in g2t.items():
        if len(subs)<2: continue
        tot_multi+=1
        union=set()
        for S in subs: union|=set(S)
        # closed under some nontrivial subgroup shift?
        closed_any=False
        for d in range(2,n+1):
            if n%d: continue
            step=n//d
            if all(((i+step)%n) in union for i in union):
                closed_any=True; break
        if closed_any: coset_collide+=1
    print(f"n={n} r={r} k={k} a={a} p={p} is2={is2}: realized={realized} prize={prize} "
          f"C(n,a)={comb(n,a)}")
    print(f"   multiplicity histogram (#subsets-per-gamma : #gammas): {dict(sorted(mult.items()))}")
    print(f"   multi-gamma (mult>=2): {tot_multi}, of which coset-structured-union: {coset_collide}")
    print()

print("=== COLLISION STRUCTURE (the real packing slack) ===\n")
for mu in (3,4):
    for r in (2,3): run(1<<mu,4,r,True)
for n in (6,12):
    for r in (2,3): run(n,4,r,False)
