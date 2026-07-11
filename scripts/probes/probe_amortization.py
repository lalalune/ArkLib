#!/usr/bin/env python3
"""
PROBE (#389): the SUPPLY->#bad AMORTIZATION across the good/bad boundary.

Fork result: #bad >> N_fib, separated by affine-line multiplicity (one witness codeword serves
many bad gamma). KEY question for the floor: is that multiplicity BOUNDED?
  - if #bad ~ Lambda (line-list of distinct witnesses), list bounds control #bad => floor follows.
  - if #bad/Lambda grows, the amortization is the wall.

For mu_n, sweep agreement a from Johnson down to capacity; at each, hill-climb the worst stack for
#bad, and report:
  maxbad        = max #{MCA-bad gamma}
  Lambda        = #distinct witness codewords over the bad gamma (the affine-line list)
  mult          = maxbad / Lambda   (average multiplicity per witness codeword)
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

def best_wit(vals,C,a):
    n=len(vals);best=0;bc=None
    for c in C:
        ag=0
        for i in range(n):
            if c[i]==vals[i]: ag+=1
        if ag>best: best=ag; bc=c
    return (best, bc) if best>=a else (best,None)
def joint(u1,C,bc,vals,a):
    # witness set S = where bc==vals; check u1|S on some codeword >=a
    n=len(vals); Sl=[i for i in range(n) if bc[i]==vals[i]]
    for c in C:
        cnt=0
        for i in Sl:
            if c[i]==u1[i]:
                cnt+=1
                if cnt>=a: return True
    return False
def bad_and_witnesses(u0,u1,C,p,a):
    n=len(u0); wits=set(); bad=0
    for g in range(p):
        vals=[(u0[i]+g*u1[i])%p for i in range(n)]
        ag,bc=best_wit(vals,C,a)
        if ag<a: continue
        if joint(u1,C,bc,vals,a): continue
        bad+=1; wits.add(bc)
    return bad, len(wits)
def maxbad(D,k,p,a,rs,cl,rng):
    C=all_cws(D,k,p);n=len(D);best=0;bestLam=0
    for _ in range(rs):
        u0=[rng.randrange(p) for _ in range(n)];u1=[rng.randrange(p) for _ in range(n)]
        cur,lam=bad_and_witnesses(u0,u1,C,p,a)
        for _ in range(cl):
            u=u0 if rng.random()<0.5 else u1
            i=rng.randrange(n);old=u[i];u[i]=rng.randrange(p)
            nb,nl=bad_and_witnesses(u0,u1,C,p,a)
            if nb>=cur: cur=nb; lam=nl
            else: u[i]=old
        if cur>best: best=cur; bestLam=lam
    return best,bestLam
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

def run(p,n,k,rs,cl,sd=0):
    D=mun(p,n)
    if D is None: print(f"(p={p} n={n}: no mu_n)",flush=True); return
    J=math.sqrt(n*k)
    print(f"\np={p} n={n} k={k} q={p} Johnson agr={J:.2f}",flush=True)
    print(f"   {'a':>2} {'reg':>5} | {'maxbad':>6} {'Lambda':>6} {'mult=bad/Lam':>13} {'eps_mca=bad/q':>13}",flush=True)
    for a in range(k+1, math.ceil(J)+2):
        mb,lam=maxbad(D,k,p,a,rs,cl,random.Random(sd))
        mult = (mb/lam) if lam>0 else 0.0
        reg = "PAST" if a<J else " - "
        print(f"   {a:>2} {reg:>5} | {mb:>6} {lam:>6} {mult:>13.2f} {mb/p:>13.3f}",flush=True)
    print(flush=True)

if __name__=="__main__":
    run(p=97, n=8, k=2, rs=8, cl=10)
    run(p=193,n=8, k=2, rs=6, cl=10)
    print("===AMORTDONE===",flush=True)
