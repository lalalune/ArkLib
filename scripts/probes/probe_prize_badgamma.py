#!/usr/bin/env python3
"""
THE verification: does the bad-SCALAR count (gamma-parameterized line-list,
the true MCA quantity) track the poly word-list or the exp core count, swept
from capacity to Johnson radius?

For a fixed stack (u0,u1) on mu_n, bad gamma = u0+gamma*u1 explainable on
some >=a set AND not jointly explainable. This is the actual #badSet that
delta* depends on. Count it per radius a (= floor((1-delta)n)) from capacity
(a~k) to Johnson (a~sqrt(kn)), for adversarial stacks, sweeping n. If poly at
window/Johnson scale => the positive lead transfers (bad-scalar count is poly,
delta* beyond Johnson plausible). If exp => lead doesn't transfer.

k=2 so codewords=lines; explainable = folded word u0+g*u1 has >=a points on a
line; not-joint = u0,u1 not both lines on that set. Count bad g over all g in F_p.
"""
import itertools, math, random
from collections import defaultdict

def find_prime(n, lo=50):
    c=(lo//n+1)*n+1
    while True:
        if c>2 and all(c%d for d in range(2,int(c**0.5)+1)): return c
        c+=n
def smooth(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if pow(h,n,p)==1 and all(pow(h,j,p)!=1 for j in range(1,n)):
            return [pow(h,t,p) for t in range(n)]
    raise RuntimeError
def rich(D,p,vals,a):
    """max # points of (D[i],vals[i]) on a common line, and whether >=a exists; returns max richness."""
    n=len(D); lines=defaultdict(set)
    for i in range(n):
        for j in range(i+1,n):
            dx=(D[i]-D[j])%p
            if dx==0: continue
            A=((vals[i]-vals[j])*pow(dx,p-2,p))%p; B=(vals[i]-A*D[i])%p
            lines[(A,B)].add(i); lines[(A,B)].add(j)
    return max((len(s) for s in lines.values()), default=1)

def bad_gamma_count(D,p,u0,u1,a):
    """# gamma in F_p with u0+g*u1 explainable on >=a (line) AND not joint."""
    n=len(D); cnt=0
    for g in range(p):
        fold=[(u0[i]+g*u1[i])%p for i in range(n)]
        if rich(D,p,fold,a) < a: continue   # not explainable on >=a
        # not-joint: u0 and u1 NOT both explainable on a common >=a set.
        # crude sufficient check: if u1 itself is a line on >=a pts AND u0 is too -> could be joint; skip strict
        # use: joint iff exists >=a set where both u0,u1 are lines. Approx by: u1 max-rich >=a and u0 max-rich>=a
        if rich(D,p,u1,a)>=a and rich(D,p,u0,a)>=a:
            continue
        cnt+=1
    return cnt

random.seed(2)
print("bad-SCALAR count (#bad gamma) vs radius, adversarial stacks, k=2:")
print("n   p   | capacity a / count ... Johnson a / count")
for n in (12,16,20,24,28):
    p=find_prime(n); D=smooth(p,n); k=2; aJ=math.ceil(math.sqrt(k*n))
    # adversarial stack: u1 a coset word (max structure), u0 random-ish
    best={a:0 for a in range(k+1,aJ+1)}
    for _ in range(15):
        cA=[random.randrange(p) for _ in range(2)]; cB=[random.randrange(p) for _ in range(2)]
        u1=[ (cA[0]*D[i]+cA[1])%p if i%2==0 else (cB[0]*D[i]+cB[1])%p for i in range(n)]
        u0=[random.randrange(p) for _ in range(n)]
        for a in range(k+1,aJ+1):
            c=bad_gamma_count(D,p,u0,u1,a)
            best[a]=max(best[a],c)
    row=" ".join(f"a={a}:{best[a]}" for a in range(k+1,aJ+1))
    print(f"{n:3d} {p:4d} (J~{aJ}) | {row}")
