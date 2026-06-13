#!/usr/bin/env python3
"""
Aggressive refutation attempt: can a stack exceed 31 bad scalars?
(p=12289, n=16, k=3, s=7).  If yes => obligation SubCeilingInteriorCeiling
<= 31 is FALSE at eps*=31/p (major finding: swarm's delta*=5/8 rung
unreachable at that budget, needs smaller eps*).

Incidence-informed construction: pick several quadratics for R1 (agreement
6-sets, pairwise <=2 overlap, fitting in 16 pts) AND frames for R0 on the
same sets, gluing-consistent on overlaps; solve R0,R1 values; plant attached
bad scalars per class in its reservoir; exact census the result.  Sweep many
class-count / size / overlap patterns and report the global max.
"""
import itertools, random
from collections import Counter

p, n, s = 12289, 16, 7
g0 = next(g for g in range(2, 500)
          if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)))
w = pow(g0, (p - 1) // n, p)
D = [pow(w, j, p) for j in range(n)]

def polmul(a, b):
    o = [0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): o[i+j]=(o[i+j]+x*y)%p
    return o
def peval(f,x):
    r=0
    for c in reversed(f): r=(r*x+c)%p
    return r
def interp(pts,vals):
    m=len(pts); co=[0]*m
    for i in range(m):
        num=[1]; den=1
        for j in range(m):
            if j==i: continue
            num=polmul(num,[(-pts[j])%p,1]); den=den*((pts[i]-pts[j])%p)%p
        ci=vals[i]*pow(den,p-2,p)%p
        for t in range(len(num)): co[t]=(co[t]+ci*num[t])%p
    return co

SUBS=list(itertools.combinations(range(n),s))
MATS=[]
for S in SUBS:
    pts=[D[i] for i in S]; M=[[0]*s for _ in range(4)]
    for j in range(s):
        num=[1]; den=1
        for t in range(s):
            if t==j: continue
            num=polmul(num,[(-pts[t])%p,1]); den=den*((pts[j]-pts[t])%p)%p
        di=pow(den,p-2,p)
        for r in range(4):
            c=num[r+3] if r+3<len(num) else 0; M[r][j]=c*di%p
    MATS.append((S,M))
def census(u0,u1):
    bad=set()
    for S,M in MATS:
        v0=[u0[i] for i in S]; v1=[u1[i] for i in S]
        tb=[sum(M[r][j]*v1[j] for j in range(s))%p for r in range(4)]
        if not any(tb): continue
        ta=[sum(M[r][j]*v0[j] for j in range(s))%p for r in range(4)]
        j=next(t for t in range(4) if tb[t])
        gam=(-ta[j])*pow(tb[j],p-2,p)%p
        if all((ta[t]+gam*tb[t])%p==0 for t in range(4)): bad.add(gam)
    return len(bad)

# class-set patterns: lists of 6-subsets w/ pairwise overlap <=2, union<=16
def gen_patterns():
    pats=[]
    # 2 disjoint blocks (record): baseline
    pats.append([list(range(6)),list(range(6,12))])
    # 2 blocks + partial 3rd sharing 2 with each
    pats.append([list(range(6)),list(range(6,12)),[0,1,6,7,12,13]])
    # 3 blocks pairwise sharing 2, tighter pack
    pats.append([[0,1,2,3,4,5],[4,5,6,7,8,9],[8,9,10,11,12,13]])
    # 3 size-5 + spread
    pats.append([[0,1,2,3,4],[5,6,7,8,9],[10,11,12,13,14]])
    # 4 size-5 chained overlap 1-2
    pats.append([[0,1,2,3,4],[3,4,5,6,7],[7,8,9,10,11],[11,12,13,14,15]])
    return pats

best=0; best_info=None
rng=random.Random(2024)
for pat in gen_patterns():
    covered=sorted(set().union(*[set(b) for b in pat]))
    free=[i for i in range(n) if i not in covered]
    for trial in range(40):
        # choose quadratics per class, gluing-consistent on overlaps
        # assign each covered point a "primary" class (first containing it)
        prim={}
        for ci,b in enumerate(pat):
            for i in b: prim.setdefault(i,ci)
        # random quadratics; enforce overlap consistency by solving R1 vals
        qs=[[rng.randrange(p) for _ in range(3)] for _ in pat]
        rs=[[rng.randrange(p) for _ in range(3)] for _ in pat]
        # overlap consistency: for i in A_a∩A_b need q_a(D[i])=q_b(D[i]).
        # enforce by setting R1[i]=q_{prim[i]}(D[i]); agreement on non-primary
        # classes then needs q_other(D[i])==that — only counts if equal.
        u1=[0]*n; u0=[0]*n
        for i in covered:
            u1[i]=peval(qs[prim[i]],D[i]); u0[i]=peval(rs[prim[i]],D[i])
        for i in free:
            # steer a fresh bad scalar via two random gammas (like record)
            ga,gb=rng.randrange(1,p),rng.randrange(1,p)
            if ga==gb: gb=(gb+1)%p or 1
            c1,c2=rng.randrange(len(pat)),rng.randrange(len(pat))
            x=D[i]
            rh1=(peval(rs[c1],x)+ga*peval(qs[c1],x))%p
            rh2=(peval(rs[c2],x)+gb*peval(qs[c2],x))%p
            det=(ga-gb)%p
            if det==0: u1[i]=rng.randrange(p); u0[i]=rng.randrange(p); continue
            R1x=(rh1-rh2)*pow(det,p-2,p)%p
            u1[i]=R1x; u0[i]=(rh1-ga*R1x)%p
        c=census(u0,u1)
        if c>best:
            best=c; best_info=(len(pat),[len(b) for b in pat],len(free))
            if c>31:
                print(f"  *** BEAT 31: total={c}, pattern {best_info} ***")
print(f"REFUTE-31 RESULT: max bad = {best} (info classes,sizes,free={best_info}); "
      f"obligation bound 31; {'REFUTED!' if best>31 else 'holds in this sweep'}")
