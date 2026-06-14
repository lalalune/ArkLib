#!/usr/bin/env python3
import itertools, math
def evalp(c,x,p): return sum(c[i]*pow(x,i,p) for i in range(len(c)))%p
def codewords(p,D,k): return [tuple(evalp(c,x,p) for x in D) for c in itertools.product(range(p),repeat=k)]
def subgroup(p,n):
    for cand in range(2,p):
        o=1;y=cand%p
        while y!=1:y=(y*cand)%p;o+=1
        if o==p-1:g=cand;break
    if (p-1)%n: return None
    h=pow(g,(p-1)//n,p); return sorted({pow(h,i,p) for i in range(n)})

def epsmca(p,D,k,num):
    n=len(D); C=codewords(p,D,k); delta=num/n; smin=math.ceil((1-delta)*n)
    Ss=[frozenset(c) for r in range(smin,n+1) for c in itertools.combinations(range(n),r)]
    # precompute, per S, the set of agreement-patterns realizable by codewords: dict S-> set of tuple(c[j] for j in S)
    patt={S:set(tuple(c[j] for j in sorted(S)) for c in C) for S in Ss}
    def ext(w,S): return tuple(w[sj] for sj in sorted(S)) in patt[S]
    best=0
    for tail0 in itertools.product(range(p),repeat=n-k):
        u0=[0]*k+list(tail0); e0={S:ext(u0,S) for S in Ss}
        for tail1 in itertools.product(range(p),repeat=n-k):
            u1=[0]*k+list(tail1); e1={S:ext(u1,S) for S in Ss}
            joint={S:(e0[S] and e1[S]) for S in Ss}
            cnt=0
            for g in range(p):
                lp=[(u0[j]+g*u1[j])%p for j in range(n)]
                if any(ext(lp,S) and not joint[S] for S in Ss): cnt+=1
            if cnt>best: best=cnt
    return best
p,n,k=13,4,2
sm=subgroup(p,n); ns=[1,2,3,4]
print(f"p={p} n={n} k={k} rho=1/2 Johnson={1-math.sqrt(.5):.3f} cap=0.5  smooth={sm}")
for num in (1,2):
    bs=epsmca(p,sm,k,num); bn=epsmca(p,ns,k,num)
    print(f"  delta={num}/4: smooth eps_mca={bs}/13   nonsmooth={bn}/13")
