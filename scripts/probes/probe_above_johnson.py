#!/usr/bin/env python3
"""Hypothesis R2 (regime-III round): does SMOOTHNESS matter ABOVE Johnson?
n=8,k=5,p=17 => rho=5/8=0.625, Johnson=1-sqrt(.625)=0.210, capacity=0.375.
delta=2/8=0.25 is STRICTLY above Johnson, strictly below capacity = regime (III).
Exact ε_mca (max over all stacks) is too expensive (p^6 pairs); SAMPLE stacks and compare the
sampled-max bad count for a smooth multiplicative subgroup domain vs random domains. Same sample
budget => fair relative signal on whether smoothness changes the above-Johnson bad count.
EVIDENCE ONLY (sampled max underestimates true max); not formalized as exact."""
import itertools, math, random
random.seed(20260611)
def evalp(c,x,p): return sum(c[i]*pow(x,i,p) for i in range(len(c)))%p
def codewords(p,D,k): return [tuple(evalp(c,x,p) for x in D) for c in itertools.product(range(p),repeat=k)]
def subgroup(p,n):
    for cand in range(2,p):
        o=1;y=cand%p
        while y!=1:y=(y*cand)%p;o+=1
        if o==p-1:g=cand;break
    if (p-1)%n: return None
    h=pow(g,(p-1)//n,p); return sorted({pow(h,i,p) for i in range(n)})

def sampled_epsmca(p,D,k,num,nsamp):
    n=len(D); C=codewords(p,D,k); delta=num/n; smin=math.ceil((1-delta)*n)
    Ss=[frozenset(c) for r in range(smin,n+1) for c in itertools.combinations(range(n),r)]
    patt={S:set(tuple(c[j] for j in sorted(S)) for c in C) for S in Ss}
    def ext(w,S): return tuple(w[sj] for sj in sorted(S)) in patt[S]
    Clist=C
    best=0
    for _ in range(nsamp):
        u0=list(random.choice(Clist)); 
        # random word = random codeword + random low-weight noise OR fully random; use fully random
        u0=[random.randrange(p) for _ in range(n)]
        u1=[random.randrange(p) for _ in range(n)]
        e0={S:ext(u0,S) for S in Ss}; e1={S:ext(u1,S) for S in Ss}
        joint={S:(e0[S] and e1[S]) for S in Ss}
        cnt=0
        for g in range(p):
            lp=[(u0[j]+g*u1[j])%p for j in range(n)]
            if any(ext(lp,S) and not joint[S] for S in Ss): cnt+=1
        if cnt>best: best=cnt
    return best
p,n,k,num=17,8,5,2
J=1-math.sqrt(k/n); cap=1-k/n
print(f"p={p} n={n} k={k} delta={num}/{n}={num/n:.3f}  Johnson={J:.3f} cap={cap:.3f}  (delta above Johnson: {num/n>J})")
sm=subgroup(p,n)
print(f"smooth subgroup order {n}: {sm}")
NS=4000
bs=sampled_epsmca(p,sm,k,num,NS)
print(f"  SMOOTH  sampled-max bad count ({NS} stacks): {bs}/17  = {bs/p:.4f}")
for r in range(3):
    D=sorted(random.sample(range(1,p),n))
    bn=sampled_epsmca(p,D,k,num,NS)
    print(f"  RANDOM domain {D}: sampled-max bad count: {bn}/17 = {bn/p:.4f}")
