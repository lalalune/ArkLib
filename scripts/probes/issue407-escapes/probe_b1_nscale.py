#!/usr/bin/env python3
"""DECISIVE n-scaling test of the agent's 'realizability gap=0' claim.
The agent measured gap(realizable, G_circ)=0 at n=8,12,16. Comment 133 measured (n=64,k=16)
true max-ragged |S| <= 18 << count-relaxation 32-39, i.e. realizability gives a LARGE reduction
at larger n. We test: does gap(G_circ - realizable) open up as n grows, for a FIXED COSET-CORE
binding direction (where the agent claims gap=0)?

We can't enumerate C(n,k) Lagrange for big n. Instead test the COUNT-BUDGET G_circ (max roots in
mu_n of any poly on support {0..k-1,a,b}) vs a REALIZABLE construction lower bound, for the
ANTIPODAL binding direction, scaling n. Key: G_circ for the antipodal direction = can it be the
full antipodal coset (n/2)? And does a realizable single-c achieve it?

Cheaper proxy: for the antipodal-binding monomial direction a, b with d=2 (a-b even), the count
budget G_circ can in principle = n/2+ (half coset). Realizable: a CONSTANT or low-deg c hitting
the antipodal-symmetric values. We measure realizable max via a smarter search at moderate n.
"""
import math, itertools
from sympy import isprime, factorint
def find_prime(n,wm):
    p=max(wm,n+1); r=p%n
    if r!=1: p+=(1-r)%n
    while True:
        if p%n==1 and isprime(p): return p
        p+=n
def generator(p):
    fac=list(factorint(p-1).keys())
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): return c
def mu_n(p,n):
    g0=generator(p); w=pow(g0,(p-1)//n,p)
    return [pow(w,j,p) for j in range(n)], w

def realizable_max_for_dir(a,b,xs,k,p,gammas):
    """max over gamma, over deg<k codewords c, of agreement. Enumerate c via C(n,k) interp - only feasible small n.
    Returns max|S|."""
    n=len(xs); best=k; inv={}
    for g in gammas:
        fv=[(pow(xs[i],a,p)+g*pow(xs[i],b,p))%p for i in range(n)]
        for T in itertools.combinations(range(n),k):
            ag=0
            for j in range(n):
                xj=xs[j]; val=0
                for t in T:
                    term=fv[t]; xt=xs[t]
                    for s in T:
                        if s==t: continue
                        d=(xt-xs[s])%p
                        if d not in inv: inv[d]=pow(d,p-2,p)
                        term=term*((xj-xs[s])%p)%p*inv[d]%p
                    val=(val+term)%p
                if val==fv[j]%p: ag+=1
            if ag>best: best=ag
    return best

def kernel_vec(M,t,p):
    A=[[x%p for x in r] for r in M]; R=len(A); pc=[]; r=0
    for c in range(t):
        piv=None
        for rr in range(r,R):
            if A[rr][c]%p!=0: piv=rr;break
        if piv is None: continue
        A[r],A[piv]=A[piv],A[r]; iv=pow(A[r][c]%p,p-2,p); A[r]=[(x*iv)%p for x in A[r]]
        for rr in range(R):
            if rr!=r and A[rr][c]%p!=0:
                f=A[rr][c]%p; A[rr]=[(A[rr][cc]-f*A[r][cc])%p for cc in range(t)]
        pc.append(c); r+=1
        if r==R: break
    free=[c for c in range(t) if c not in pc]
    if not free: return None
    fc=free[0]; cv=[0]*t; cv[fc]=1
    for ri,p2 in enumerate(pc): cv[p2]=(-A[ri][fc])%p
    return cv
def G_circ(a,b,xs,k,p):
    E=sorted(set(list(range(k))+[a,b])); t=len(E)
    V=[[pow(x,e,p) for e in E] for x in xs]; n=len(xs); best=0
    for B in itertools.combinations(range(n),t-1):
        cv=kernel_vec([V[i] for i in B],t,p)
        if cv is None: continue
        cnt=sum(1 for x in range(n) if sum(V[x][j]*cv[j] for j in range(t))%p==0)
        if cnt>best: best=cnt
        if best==n: break
    return best

# For each n (2-power), pick the antipodal binding dir (a=n/2+2, b=n/2 -> d=2, even-symmetric? check)
# and a primitive far dir; compare realizable vs G_circ.
print(f"{'n':>4} {'k':>3} | antipodal-dir realiz vs Gcirc | gap || sqrt(nk)")
for (n,k) in [(8,2),(16,2),(8,3),(16,3),(16,4),(32,3)]:
    p=find_prime(n,200); xs,w=mu_n(p,n)
    # antipodal direction: a,b both even and a-b div by 2, with x^{a},x^{b} symmetric. Use a=n//2+?
    # The binding dirs found: n=16 a=11,b=9 (d=2, odd a-b... gcd(2,16)=2). a-b=2. pick a=n//2+3,b=n//2+1
    a=n//2+3; b=n//2+1
    if a>=n: a=n-1; b=n-3
    gammas=list(range(1,p,max(1,(p-1)//30)))
    if n<=16:
        R=realizable_max_for_dir(a,b,xs,k,p,gammas)
    else:
        R=-1  # too big to enumerate; mark
    Gc=G_circ(a,b,xs,k,p)
    print(f"{n:>4} {k:>3} | a={a} b={b} realiz={R} Gcirc={Gc} gap={Gc-R if R>=0 else 'NA'} || {math.sqrt(n*k):.1f}")
