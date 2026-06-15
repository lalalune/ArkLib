#!/usr/bin/env python3
"""Does a LARGER prime at n=32 restore thin>thick (thinness-essential) and push C* up?
If the C*=1 collapse is 'prize prime too small for N=16 (pigeonhole)', big p should lift it AND
separate thin from thick. Tests whether erosion is fundamental or a small-p artifact.
n=32, N=16, primes from prize p~n^4~1e6 up to ~n^8~1e12 (32 | p-1)."""
import numpy as np, random, math, statistics
def prim(p,m):
    e=(p-1)//(1<<m); rr=random.Random(p)
    for _ in range(2000):
        b=rr.randrange(2,p); c=pow(b,e,p)
        if pow(c,(1<<m)//2,p)==p-1: return c
def lll_float(B, delta=0.99):
    B=B.astype(np.float64).copy(); n=B.shape[0]
    def gso(B):
        n=B.shape[0]; Bs=np.zeros_like(B); mu=np.zeros((n,n))
        for i in range(n):
            Bs[i]=B[i].copy()
            for j in range(i):
                d=np.dot(Bs[j],Bs[j]); mu[i][j]=np.dot(B[i],Bs[j])/d if d else 0.0; Bs[i]-=mu[i][j]*Bs[j]
        return Bs,mu
    Bs,mu=gso(B); k=1; it=0
    while k<n and it<60000:
        it+=1
        for j in range(k-1,-1,-1):
            if abs(mu[k][j])>0.5: B[k]-=round(mu[k][j])*B[j]; Bs,mu=gso(B)
        if np.dot(Bs[k],Bs[k])>=(delta-mu[k][k-1]**2)*np.dot(Bs[k-1],Bs[k-1]): k+=1
        else: B[[k,k-1]]=B[[k-1,k]]; Bs,mu=gso(B); k=max(k-1,1)
    return np.rint(B).astype(np.int64)
def cstar_ub(a,p):
    N=len(a); B=np.zeros((N+1,N+1),dtype=np.float64)
    for j in range(N): B[j,j]=1.0; B[j,N]=p*a[j]
    B[N,N]=p*p
    R=lll_float(B); best=None
    for row in R:
        g=[int(x) for x in row[:N]]
        if any(g) and sum(c*x for c,x in zip(g,a))%p==0:
            h=max(abs(c) for c in g); best=h if best is None else min(best,h)
    if best is None: best=99
    return best
def thick(p,N,seed):
    rnd=random.Random(seed); s=set()
    while len(s)<N: s.add(rnd.randrange(1,p))
    return sorted(s)
def find_prime_ge(x,mod):
    # smallest prime >= x with mod | p-1
    import sympy
    k=(x+mod-1)//mod
    while True:
        p=k*mod+1
        if sympy.isprime(p): return p
        k+=1
m=5; n=32; N=16; mod=32
print(f"n={n} N={N}: C* vs prime size (thin 2-power vs thick median/5). Prize p~n^4~{n**4}.")
print(f"{'p':>13} {'beta':>5} {'2lnq':>5} {'thinC*':>7} {'thickMed':>8}  verdict")
for exp in [4, 5, 6]:
    p=find_prime_ge(n**exp, mod)
    w=prim(p,m); a=[pow(w,j,p) for j in range(N)]
    thin=cstar_ub(a,p)
    th=[cstar_ub(thick(p,N,s*977+ (p%1000000)),p) for s in range(5)]
    med=statistics.median(th)
    beta=math.log(p)/math.log(n); twolnq=2*math.log(p)
    verdict="THIN>thick" if thin>med else ("tie" if thin==med else "thin<thick")
    print(f"{p:>13} {beta:>5.2f} {twolnq:>5.1f} {thin:>7} {med:>8.0f}  {verdict}")
