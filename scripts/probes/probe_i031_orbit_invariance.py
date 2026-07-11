#!/usr/bin/env python3
"""Quick check: is |X_b| EXACTLY constant on dilation orbits b ~ ζ b for ζ in μ_n?
   If yes, the sup over F_p* = sup over the m=(p-1)/n orbit representatives,
   and chaining should be done on the QUOTIENT, not the full set.
   This is the I031 'process isometry collapses cosets to n orbits' claim.
   PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3, proper subgroup."""
import cmath, math

def isprime(m):
    if m < 2: return False
    if m % 2 == 0: return m == 2
    d=m-1;s=0
    while d%2==0: d//=2;s+=1
    for a in [2,3,5,7,11,13,17,19,23,29,31,37]:
        if a%m==0: continue
        x=pow(a,d,m)
        if x==1 or x==m-1: continue
        ok=False
        for _ in range(s-1):
            x=x*x%m
            if x==m-1: ok=True;break
        if not ok: return False
    return True

def find_prime(mu,beta):
    n=1<<mu; lo=int(n**beta); t=((lo//n)+1)*n+1
    while True:
        if isprime(t): return n,t
        t+=n

def subgroup(p,n):
    fac=[];x=p-1;d=2
    while d*d<=x:
        if x%d==0:
            fac.append(d)
            while x%d==0: x//=d
        d+=1
    if x>1: fac.append(x)
    g=None
    for c in range(2,p):
        if all(pow(c,(p-1)//q,p)!=1 for q in fac): g=c;break
    h=pow(g,(p-1)//n,p)
    H=[pow(h,i,p) for i in range(n)]
    assert len(set(H))==n and pow(h,n//2,p)!=1
    return h,H

for mu,beta in [(2,3.2),(3,3.2),(4,3.2),(5,3.2)]:
    n,p=find_prime(mu,beta)
    h,H=subgroup(p,n)
    w=2*math.pi/p
    def Xb(b): return sum(cmath.exp(1j*w*((b*x)%p)) for x in H)
    # Check |X_{h b}| == |X_b| for random b
    maxdiff=0.0
    import random; random.seed(1)
    for _ in range(50):
        b=random.randrange(1,p)
        v0=abs(Xb(b)); v1=abs(Xb((h*b)%p))
        maxdiff=max(maxdiff,abs(v0-v1))
    # number of orbits
    m=(p-1)//n
    print(f"n={n} p={p} m=(p-1)/n={m}  max||X_hb|-|X_b||={maxdiff:.2e}  (should be ~0)")
