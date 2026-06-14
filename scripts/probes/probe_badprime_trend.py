# Map the bad-prime set (Excess(ln p) > Wick) across n=16,32,64,128. Does it proliferate?
import math
def isprime(x):
    if x<2: return False
    if x%2==0: return x==2
    d=3
    while d*d<=x:
        if x%d==0: return False
        d+=2
    return True
def primroot(p):
    fac=set(); m=p-1; d=2
    while d*d<=m:
        if m%d==0:
            fac.add(d)
            while m%d==0: m//=d
        d+=1
    if m>1: fac.add(m)
    for a in range(2,p):
        if all(pow(a,(p-1)//q,p)!=1 for q in fac): return a
def gmu(p,n):
    g=pow(primroot(p),(p-1)//n,p); return [pow(g,i,p) for i in range(n)]
def Er(roots,p,r):
    f=[0]*p
    for x in roots: f[x]+=1
    for _ in range(r-1):
        nf=[0]*p
        for t in range(p):
            ft=f[t]
            if ft:
                for x in roots: nf[(t+x)%p]+=ft
        f=nf
    return sum(v*v for v in f)
def dblfact(m):
    x=1
    while m>0: x*=m; m-=2
    return x
PMAX=8000
for n in [16,32,64,128]:
    bad=[]; worst=0; worstp=0; tot=0
    p=n+1
    while p<PMAX:
        if isprime(p):
            r=max(2,round(math.log(p)))
            E=Er(gmu(p,n),p,r)
            ratio=(E-(n**(2*r))/p)/(dblfact(2*r-1)*(n**r))
            tot+=1
            if ratio>1.0: bad.append((p,round(ratio,3)))
            if ratio>worst: worst=ratio; worstp=p
        p+=n
    frac=len(bad)/tot if tot else 0
    print(f"n={n:<4} primes<{PMAX}: {tot}  BAD={len(bad)} ({100*frac:.1f}%)  worst={worst:.3f}@p={worstp}",flush=True)
    print(f"        bad primes: {bad[:12]}{'...' if len(bad)>12 else ''}",flush=True)
