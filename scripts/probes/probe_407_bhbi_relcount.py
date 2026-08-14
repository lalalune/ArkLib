#!/usr/bin/env python3
"""Confirm the anti-rule-3 finding: at the prize prime (n=32, p~n^4), does thin 2-power omega have
MORE height-1 sign-relations than thick generic? Test several prize-regime primes (32|p-1, beta~4)."""
import numpy as np, random, math, itertools, statistics, sympy
def prim(p,m):
    e=(p-1)//(1<<m); rr=random.Random(p)
    for _ in range(2000):
        b=rr.randrange(2,p); c=pow(b,e,p)
        if pow(c,(1<<m)//2,p)==p-1: return c
def count_h1_vec(a,p):
    A=np.array(a,dtype=np.int64)
    tail=np.array(list(itertools.product((-1,0,1),repeat=12)),dtype=np.int64)
    tr=(tail@A[4:])%p; cnt=0
    for head in itertools.product((-1,0,1),repeat=4):
        h=head[0]*a[0]+head[1]*a[1]+head[2]*a[2]+head[3]*a[3]
        c=int(((h+tr)%p==0).sum())
        if not any(head): c-=1
        cnt+=c
    return cnt//2
def thick(p,N,seed):
    rnd=random.Random(seed); s=set()
    while len(s)<N: s.add(rnd.randrange(1,p))
    return sorted(s)
m=5; n=32; N=16
# several prize-regime primes near n^4=1048576, 32|p-1
primes=[]
k=(n**4)//32
while len(primes)<4:
    p=k*32+1
    if sympy.isprime(p): primes.append(p)
    k+=1
print(f"n=32 N=16 prize regime (p~n^4={n**4}): # height-1 sign-relations, thin vs thick(5 seeds)")
for p in primes:
    w=prim(p,m); a=[pow(w,j,p) for j in range(N)]
    thin=count_h1_vec(a,p)
    th=[count_h1_vec(thick(p,N,s*131+(p%97777)),p) for s in range(5)]
    med=statistics.median(th); beta=math.log(p)/math.log(n)
    verdict="THIN>thick (anti-rule3: 2-power has MORE relations)" if thin>med else ("tie" if thin==med else "thin<thick (rule3)")
    print(f"  p={p:>9} b={beta:.3f}: thin#={thin:>4}  thick med={med:.0f} ({th})  {verdict}")
