#!/usr/bin/env python3
"""I031 RISK TEST: vary n at FIXED thin beta=4. Does the chaining constant
   C := M / (sqrt(n) * g2q) stay BOUNDED as n grows, OR does it blow up (the
   deterministic-vs-random RIP gap = the stated RISK)?

   ALSO: does g2q/sqrt(log m) stay bounded as n grows (the entropy telescoping
   uniform in n)?  If BOTH bounded -> I031 predicts M <= C sqrt(n log(p/n)) with
   an n-uniform constant => EXPONENT 1/2, beating 1-o(1).  This is the decisive
   honest check: the prior moment methods all had the CONSTANT/exponent creep.

   PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3, proper subgroup.
"""
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

def orbit_reps(p,n,h):
    seen=bytearray(p); reps=[]
    for b in range(1,p):
        if seen[b]: continue
        x=b; mn=b
        for _ in range(n):
            seen[x]=1
            if x<mn: mn=x
            x=(x*h)%p
        reps.append(mn)
    return reps

print("VARY n at fixed beta=4 (thin): is the chaining constant C n-UNIFORM?")
print(f"{'n':>4}{'p':>11}{'m':>9}  {'M':>8}{'floor':>8}{'M/fl':>6}"
      f"  {'g2q':>6}{'g2q/sqLgm':>10}{'C=M/(sqn g2q)':>14}{'mxlNq/logm':>11}")
for mu in [2,3,4,5,6]:
    beta=4.0
    n,p=find_prime(mu,beta)
    h,H=subgroup(p,n)
    w=2*math.pi/p
    m=(p-1)//n
    def Xb(b): return sum(cmath.exp(1j*w*((b*x)%p)) for x in H)
    reps=orbit_reps(p,n,h)
    # full sup if feasible; else stride sample of reps
    if len(reps)>200000:
        stride=len(reps)//200000; rsM=reps[::stride]
    else:
        rsM=reps
    Mvals={b:abs(Xb(b)) for b in rsM}
    M=max(Mvals.values())
    floor=math.sqrt(n*math.log(p/n))
    logm=math.log(m); logp=math.log(p)
    Hset=H
    def d2(c):
        s=0.0
        for x in Hset: s+=1-math.cos(w*((c*x)%p))
        return 2.0*s/n
    base=max(Mvals,key=lambda b:Mvals[b])
    baseorbit=[(base*hp)%p for hp in H]
    def dq_to_base(bj):
        best=1e18
        for zb in baseorbit:
            v=d2((bj-zb)%p)
            if v<best: best=v
        return math.sqrt(max(best,0.0))
    if len(reps)>30000:
        stride=len(reps)//30000; rsamp=reps[::stride]; sf=len(reps)/len(rsamp)
    else:
        rsamp=reps; sf=1.0
    dists=[dq_to_base(bj) for bj in rsamp]
    diam=max(dists)
    g2q=0.0; mxlNq=0.0; K=18; prev=diam
    for k in range(K):
        eps=diam*(2**(-k))
        ball=sum(1 for r in dists if r<=eps)*sf+1
        Nq=max(m/ball,1.0); lN=math.log(Nq); mxlNq=max(mxlNq,lN)
        g2q+=(prev-eps)*math.sqrt(max(lN,0.0)); prev=eps
    sqLgm=math.sqrt(logm)
    print(f"{n:>4}{p:>11}{m:>9}  {M:>8.2f}{floor:>8.2f}{M/floor:>6.2f}"
          f"  {g2q:>6.2f}{g2q/sqLgm:>10.2f}{M/(math.sqrt(n)*g2q):>14.2f}{mxlNq/logm:>11.2f}")
print()
print("If C and g2q/sqLgm BOTH bounded as n grows => I031 gives M=O(sqrt(n log(p/n))),")
print("exponent 1/2, n-uniform constant. If C grows with n => deterministic-random gap (RISK).")
