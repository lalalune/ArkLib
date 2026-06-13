import math, random
from collections import Counter
# FAITHFUL e-symm fiber at PRODUCTION-SCALE prime (no small-prime pigeonhole saturation).
# p = 2013265921 = 15*2^27+1 (BabyBear); 32 | p-1 so mu_32 exists. C(32,18)=4.8e8 << p^2=4e18,
# so targets are NOT saturated => faithful counts. Compute via the matching trick:
# union e-vector (M=2): E1=e1A+e1B, E2=e2A+e1A*e1B+e2B. For a TARGET (T1,T2), for each
# (e1A,e2A) at size a the matching B-vector is e1B=T1-e1A, e2B=T2-e2A-e1A*e1B at size b=t-a.
# Look up in PB[b] dict -> O(2^n/2) per target. Cheap; faithful.
p = 2013265921
def mu(n):
    g=next(c for c in range(2,p) if pow(c,n,p)==1 and all(pow(c,n//q,p)!=1 for q in [2]))
    return [pow(g,i,p) for i in range(n)]
def parts(side,M):
    cur=[Counter() for _ in range(len(side)+1)]; cur[0][tuple([0]*M)]=1
    for x in side:
        nxt=[Counter() for _ in range(len(side)+1)]
        for sz in range(len(side)+1):
            for e_,c in cur[sz].items():
                nxt[sz][e_]+=c
                ne=list(e_)
                for j in range(M-1,-1,-1): ne[j]=(e_[j]+x*(e_[j-1] if j>=1 else 1))%p
                nxt[sz+1][tuple(ne)]+=c
        cur=nxt
    return cur
def fiber_at(PA,PB,t,half,target):
    """count t-subsets (union of A-subset + B-subset) with union e-vector == target (M=2)."""
    T1,T2=target; tot=0
    for a in range(0,min(t,half)+1):
        b=t-a
        if b<0 or b>half: continue
        for (e1A,e2A),cA in PA[a].items():
            e1B=(T1-e1A)%p
            e2B=(T2-e2A-e1A*e1B)%p
            cB=PB[b].get((e1B,e2B),0)
            if cB: tot+=cA*cB
    return tot
def run(n,k,m):
    dom=mu(n); t=k+m+1; M=m+1; half=n//2
    PA=parts(dom[:half],M); PB=parts(dom[half:],M)
    # zero target (structured: e_1=e_2=0)
    zfib=fiber_at(PA,PB,t,half,(0,0))
    # sample random targets to estimate the max (each cheap)
    random.seed(7); mx=zfib; argmax="zero"
    for _ in range(300):
        T=(random.randrange(p),random.randrange(p))
        f=fiber_at(PA,PB,t,half,T)
        if f>mx: mx=f; argmax=str(T)
    return zfib,mx,argmax,t
for nm,nu,de in [("1/2",1,2),("1/4",1,4)]:
    for n in [16,32]:
        k=n*nu//de
        zf,mx,arg,t=run(n,k,1)
        print(f"rho={nm} n={n} k={k} m=1 t={t}: FAITHFUL zero-target-fiber={zf} (log2/n={math.log2(zf)/n if zf else 0:.4f}) "
              f"max-over-sample={mx} argmax={arg}",flush=True)
