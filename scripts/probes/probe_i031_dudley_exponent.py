#!/usr/bin/env python3
"""I031 EXPONENT vs CONSTANT adjudication — the honest verdict.

The product M/floor grows 1.07->1.36 (n=4..64). Is this:
 (a) the EXPONENT failing (g2q grows like (log m)^{1/2+c}, c>0) => no-gain, or
 (b) just the CONSTANT (g2q = C_n sqrt(log m) with C_n bounded but slowly increasing,
     and diam grows) => exponent 1/2 SAFE but constant not pinned.

DECISIVE: regress log(g2q) on log(log m) at FIXED n across betas. If slope ~ 1/2,
exponent is 1/2 (handle real on exponent). If slope > 1/2, telescoping fails.

ALSO regress log(M) on log(log m) at fixed n: the TRUE sup exponent in log(p/n).
The floor claims slope 1/2. SOTA BGK gives M ~ n^{1-o(1)} which in fixed-n is just a
constant (no log dependence) => the log(p/n) dependence is the NEW content the floor adds.

PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3.
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
def find_prime_at(mu, target_p):
    n=1<<mu; t=((target_p//n)+1)*n+1
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

# FIX n=8, many betas => regress slope of log(M) and log(g2q) vs log(log m).
mu=3; n=1<<mu
pts=[]
for tp in [400, 1500, 6000, 25000, 100000, 400000, 1500000]:
    nn,p=find_prime_at(mu,tp)
    h,H=subgroup(p,n)
    w=2*math.pi/p; m=(p-1)//n
    def Xb(b): return sum(cmath.exp(1j*w*((b*x)%p)) for x in H)
    reps=orbit_reps(p,n,h)
    if len(reps)>150000:
        stride=len(reps)//150000; rsM=reps[::stride]
    else: rsM=reps
    Mvals={b:abs(Xb(b)) for b in rsM}
    M=max(Mvals.values())
    logm=math.log(m)
    def d2(c):
        s=0.0
        for x in H: s+=1-math.cos(w*((c*x)%p))
        return 2.0*s/n
    base=max(Mvals,key=lambda b:Mvals[b]); baseorbit=[(base*hp)%p for hp in H]
    def dq(bj):
        best=1e18
        for zb in baseorbit:
            v=d2((bj-zb)%p)
            if v<best: best=v
        return math.sqrt(max(best,0.0))
    if len(reps)>30000:
        stride=len(reps)//30000; rsamp=reps[::stride]; sf=len(reps)/len(rsamp)
    else: rsamp=reps; sf=1.0
    dists=[dq(bj) for bj in rsamp]; diam=max(dists)
    g2q=0.0; prev=diam
    for k in range(18):
        eps=diam*(2**(-k))
        ball=sum(1 for r in dists if r<=eps)*sf+1
        Nq=max(m/ball,1.0)
        g2q+=(prev-eps)*math.sqrt(max(math.log(Nq),0.0)); prev=eps
    pts.append((logm, M, g2q))
    print(f"n={n} p={p:>9} m={m:>8} logm={logm:6.3f}  M={M:6.2f}  g2q={g2q:5.2f}")

def slope(xs, ys):
    lx=[math.log(x) for x in xs]; ly=[math.log(y) for y in ys]
    nx=len(lx); mx=sum(lx)/nx; my=sum(ly)/nx
    num=sum((a-mx)*(b-my) for a,b in zip(lx,ly)); den=sum((a-mx)**2 for a in lx)
    return num/den
print()
print(f"slope log(M)   vs log(log m) = {slope([x for x,_,_ in pts],[y for _,y,_ in pts]):.3f}  (floor predicts 0.5)")
print(f"slope log(g2q) vs log(log m) = {slope([x for x,_,_ in pts],[g for _,_,g in pts]):.3f}  (telescoping predicts 0.5)")
print("If both ~0.5 => the log(p/n) dependence has exponent 1/2 = the FLOOR exponent (handle real on exponent).")
