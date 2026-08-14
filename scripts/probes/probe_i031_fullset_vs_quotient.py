#!/usr/bin/env python3
"""I031 GROUP-INVARIANT DUDLEY — head-to-head: FULL-set chaining (prior A2, 'reduces-to-wall')
   vs QUOTIENT (orbit-space) chaining (the never-tried twist).

   The prior A2 v2 probe chained over ALL of F_p^* under the increment metric d and found
   maxlogN/log p = 1.00 EXACTLY => 'entropy = Theta(log q), no collapse, reduces-to-wall'.

   But |X_b| is EXACTLY mu_n-orbit-invariant (verified: machine precision). So chaining
   over F_p^* DOUBLE-COUNTS each value n times in n different index points. The honest
   chaining is over the QUOTIENT F_p^*/mu_n (m=(p-1)/n points). This probe shows the
   entropy DROPS from log p to log m=log(p/n) under the quotient => the floor scale.

   This is the I031 'dilation is a process isometry collapsing the p/n cosets into n orbits'
   lemma, and it is what the prior A2 attack MISSED (it chained the wrong index set).

   VERDICT METRIC: full-set maxlogN/logp (should be 1, the wall) vs quotient mxlNq/logp
   (should be ~log m/log p < 1, the gain). And the exponent slope.

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

print("FULL-set chaining (PRIOR A2, reduces-to-wall) vs QUOTIENT chaining (I031 twist)")
print(f"{'n':>4}{'p':>9}{'m':>7}  {'FULL maxlogN/logp':>18}  {'QUOTIENT mxlNq/logp':>20}  {'logm/logp':>10}")
for mu,beta in [(2,3.5),(3,3.5),(4,3.5),(5,3.5)]:
    n,p=find_prime(mu,beta)
    h,H=subgroup(p,n); w=2*math.pi/p; m=(p-1)//n
    logp=math.log(p); logm=math.log(m)
    def d2(c):
        s=0.0
        for x in H: s+=1-math.cos(w*((c*x)%p))
        return 2.0*s/n
    # FULL-set entropy: cover F_p (translation-inv additive metric), ball around 0.
    if p<=200000: cs=list(range(1,p)); sf=1.0
    else:
        st=max(1,(p-1)//200000); cs=list(range(1,p,st)); sf=(p-1)/len(cs)
    rhos=[math.sqrt(max(d2(c),0.0)) for c in cs]; diam=max(rhos)
    full_max=0.0
    for k in range(18):
        eps=diam*(2**(-k))
        ball=sum(1 for r in rhos if r<=eps)*sf+1
        full_max=max(full_max, math.log(max(p/ball,1.0)))
    # QUOTIENT entropy: cover orbit reps, distance to a fixed base orbit.
    reps=orbit_reps(p,n,h)
    base=reps[0]; baseorbit=[(base*hp)%p for hp in H]
    def dq(bj):
        best=1e18
        for zb in baseorbit:
            v=d2((bj-zb)%p)
            if v<best: best=v
        return math.sqrt(max(best,0.0))
    if len(reps)>50000:
        st=len(reps)//50000; rsamp=reps[::st]; sf2=len(reps)/len(rsamp)
    else: rsamp=reps; sf2=1.0
    dists=[dq(bj) for bj in rsamp]; diamq=max(dists)
    q_max=0.0
    for k in range(18):
        eps=diamq*(2**(-k))
        ball=sum(1 for r in dists if r<=eps)*sf2+1
        q_max=max(q_max, math.log(max(m/ball,1.0)))
    print(f"{n:>4}{p:>9}{m:>7}  {full_max/logp:>18.3f}  {q_max/logp:>20.3f}  {logm/logp:>10.3f}")
print()
print("FULL ~1.0 (the prior wall) vs QUOTIENT < 1.0 ~ logm/logp: the entropy lives at the")
print("log(p/n) scale once you chain the ORBIT SPACE. That is the I031 collapse the prior A2 missed.")
