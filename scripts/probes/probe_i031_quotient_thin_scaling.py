#!/usr/bin/env python3
"""I031 DECISIVE: does quotient-chaining gamma_2 PROVABLY scale as O(sqrt(log m))
   uniformly, as p/n -> infinity (the THIN prize regime), with M tracked to a const?

   FIX n, GROW beta (=> grow m=p/n). The floor sqrt(n log(p/n)) grows like sqrt(log m).
   If gamma_2_quotient / sqrt(log m) stays BOUNDED and M/(sqrt(n) g2q) stays ~const,
   then I031 gives a GENUINE handle: M = O(sqrt(n log(p/n))) with explicit constant,
   matching the floor EXPONENT 1/2 (not 1-o(1)).
   If gamma_2_q/sqrt(log m) GROWS, the telescoping is loose and it's no-gain.

   THE CRUX vs the prior A2 'reduces-to-wall': the prior chained the FULL F_p* (entropy
   log p, the additive metric blind to mult orbits). Chaining the QUOTIENT F_p*/mu_n is
   the never-tried twist. Test if the gain survives thinning.

   PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3, proper subgroup, NEVER n=p-1.
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

print("FIX n=8, GROW beta (thin the subgroup): does quotient gamma_2 ~ sqrt(log m)?")
print(f"{'n':>4}{'beta':>5}{'p':>11}{'m':>9}  {'M':>7}{'floor':>7}{'M/fl':>6}"
      f"  {'g2q':>6}{'sqLgm':>7}{'g2q/sqLgm':>10}{'M/(sqn g2q)':>12}  {'mxlNq/logm':>11}{'/logp':>7}")
for mu in [3]:
  for beta in [3.0, 3.5, 4.0, 4.5, 5.0]:
    n,p=find_prime(mu,beta)
    h,H=subgroup(p,n)
    w=2*math.pi/p
    m=(p-1)//n
    def Xb(b): return sum(cmath.exp(1j*w*((b*x)%p)) for x in H)
    reps=orbit_reps(p,n,h)
    Mvals={b:abs(Xb(b)) for b in reps}
    M=max(Mvals.values())
    floor=math.sqrt(n*math.log(p/n))
    logm=math.log(m); logp=math.log(p)
    Hset=H
    def d2(c):
        s=0.0
        for x in Hset: s+=1-math.cos(w*((c*x)%p))
        return 2.0*s/n
    base=max(reps,key=lambda b:Mvals[b])
    baseorbit=[(base*hp)%p for hp in H]
    def dq_to_base(bj):
        best=1e18
        for zb in baseorbit:
            c=(bj-zb)%p
            v=d2(c)
            if v<best: best=v
        return math.sqrt(max(best,0.0))
    # sample reps if too many (deterministic stride)
    if len(reps)>40000:
        stride=len(reps)//40000
        rsamp=reps[::stride]; sf=len(reps)/len(rsamp)
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
    print(f"{n:>4}{beta:>5.1f}{p:>11}{m:>9}  {M:>7.2f}{floor:>7.2f}{M/floor:>6.2f}"
          f"  {g2q:>6.2f}{sqLgm:>7.2f}{g2q/sqLgm:>10.2f}{M/(math.sqrt(n)*g2q):>12.2f}"
          f"  {mxlNq/logm:>11.2f}{mxlNq/logp:>7.2f}")
