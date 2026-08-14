#!/usr/bin/env python3
"""I031 GROUP-INVARIANT DUDLEY CHAINING — the quotient version the prior A2 probe missed.

KEY FACT (verified): |X_b| is EXACTLY constant on dilation orbits b ~ zeta*b (zeta in mu_n).
So  M = max_{b!=0}|X_b| = max over the m=(p-1)/n ORBIT REPRESENTATIVES.

I031's NEW LEMMA: chain the process on the QUOTIENT index set T/mu_n (m points), under the
INDUCED metric d_q(orbit_b, orbit_b') = min over the orbit of d(b,b'). Then the entropy
integral telescopes: log N(T/mu_n, d_q, eps) <= log m = log(p/n), NOT log p.
Prediction: gamma_2 on the quotient = Theta(sqrt(log(p/n))) => M <= C sqrt(n log(p/n)) = FLOOR.

DECISIVE TESTS:
 (1) Quotient entropy: max_eps log N(quotient) / log(p/n). If ~1 => the quotient carries the
     FULL log(p/n) and the floor IS the quotient entropy integral (telescoping CONFIRMED).
     If the quotient entropy is STILL ~log p (i.e. min-over-orbit doesn't shrink the metric
     balls) => collapse FAILS, the multiplicative orbit and additive metric are misaligned.
 (2) Chaining tightness on the quotient: M / (sqrt(n) * gamma_2_quotient).
 (3) THE RISK (deterministic-vs-random RIP gap): does the DETERMINISTIC sup equal the
     sub-Gaussian chaining prediction, or is there a gap? Compare M to sqrt(n)*gamma_2_quotient.

PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3, proper 2-power subgroup, NEVER n=p-1.
"""
import cmath, math, random

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
    """One representative per dilation orbit (smallest element of each orbit)."""
    seen=[False]*p
    reps=[]
    for b in range(1,p):
        if seen[b]: continue
        # build orbit
        orb=set()
        x=b
        for _ in range(n):
            orb.add(x); x=(x*h)%p
        for y in orb: seen[y]=True
        reps.append(min(orb))
    return reps

print("I031 QUOTIENT (orbit-space) CHAINING — telescoping test")
print(f"{'n':>4}{'p':>9}{'m':>7}  {'M':>7}{'floor':>7}{'M/fl':>6}"
      f"  {'#reps':>6}  {'g2q':>6}{'sqLgm':>7}{'sqn*g2q':>8}{'M/(sqn g2q)':>12}"
      f"  {'mxlNq':>7}{'logm':>6}{'mxlNq/logm':>11}{'/logp':>7}")
for mu,beta in [(2,3.2),(3,3.2),(4,3.2),(5,3.2)]:
    n,p=find_prime(mu,beta)
    h,H=subgroup(p,n)
    w=2*math.pi/p
    m=(p-1)//n
    def Xb(b): return sum(cmath.exp(1j*w*((b*x)%p)) for x in H)
    reps=orbit_reps(p,n,h)
    assert len(reps)==m, (len(reps),m)
    Mvals={b:abs(Xb(b)) for b in reps}
    M=max(Mvals.values())
    floor=math.sqrt(n*math.log(p/n))
    logm=math.log(m); logp=math.log(p)
    # Quotient metric: d_q(orbit_b, orbit_b') = min_{zeta in mu_n} d(b, zeta b').
    # d(b,b')^2 = (2/n) sum_x (1 - cos(w (b-b') x)).  Translation-inv on F_p (additive),
    # BUT the quotient is by MULTIPLICATIVE mu_n, so we compute the induced quotient metric
    # explicitly: distance between two orbits = min over the n*n cross pairs (cheap: n small,
    # but orbit of b' under mu_n is n points; min over those).
    Hset=H
    def d2(c):  # c = difference
        s=0.0
        for x in Hset: s+=1-math.cos(w*((c*x)%p))
        return 2.0*s/n
    # For quotient covering: pick a base rep b0, compute d_q(orbit_b0, orbit_bj) for all reps bj.
    # We approximate the quotient covering number by: for each rep, min distance to base orbit;
    # then count eps-balls in the quotient.  Use ONE fixed base (orbit of rep with max |X|).
    base=max(reps,key=lambda b:Mvals[b])
    baseorbit=[ (base*hp)%p for hp in H ]  # all dilates of base
    # quotient distance from orbit(bj) to orbit(base): min over dilates of bj of d(bj_dilate, base)
    # = min over zeta1,zeta2 of d(zeta1 bj, zeta2 base) = min over zeta of d(bj, zeta base) by translation? 
    # NO - d is additive-translation-inv in the DIFFERENCE, and difference zeta1 bj - zeta2 base.
    # min over zeta1,zeta2 in mu_n. Use min over the n dilates of base (fix bj):
    def dq_to_base(bj):
        best=1e9
        for zb in baseorbit:
            c=(bj-zb)%p
            best=min(best, d2(c))
        return math.sqrt(max(best,0.0))
    dists=[dq_to_base(bj) for bj in reps]
    diam=max(dists) if dists else 0.0
    # Dudley over quotient
    g2q=0.0; mxlNq=0.0; K=16; prev=diam
    for k in range(K):
        eps=diam*(2**(-k))
        ball=sum(1 for r in dists if r<=eps)+1
        Nq=max(m/ball,1.0)
        lN=math.log(Nq); mxlNq=max(mxlNq,lN)
        g2q+=(prev-eps)*math.sqrt(max(lN,0.0)); prev=eps
    sqLgm=math.sqrt(logm)
    print(f"{n:>4}{p:>9}{m:>7}  {M:>7.2f}{floor:>7.2f}{M/floor:>6.2f}"
          f"  {len(reps):>6}  {g2q:>6.2f}{sqLgm:>7.2f}{math.sqrt(n)*g2q:>8.2f}{M/(math.sqrt(n)*g2q):>12.2f}"
          f"  {mxlNq:>7.2f}{logm:>6.2f}{mxlNq/logm:>11.2f}{mxlNq/logp:>7.2f}")
print()
print("READING:")
print(" mxlNq/logm ~ 1 => quotient entropy = log m = log(p/n) (telescoping to the RIGHT scale).")
print(" mxlNq/logp < 1 and shrinking => collapse from log p to log m CONFIRMED (the I031 gain).")
print(" M/(sqn g2q) ~ const => floor IS the quotient entropy integral (deterministic=random, no gap).")
