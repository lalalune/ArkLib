#!/usr/bin/env python3
"""I031 THE RISK: deterministic M vs the RANDOM sub-Gaussian model on the SAME metric.

Dudley/Talagrand bound E sup_b Y_b <= C gamma_2(T,d) holds for a RANDOM sub-Gaussian
process Y_b with increment metric d. Our X_b is DETERMINISTIC. I031 needs the transfer
(deterministic = random, the RISK). Test it directly:

Build the canonical RANDOM Gaussian process G_b on the quotient with the SAME covariance
structure as X_b (i.e. G_b = Re sum_x g_x e_p(b x), g_x iid complex Gaussian), measure
E sup_b |G_b| over orbit reps, and compare to the deterministic M = max_b |X_b|.

If E sup|G| ~ M (ratio ~ const) => the deterministic worst-case is tracked by the random
chaining => I031's transfer is empirically VALID => real handle on the EXPONENT.
If M >> E sup|G| (gap grows) => deterministic worst-case escapes the random model => RISK
bites => promising-partial (chaining bounds the random proxy, not M itself).

PROPER REGIME: p prime, n=2^mu, n|p-1, p>>n^3.
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

random.seed(42)
print("DETERMINISTIC M  vs  RANDOM-model E sup|G| (same Gauss-period covariance), on orbit reps")
print(f"{'n':>4}{'beta':>5}{'p':>9}{'m':>7}  {'det M':>7}{'rand EsupG':>11}{'M/rand':>8}{'floor':>7}{'rand/fl':>8}")
for mu,beta in [(2,4.0),(3,4.0),(4,4.0),(5,3.5)]:
    n,p=find_prime(mu,beta)
    h,H=subgroup(p,n); w=2*math.pi/p; m=(p-1)//n
    reps=orbit_reps(p,n,h)
    if len(reps)>20000:
        st=len(reps)//20000; reps=reps[::st]
    # deterministic M
    def Xb(b): return sum(cmath.exp(1j*w*((b*x)%p)) for x in H)
    M=max(abs(Xb(b)) for b in reps)
    # random model: G_b = sum_x g_x exp(i w b x), g_x iid standard complex normal.
    # E sup_b |G_b|: average over trials of max over reps. Each row vector e_p(b x).
    phases=[[cmath.exp(1j*w*((b*x)%p)) for x in H] for b in reps]
    T=30
    acc=0.0
    for _ in range(T):
        g=[complex(random.gauss(0,1)/math.sqrt(2), random.gauss(0,1)/math.sqrt(2)) for _ in H]
        mx=0.0
        for row in phases:
            v=abs(sum(row[i]*g[i] for i in range(n)))
            if v>mx: mx=v
        acc+=mx
    EsupG=acc/T
    floor=math.sqrt(n*math.log(p/n))
    print(f"{n:>4}{beta:>5.1f}{p:>9}{m:>7}  {M:>7.2f}{EsupG:>11.2f}{M/EsupG:>8.2f}{floor:>7.2f}{EsupG/floor:>8.2f}")
print()
print("M/rand ~ const => deterministic worst-case TRACKED by random chaining (transfer valid).")
print("M/rand GROWS => deterministic escapes the random model (the RISK bites).")
print("rand/floor: the random model already obeys the floor by Dudley (E sup G <= C sqrt(n log m)).")
