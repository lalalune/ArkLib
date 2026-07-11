#!/usr/bin/env python3
"""
TOOL 2 FINAL: does the strongest prize-period dilation correlation DECAY toward the random
null as m grows (=> DIFFUSE, same wall) or stay >> random (=> exploitable structure)?

For each (n, p) measure:
  Darith = max_lambda |sum_t eta_t conj(eta_{lambda t})| / sum|eta_t|^2
  Drand  = same statistic for a RANDOM-THIN null (m i.i.d. sums of n random unit phases),
           averaged over trials -> the noise level of 'max over O(m) dilations of a length-m
           correlation' (extreme value ~ sqrt(log m / m)).
If Darith ~ Drand (within trial spread), the arithmetic dilation structure is INDISTINGUISHABLE
from noise = DIFFUSE. If Darith >> Drand persistently, it's exploitable.
"""
import math, cmath, random

def is_prime(m):
    if m<2: return False
    i=2
    while i*i<=m:
        if m%i==0: return False
        i+=1
    return True

def find_prime_cong1(n, lo):
    p=lo+(1-lo)%n
    while True:
        if p>2 and p%n==1 and is_prime(p): return p
        p+=n

def primitive_root(p):
    phi=p-1; factors=set(); nn=phi; d=2
    while d*d<=nn:
        if nn%d==0:
            factors.add(d)
            while nn%d==0: nn//=d
        d+=1
    if nn>1: factors.add(nn)
    for g in range(2,p):
        if all(pow(g,phi//f,p)!=1 for f in factors): return g

def max_dilation_corr_vals(et, m):
    denom = sum(abs(v)**2 for v in et)
    best = 0.0
    for lam in range(2, m):
        if math.gcd(lam,m)!=1: continue
        s = sum(et[t]*et[(lam*t)%m].conjugate() for t in range(m))
        v = abs(s)/denom
        if v>best: best=v
    return best

def arith_dilation(p, n):
    g=primitive_root(p)
    H=[pow(pow(g,(p-1)//n,p),i,p) for i in range(n)]
    eta={b: sum(cmath.exp(2j*math.pi*(b*x%p)/p) for x in H) for b in range(1,p)}
    m=(p-1)//n
    et=[eta[pow(g,t,p)] for t in range(m)]
    return max_dilation_corr_vals(et, m)

def rand_dilation(m, n, trials, seed=0):
    rng=random.Random(seed)
    vals=[]
    for _ in range(trials):
        et=[sum(cmath.exp(2j*math.pi*rng.random()) for _ in range(n)) for _ in range(m)]
        vals.append(max_dilation_corr_vals(et, m))
    return sum(vals)/len(vals), min(vals), max(vals)

if __name__=='__main__':
    print("Strongest dilation correlation: arithmetic vs random-thin null (DIFFUSE test)")
    print(f"{'n':>3} {'p':>8} {'m':>6} {'Darith':>8} {'Drand_mean':>10} {'[Drand min,max]':>18} "
          f"{'arith/randmean':>14} {'noise 1/sqrt m':>14}")
    for n in [8]:
        for lo in [503, 2003, 8009, 30011, 100003]:
            p=find_prime_cong1(n, lo)
            m=(p-1)//n
            if m>2600: continue   # keep the O(m^2) dilation scan tractable
            Da=arith_dilation(p, n)
            tr = 30 if m<400 else (12 if m<1200 else 6)
            Dr, Drmin, Drmax = rand_dilation(m, n, tr)
            print(f"{n:>3} {p:>8} {m:>6} {Da:>8.4f} {Dr:>10.4f} [{Drmin:.4f},{Drmax:.4f}]   "
                  f"{Da/Dr:>14.3f} {1/math.sqrt(m):>14.4f}")
    print("VERDICT: if arith/randmean ~ 1 and decreasing toward 1/sqrt(m), the dilation structure")
    print("is statistically the SAME as random thin sums = DIFFUSE = same BGK wall.")
