#!/usr/bin/env python3
"""
Door-(iv) Lane 1 sweep 3 — is there SLACK between the worst |eta_b| and the second-moment
(L2/Plancherel) prediction, where a non-moment door-(iv) method could live?

Both prior refutations (758205014 window-spread energy-blind, 592490748 worst-b ~5sigma spike =
moment-equivalent) concluded the cancellation routes through the SECOND MOMENT of {|eta_b|}. The
decisive remaining question: does the actual sup M = max_b |eta_b| SATURATE its second-moment
ceiling, or is there a measurable GAP?

Second-moment facts (over the (p-1)/n nonzero coset frequencies b):
  - Plancherel: sum over ALL p frequencies of |eta_b|^2 = p * n  (eta_0 = n; the rest carry p*n - n^2).
    Over the n-1 ... actually over nonprincipal b, sum |eta_b|^2 = n*(p - n) (exact), so the
    AVERAGE |eta_b|^2 over nonzero b = n*(p-n)/(p-1) -> n. Hence the L2/Plancherel FLOOR is
    M >= sqrt(mean) ~ sqrt(n) and the trivial 2nd-moment CEILING from a single moment is only ~sqrt(n*?).
  The prize wants M <= C*sqrt(n*log(p/n)); SOTA n^0.989. The OPEN gap is between sqrt(n) (Plancherel
  floor) and the actual sup, which empirically sits at M ~ (2-4)*sqrt(n) with a log-type growth.

Measure, in the prize regime (proper mu_n, p>>n^3, never n=q-1):
  - M = max_b |eta_b|,  rmsM = sqrt(mean_b |eta_b|^2)  (the exact 2nd-moment scale)
  - ratio M / rmsM            (how far the sup exceeds the L2 scale; the "log overshoot")
  - check M/rmsM vs sqrt(log(p/n))  (does the overshoot track the prize log factor? = door-iii EVT)
  - 4th-moment ratio: mean|eta|^4 / (mean|eta|^2)^2  (kurtosis; Gaussian=2 for complex, larger=>heavy tail)
EXACT complex arithmetic.
"""
import cmath, math

def is_prime(n):
    if n<2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n%q==0: return n==q
    d=n-1; r=0
    while d%2==0: d//=2; r+=1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x=pow(a,d,n)
        if x in (1,n-1): continue
        for _ in range(r-1):
            x=x*x%n
            if x==n-1: break
        else: return False
    return True

def find_prime(n,beta):
    t=int(round(n**beta)); k0=max(2,t//n)
    for dk in range(0,400000):
        for k in (k0+dk,k0-dk):
            if k<2: continue
            p=k*n+1
            if p>n and is_prime(p): return p
    return None

def subgroup(p,n):
    pm1=p-1; f={}; m=pm1; d=2
    while d*d<=m:
        while m%d==0: f[d]=1; m//=d
        d+=1
    if m>1: f[m]=1
    def isg(g): return all(pow(g,pm1//q,p)!=1 for q in f)
    g=2
    while not isg(g): g+=1
    h=pow(g,pm1//n,p); mu=[]; c=1
    for _ in range(n): mu.append(c); c=c*h%p
    return mu,g

def eta(b,mu,p):
    return abs(sum(cmath.exp(2j*math.pi*((b*y)%p)/p) for y in mu))

def main():
    print("=== sup |eta_b| vs second-moment scale: where is the slack? ===")
    print(f"{'n':>4} {'p':>11} {'M':>8} {'M/sqn':>6} {'rmsM':>7} {'rmsM/sqn':>8} "
          f"{'M/rmsM':>7} {'sqrt(log)':>9} {'(M/rms)/sqlog':>13} {'kurt':>6}")
    for n,beta in [(16,4.0),(32,4.0),(64,4.0),(128,4.0),(16,4.5),(32,4.5),(64,4.5)]:
        p=find_prime(n,beta)
        if p is None: continue
        mu,g=subgroup(p,n)
        ncos=(p-1)//n
        # over coset reps b = g^j (the distinct nonzero frequency classes)
        cur=1; s2=0.0; s4=0.0; M=0.0
        cap=min(ncos, 60000)
        for j in range(cap):
            v=eta(cur,mu,p); v2=v*v
            s2+=v2; s4+=v2*v2
            if v>M: M=v
            cur=cur*g%p
        mean2=s2/cap; mean4=s4/cap
        rms=math.sqrt(mean2); sqn=math.sqrt(n)
        logf=math.log(p/n); sqlog=math.sqrt(logf)
        kurt=mean4/(mean2*mean2)
        print(f"{n:>4} {p:>11} {M:>8.3f} {M/sqn:>6.2f} {rms:>7.3f} {rms/sqn:>8.3f} "
              f"{M/rms:>7.3f} {sqlog:>9.3f} {(M/rms)/sqlog:>13.3f} {kurt:>6.3f}")

if __name__=="__main__":
    main()
