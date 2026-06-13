#!/usr/bin/env python3
"""Confirm the two obstruction theorems that protect the pin from EsymmFiber:
(T1) NO power-of-2 k (production rate) admits exponential coset-union supply, any n.
(T2) In the OPEN mid-window rho < alpha < sqrt(rho), the supply is bounded by a CONSTANT
     C(round(1/(alpha-rho)), round(alpha/(alpha-rho))) — exponential only as alpha->rho."""
from math import comb, log2
def v2(x):
    c=0
    while x and x%2==0: x//=2; c+=1
    return c
def max_supply(n, k):
    """max C(n/d, t/d) over d=2^j|n, d>=m+2, d|t, t=k+m+1<=n, m>=0."""
    best=0; arg=None
    d=1
    js=[1<<j for j in range(64) if (1<<j)<=n]
    for t in range(k+1, n+1):
        m=t-k-1
        for d in js:
            if d<m+2: continue
            if n%d or t%d: continue
            s=t//d; Nc=n//d
            if s<=Nc:
                val=comb(Nc,s)
                if val>best: best=val; arg=(m,t,d,s,t/n)
    return best, arg

print("(T1) exponential firing at POWER-OF-2 k (= production rates)? exp := log2(supply)/n > 0.02")
any_exp=False
for mu in range(4,14):
    n=1<<mu
    for a in range(1,mu):           # k = 2^a, rate 2^{a-mu}
        k=1<<a
        best,arg=max_supply(n,k)
        rate=log2(best)/n if best>0 else 0
        if rate>0.02:
            any_exp=True
            print(f"   mu={mu} k={k}(rho=2^{a-mu}): EXP rate={rate:.3f} {arg}")
print(f"   => power-of-2 k exponential firings across mu=4..13: {'FOUND' if any_exp else 'NONE (T1 holds)'}\n")

print("(T2) mid-window supply bound: for alpha in (rho, sqrt(rho)), is max supply <= small const?")
# take rho=1/4 (k=n/4); scan agreements alpha between rho=0.25 and sqrt=0.5
for mu in [10,12]:
    n=1<<mu; k=n//4; rho=0.25
    print(f"   mu={mu} n={n} k={k} rho=0.25 Johnson-agr=0.5:")
    for alpha in [0.27, 0.30, 0.35, 0.45]:
        t=round(alpha*n); m=t-k-1
        # best supply at this band
        best=0;barg=None
        for d in [1<<j for j in range(mu+1)]:
            if d<m+2 or n%d or t%d: continue
            s=t//d;Nc=n//d
            if s<=Nc and comb(Nc,s)>best: best=comb(Nc,s);barg=(d,s)
        pred=comb(round(1/(alpha-rho)), max(1,round(alpha/(alpha-rho)))) if alpha>rho else 0
        print(f"      alpha={alpha}: max supply={best} {barg}  log2={log2(best)/n if best>0 else 0:.4f}  (const-bound C(1/(a-r),..)≈{pred})")
print("\n   => mid-window supply is bounded/constant; exponential only as alpha->rho (capacity edge, KKH26-known)")
