#!/usr/bin/env python3
"""THE 2-ADIC OBSTRUCTION (final, rigorous). Exponential coset-union supply C(n/d,t/d)
requires d CONSTANT (so n/d grows). At production rate rho (k = rho*n = 2^a a power of 2):
  firing needs d=2^j | t=(k+m+1), d>=m+2.
  For d constant => m constant => need 2^j | (2^a + m+1) with 2^j>=m+2.
  For a>j: 2^a = 0 mod 2^j, so need 2^j | (m+1) AND 2^j >= m+2 => m+1 >= 2^j >= m+2: IMPOSSIBLE.
So at production rates, every firing has d NOT constant (d grows with n), giving
C(n/d, t/d)=C(O(1),O(1))=constant. TEST: track best supply rate at FIXED rho as n grows.
Genuine exponential <=> rate bounded below; vacuous/poly <=> rate -> 0."""
from math import comb, log2
def best_rate(n, k):
    best=0
    for t in range(k+1, n+1):
        m=t-k-1
        # largest power-of-2 divisor of t that also divides n and is >= m+2
        d=1
        while d*2<=t and t%(d*2)==0 and (d*2)<=n and n%(d*2)==0: d*=2
        # also consider all 2^j | gcd-ish; simplest: take the maximal 2^j | t with 2^j<=n
        dd=1
        while (dd*2)<=t and t%(dd*2)==0: dd*=2
        # need dd | n too (auto if n=2^mu) and dd>=m+2
        if dd>=m+2 and n%dd==0:
            s=t//dd; Nc=n//dd
            if s<=Nc: best=max(best, comb(Nc,s))
    return log2(best)/n if best>0 else 0.0

print("FIXED production rho: does best supply rate stay bounded (exp) or -> 0 (poly) as n grows?")
for name,num,den in [("1/2",1,2),("1/4",1,4),("1/8",1,8),("1/16",1,16)]:
    rates=[]
    for mu in range(5,15):
        n=1<<mu; k=n*num//den
        if k<1: continue
        rates.append((mu, best_rate(n,k)))
    trend=" ".join(f"{r:.4f}" for _,r in rates)
    verdict = "-> 0 (POLYNOMIAL, pin safe)" if rates[-1][1] < rates[0][1] and rates[-1][1] < 0.01 else "BOUNDED? check"
    print(f"  rho={name}: rates(mu=5..14) = {trend}   {verdict}")

print("\nContrast — NON-production low rate where the construction IS exponential:")
for k in [5, 9, 13]:
    rates=[]
    for mu in range(5,15):
        n=1<<mu
        if k>=n: continue
        rates.append(best_rate(n,k))
    print(f"  fixed k={k} (rho->0): rates = {' '.join(f'{r:.3f}' for r in rates)}  (note: rho={k}/2^mu shrinks)")

# the airtight symbolic check of the obstruction at production k=2^a:
print("\nSYMBOLIC: at k=2^a, is there ANY constant d=2^j>=m+2 (m constant) dividing k+m+1?")
import itertools
bad=0
for a in range(3, 20):
    k=1<<a
    for m in range(0, 64):       # constant band offsets
        t=k+m+1
        found=[1<<j for j in range(1,a+2) if (1<<j)>=m+2 and t%(1<<j)==0]
        if found: bad+=1; 
    # report only if any constant-d firing exists with d small (<=64, i.e. truly constant)
print(f"  constant-d (d<=64) firings at production k=2^a (a=3..19, m=0..63): {bad}",
      "=> NONE: exponential regime unreachable at production" if bad==0 else "=> some exist, inspect")
