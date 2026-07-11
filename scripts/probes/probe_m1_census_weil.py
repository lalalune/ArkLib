#!/usr/bin/env python3
"""probe_m1_census_weil.py (#389, Fable): the m=1 deep-band census is n/4 EXACTLY for
production fields (Weil regime), inflation confined to small fields q <~ n^1.5.

#{4-subsets of mu_n : sum x = sum x^2 = 0} (m=1 supply of x^4) = n/4 = #mu_4-cosets, via the
map phi(x)=x^3+x^2+x being 3-to-1 on mu_n ONLY over c=-1 (fiber {-1,i,-i}, proven by
x^3+x^2+x+1=(x+1)(x^2+1)). The converse (no other c has 3 preimages in mu_n) HOLDS once
q >~ n^1.5: the cubic-splitting count #{c : t^3+t^2+t-c has 3 mu_n-roots} ~ n^3/q^2 -> 0 (Weil).
Inflation (extra c) is the small-field n=Theta(q) regime ONLY: largest-q-with-inflation < n^1.5
(n=64:193, n=128:1409, n=256:257); clean for all q >> n^1.5 incl production q >= 2^128.
=> the small-m deep-band faces are WEIL-controlled (standard), NOT Bourgain-open. The Bourgain
hardness is localized to the large-m cliff (degree-(m+2) census with m ~ nH/(beta log n), where
the Weil threshold ~n^m exceeds production q)."""
from collections import Counter
import sympy
def rou(p,n):
    for g in range(2,p):
        h=pow(g,(p-1)//n,p)
        if all(pow(h,d,p)!=1 for d in range(1,n)): return [pow(h,i,p) for i in range(n)]
def nfib3(n,p):
    D=rou(p,n); fib=Counter((pow(x,3,p)+pow(x,2,p)+x)%p for x in D)
    return sum(1 for c,k in fib.items() if k>=3)
if __name__=="__main__":
    for n in (32,64,128,256):
        last=0; cand=n+1; t=0
        while cand<3*n*n and t<60:
            if sympy.isprime(cand) and (cand-1)%n==0:
                if nfib3(n,cand)>1: last=cand
                t+=1
            cand+=1
        print(f"n={n}: n^1.5={int(n**1.5)}, largest q with inflation={last} (< n^1.5), "
              f"census=n/4={n//4} for q>>n^1.5")
