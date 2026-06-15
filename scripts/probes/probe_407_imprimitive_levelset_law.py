#!/usr/bin/env python3
"""
The PROVABLE inverse-LO bound for the imprimitive family r(x)=-x^j on mu_n.

CLEAN STATEMENT (provable, char-free, the Lean brick candidate):
For the ratio sequence r: mu_n -> F, r(x) = -x^j (the imprimitive monomial direction),
the ratioMult of EVERY value is exactly gcd(j,n) (on the values in the image) or 0.
Specifically: ratioMult(gamma) = gcd(j,n) if -gamma is a (j-th power) i.e. in (mu_n)^j,
else 0. And the number of nonzero-mult values = n/gcd(j,n).

This is the LEVEL-SET structure of the homomorphism x |-> x^j on the cyclic group mu_n.
The fibers of a group hom phi: mu_n -> mu_n, phi(x)=x^j, are cosets of ker(phi) = mu_{gcd(j,n)},
each of size gcd(j,n). Image = (mu_n)^j = mu_{n/gcd(j,n)}.

This is PURELY group theory (cyclic group, power map), char-free, Mathlib-provable.

INVERSE-LO INTERPRETATION: the ratio sequence r=-x^j has its mass CONCENTRATED on
n/gcd(j,n) values, each with multiplicity gcd(j,n). The inverse-LO bound:
  #{gamma : ratioMult(gamma) >= t} = n/gcd(j,n)  if t <= gcd(j,n), else 0.
So the high-multiplicity (>= t) level set has size EXACTLY n/gcd(j,n) (a sharp bound,
both directions). This is the cleanest possible inverse-LO statement.

Verify numerically:
"""
import itertools
from math import gcd
from collections import Counter

def setup(n,plo):
    p=plo
    def isp(x):
        if x<2:return False
        for d in range(2,int(x**0.5)+1):
            if x%d==0:return False
        return True
    while not(p%n==1 and isp(p)):p+=1
    for cand in range(2,p):
        if pow(cand,n,p)==1 and all(pow(cand,n//q,p)!=1 for q in (2,3,5,7) if n%q==0):
            return p,[pow(cand,i,p) for i in range(n)]

for n in [8,16,32,64]:
    p,mu=setup(n,n*10000+1)
    print(f"n={n} p={p}:")
    for j in range(1,n):
        d=gcd(j,n)
        # ratio r(x) = -x^j; multiplicity profile
        prof=Counter()
        for x in mu:
            prof[(-pow(x,j,p))%p]+=1
        mults=set(prof.values())
        nvals=len(prof)
        # check: all mults == d, nvals == n/d
        ok = (mults=={d} and nvals==n//d)
        if j in (1,2,n//4,n//2,n-1):
            print(f"  j={j:3d} gcd={d:3d}: #vals={nvals:3d}(=n/gcd={n//d}) all-mult-{d}? {ok}")
    # spot any failure
    fail=False
    for j in range(1,n):
        d=gcd(j,n);prof=Counter()
        for x in mu: prof[(-pow(x,j,p))%p]+=1
        if set(prof.values())!={d} or len(prof)!=n//d: fail=True
    print(f"  -> ALL j (1..{n-1}) match level-set law (mult=gcd, #vals=n/gcd)? {not fail}")
