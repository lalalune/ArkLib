#!/usr/bin/env python3
"""
Finiteness + exactness of the excess trigger (#389 Fable wf2).

CONFIRMED (probe 3): excess(mu_n)>0  <=>  p in PrimeFactors(set of forbidden
4-term cyclotomic norms).  This set is FINITE for each n.

Consequences to verify:
 (C1) For each fixed n, there are only FINITELY many "bad" primes p (excess>0);
      ALL sufficiently large p give E(mu_n) = 3n^2-3n EXACTLY -- even at p~n^2.
      => the char-0 minimal energy holds at the BOUNDARY too, for all but finitely
         many p. The "n^2 log n" boundary energy is the WORST case (Fermat-type p),
         NOT the typical case.
 (C2) The largest bad prime for n=2^m: how big? Is it the Fermat-number factor pattern?
      For n=16 we saw bad primes up to 337; note 17,97,113,193,257,337 = primes p|17! ..
      Let's see if largest bad prime = O(n^c) -- gives an EXPLICIT threshold p0(n)
      above which E is exactly minimal (boundary closure).
 (C3) Two-power special: are the bad primes exactly those with small mult. order of 2,
      or p ≡ 1 mod higher 2-power (subfield-of-Q(zeta) alignment)?
"""
import sympy
from sympy import isprime, primefactors, symbols, Poly, cyclotomic_poly, resultant
from collections import Counter
import itertools

X=symbols('X')
def w_of_order(p,n):
    g=sympy.primitive_root(p); return pow(g,(p-1)//n,p)
def mu_n_list(p,n):
    w=w_of_order(p,n); return [pow(w,i,p) for i in range(n)]
def excess(p,n):
    G=mu_n_list(p,n); cnt=Counter()
    for a in G:
        for b in G: cnt[(a+b)%p]+=1
    return sum(v*v for v in cnt.values())-(3*n*n-3*n)
def cyclo_norm(n, c):
    Phi=cyclotomic_poly(n,X)
    poly=Poly(sum(v*X**(e%n) for e,v in c.items()),X)
    return int(resultant(Poly(Phi,X),poly))

def forbidden_norm_primes(n):
    norms=set(); rng=range(n)
    for i,j,k,l in itertools.product(rng,repeat=4):
        if frozenset([i,j])==frozenset([k,l]): continue
        c=Counter(); c[i]+=1;c[j]+=1;c[k]-=1;c[l]-=1
        cc={e:v for e,v in c.items() if v!=0}
        if not cc: continue
        N=cyclo_norm(n,cc)
        if N!=0:
            for pf in primefactors(abs(N)): norms.add(pf)
    return sorted(p for p in norms if p>n)

print("="*78)
print("PROBE 4: finiteness & exact bad-prime set, n=2^m")
print(f"{'n':>4} {'#badprimes>n':>12} {'maxbad':>8} {'maxbad/n^2':>11} {'badprimes':>40}")
print("="*78)
import math
for m in (2,3,4,5):
    n=2**m
    bp=forbidden_norm_primes(n)
    # verify each is ACTUALLY bad (excess>0)
    verified=[]
    for p in bp:
        if (p-1)%n==0:
            try:
                if excess(p,n)>0: verified.append(p)
            except Exception: pass
    mb=max(bp) if bp else 0
    print(f"{n:>4} {len(bp):>12} {mb:>8} {mb/(n*n):>11.2f}   {bp[:12]}")
    # all primes p>maxbad with p≡1 mod n have excess 0?
    cnt=0; allgood=True; p=mb+1
    while cnt<25 and p<mb*20+200:
        if isprime(p) and (p-1)%n==0:
            cnt+=1
            if excess(p,n)>0: allgood=False; break
        p+=1
    print(f"       => verified-bad (p≡1 mod n): {verified}")
    print(f"       => ALL p>{mb} (p≡1 mod n, sampled {cnt}) have excess 0: {allgood}")
    print()

print("="*78)
print("PROBE 4b: explicit threshold p0(n) = largest bad prime; compare to candidates")
print("Candidates for closed form of p0(n) for n=2^m")
print("="*78)
for m in (2,3,4,5):
    n=2**m
    bp=forbidden_norm_primes(n)
    mb=max(bp) if bp else 0
    # 2^m roots: largest 4-term norm prime. Compare to (2n choose stuff), Fermat F_{m}, etc
    print(f"n={n}: maxbad={mb}, 2^n-1 factors include? ", mb, " n^2.5=", round(n**2.5))
