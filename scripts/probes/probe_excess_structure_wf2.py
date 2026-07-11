#!/usr/bin/env python3
"""
Structure of the energy EXCESS quadruples at the boundary (#389 Fable wf2).

We found: excess(mu_n) is spiky in p; it explodes at Fermat primes / special p.
Now: WHAT are the excess quadruples? Hypotheses to test:
  H_A: every excess quadruple a+b=c+d (not diagonal/antipodal) corresponds to a
       NONTRIVIAL vanishing 4-sum of n-th roots a+b-c-d=0 that vanishes mod p but
       NOT over Q  (i.e. p | a cyclotomic-integer norm). Hence excess is governed
       by which primes p divide Res-type quantities.
  H_B: excess > 0  <=>  p divides  N := product over the finitely many
       'forbidden' cyclotomic-integer differences  <=>  p is a "bad prime".
  H_C: the rep count r(t) for excess: at a bad prime, some t has r(t) >= 3
       (vs the generic max r(t)=2 from Sidon-mod-neg).  The MAX rep count jumps.
  H_D (signed basis): excess quadruples come in Galois orbits under
       (Z/n)^* acting by x->x^j; the orbit count is the real invariant.
"""
import sympy
from sympy import isprime
from collections import defaultdict, Counter
import itertools, math

def w_of_order(p,n):
    g=sympy.primitive_root(p); return pow(g,(p-1)//n,p)
def mu_n(p,n):
    w=w_of_order(p,n); return [pow(w,i,p) for i in range(n)], w

def rep_counts(G,p):
    cnt=Counter()
    for a in G:
        for b in G: cnt[(a+b)%p]+=1
    return cnt

def maxrep(G,p):
    cnt=rep_counts(G,p)
    return max(cnt.values()), Counter(cnt.values())

print("="*78)
print("PROBE 2a: max rep count r(t) at boundary primes (jump => excess)")
print("="*78)
print(f"{'m':>2} {'n':>4} {'p':>8} {'fermat?':>7} {'maxrep':>6} {'#t:r>=3':>8} {'rep-hist (val:count)':>30}")
for m in range(2,7):
    n=2**m
    targets=[int(n*n*r) for r in (1.0,1.3,2.0,4.0,16.0)]
    seen=set()
    for tgt in targets:
        p=(tgt//n)*n+1
        for _ in range(200000):
            if isprime(p) and p>n*n*0.5: break
            p+=n
        if p in seen: continue
        seen.add(p)
        G,w=mu_n(p,n)
        if len(set(G))!=n: continue
        mr,hist=maxrep(G,p)
        cnt=rep_counts(G,p)
        nbig=sum(1 for t,v in cnt.items() if v>=3 and t!=0)
        fermat = isprime(p) and (p-1)&(p-2)==0  # p-1 power of 2 => Fermat-type
        hh = " ".join(f"{k}:{v}" for k,v in sorted(hist.items()))
        print(f"{m:>2} {n:>4} {p:>8} {str(bool(fermat)):>7} {mr:>6} {nbig:>8}   {hh}")
    print()

print("="*78)
print("PROBE 2b: when excess>0, are the high-rep t's themselves n-th roots? (subfield align)")
print("="*78)
def w_of_order2(p,n):
    g=sympy.primitive_root(p); return pow(g,(p-1)//n,p)
for (n,p) in [(16,257),(32,1153),(64,65537),(64,4289)]:
    if (p-1)%n!=0: continue
    G,w=mu_n(p,n); Gs=set(G)
    cnt=rep_counts(G,p)
    high=[(t,v) for t,v in cnt.items() if v>=3 and t!=0]
    in_mu = sum(1 for t,v in high if t in Gs)
    # are high t's a coset of a subgroup / related to 2-adic valuation?
    print(f"n={n} p={p}: #high-rep t (r>=3) = {len(high)}, of which in mu_n: {in_mu}, maxr={max(cnt.values())}")
    # check: is t/2 in mu_n  (antipodal-doubling) ?
    inv2=pow(2,p-2,p)
    half_in=sum(1 for t,v in high if (t*inv2)%p in Gs)
    print(f"        of the high t, #with t/2 in mu_n: {half_in}")
