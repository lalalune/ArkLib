#!/usr/bin/env python3
"""
Probe: the SMALLEST odd bad prime for antipodal-free relations as a function of weight w and m.
The prize regime needs depth r ≈ log q, weight ≈ 2 log q. Does the smallest bad prime GROW with
weight (good for the wall — pushes bad primes away from any fixed prize p) or stay small?

For each weight w (2..6) and m (3..6), over antipodal-free relations σ_T, the bad primes are the
odd primes p with p | N(σ_T). The SMALLEST odd bad prime over all weight-w relations = the smallest
odd p that supports SOME weight-w spurious collision = onset of Spur_{w/2}(p) at that p.

Key wall question: is min-bad-prime monotone-increasing in m at fixed weight? If yes, a FIXED prize
prime p eventually sees NO spurious collisions at any bounded weight as m→∞ (the relations that
collide at p have weight → ∞), which is the structural content of "Spur localized to deep relations."
"""
import sympy as sp
from sympy import symbols, Poly, cyclotomic_poly, resultant, factorint, ZZ
from itertools import combinations, product

x=symbols('x')

def relation_norm(exps, signs, m):
    N=2**m
    Phi=cyclotomic_poly(N,x)
    R=sum(s*x**e for s,e in zip(signs,exps))
    return int(abs(resultant(Poly(Phi,x,domain=ZZ),Poly(R,x,domain=ZZ))))

def antipodal_free(exps,signs,N):
    half=N//2
    for i in range(len(exps)):
        for j in range(i+1,len(exps)):
            d=(exps[i]-exps[j])%N
            if d==0: return False
            if d==half and signs[i]==signs[j]: return False
    return True

for m in range(3,6):
    N=2**m
    print(f"\n=== m={m} N={N} phi={N//2} ===")
    for w in ([2,4] if m<=5 else [2]):  # weight = number of terms (first term fixed +1 at exp0)
        min_odd=None
        odd_primes_seen=set()
        # choose w-1 more exps + signs
        if w-1 > N-1: continue
        count=0
        for exps_rest in combinations(range(1,N), w-1):
            for signs_rest in product([1,-1], repeat=w-1):
                exps=(0,)+exps_rest; signs=(1,)+signs_rest
                if not antipodal_free(exps,signs,N): continue
                nv=relation_norm(exps,signs,m)
                if nv==0: continue
                count+=1
                f=factorint(nv)
                for p in f:
                    if p!=2:
                        odd_primes_seen.add(p)
                        if min_odd is None or p<min_odd: min_odd=p
        small=sorted(odd_primes_seen)[:8]
        print(f"  weight={w}: tested={count}, min odd bad prime={min_odd}, smallest odd primes={small}")
