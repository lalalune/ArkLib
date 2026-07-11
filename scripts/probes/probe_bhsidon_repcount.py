#!/usr/bin/env python3
"""
Probe: a B_h-Sidon set has h-fold ORDERED representation function r_h(x) <= h!.

r_h(x) = #{ (a_1,...,a_h) in S^h : a_1+...+a_h = x }  (ORDERED tuples).
Claim: B_h-Sidon (unique MULTISET per sum) => r_h(x) <= h! for every x.
Reason: all ordered reps of x share the SAME multiset (uniqueness), and a single
size-h multiset has at most h! orderings (exactly h!/prod(mult!) ).
So the MULTISET rep function R_h(x) in {0,1}, and r_h(x) <= h!.

Probe r_h(x) <= h! and also confirm R_h(x) <= 1 (the multiset version), over
PROPER thin mu_n + random sets. NEVER n=q-1.
"""
from itertools import product
import math, random

def rep_counts(S, h, m):
    """returns (max ordered rep over all sums, max multiset rep over all sums)."""
    ordered = {}
    msets = {}
    for tup in product(S, repeat=h):
        s = sum(tup) % m
        ordered[s] = ordered.get(s,0)+1
        key = tuple(sorted(tup))
        msets.setdefault(s,set()).add(key)
    max_ord = max(ordered.values()) if ordered else 0
    max_mset = max(len(v) for v in msets.values()) if msets else 0
    return max_ord, max_mset

def is_bh_sidon(S,h,m):
    seen={}
    from itertools import combinations_with_replacement as cwr
    for c in cwr(range(len(S)),h):
        s=sum(S[i] for i in c)%m
        k=tuple(sorted(S[i] for i in c))
        if s in seen:
            if seen[s]!=k: return False
        else: seen[s]=k
    return True

random.seed(13)
viol_ord=viol_mset=tot=0
for _ in range(6000):
    m=random.choice([13,17,19,23,29,31,37,41])
    k=random.randint(1,6)
    S=random.sample(range(m),min(k,m))
    h=random.randint(2,4)
    if is_bh_sidon(S,h,m):
        tot+=1
        mo,mm = rep_counts(S,h,m)
        if mo > math.factorial(h): viol_ord+=1
        if mm > 1: viol_mset+=1

print(f"B_h-Sidon cases: {tot}")
print(f"ordered rep > h! violations: {viol_ord}")
print(f"multiset rep > 1 violations:  {viol_mset}")
print("VERDICT: B_h-Sidon => r_h(x) <= h! AND R_h(x) <= 1." if viol_ord==0 and viol_mset==0 else "VERDICT: violation, recheck.")
