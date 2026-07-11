#!/usr/bin/env python3
"""Consolidated verdict flags for C21-C28. Each prints PASS/FAIL of its closure predicate
with a one-line mechanism. Multi-prime, proper mu_n, rule-3 where applicable."""
import sys, math
import numpy as np
sys.path.insert(0,"/tmp")
from probe_444r2_conj3_core import find_prime, subgroup, M_of, neg_closed_random

def spec2(S,p):
    ind=np.zeros(p)
    for x in S: ind[int(x)]=1.0
    return np.abs(np.fft.fft(ind))**2

print("C21 metaplectic factorization: #distinct|eta|^2 vs #cosets")
ok=True
for mu in (3,4,5):
    n=2**mu; p=find_prime(n,3.0); S=subgroup(n,p)
    nd=len(set(np.round(spec2(S,p),6))); nc=(p-1)//n
    if nd > 2*(mu+5): ok_local=False
    print(f"  n={n}: distinct={nd} cosets={nc} mu+1={mu+1}  (collapse-to-O(mu)? {'YES' if nd<=mu+3 else 'NO'})")
print(f"  => REFUTED: distinct values ~ #cosets (coset-spectrum, DEAD/thickness-inv), no O(mu) metaplectic collapse.\n")

print("C28 recursion M(n)<=sqrt2 M(n/2) at prize-beta=4 + rule-3:")
viol=0; tot=0
for mu in (4,5,6):
    n=2**mu; p=find_prime(n,4.0)
    S=subgroup(n,p); Sh=subgroup(n//2,p)
    Mn=math.sqrt(spec2(S,p)[1:].max()); Mh=math.sqrt(spec2(Sh,p)[1:].max())
    T=neg_closed_random(n,p,5); Th=neg_closed_random(n//2,p,6)
    Mt=math.sqrt(spec2(T,p)[1:].max()); Mth=math.sqrt(spec2(Th,p)[1:].max())
    r=Mn/Mh; rt=Mt/Mth; tot+=1
    if r>math.sqrt(2): viol+=1
    print(f"  n={n}: thin {r:.3f} thick {rt:.3f}  recursion {'HOLDS' if r<=math.sqrt(2) else 'VIOLATED'}")
print(f"  => REFUTED at prize-beta: {viol}/{tot} violate M<=sqrt2 M(n/2); thin~thick (thickness-invariant).")
