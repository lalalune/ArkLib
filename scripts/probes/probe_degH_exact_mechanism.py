#!/usr/bin/env python3
"""Verify the CLEAN char-0 mechanism behind deg H + m >= k-1 (dyadic):
  CLAIM A: e_1(S)=sum_{s in S} s = 0  <=>  S = -S (antipodal-symmetric)  [Lam-Leung dyadic]
  CLAIM B: H != 0 (S != -S)  =>  deg H = k-1 EXACTLY (not just >= k/2)   [since top odd coeff = +-e_1]
  => deg H + m = (k-1) + m >= k-1, with deg H = k-1 the exact value. Stronger & simpler than
     the swarm's 'deg H + m >= k-1 via m <= deg H => deg H >= k/2'.
Check over all 2k-subsets of mu_{4k} for dyadic 4k in {8,16,32} and non-dyadic 12,24 (must FAIL)."""
import itertools, cmath, math

def build(S, roots):
    poly=[1.0+0j]
    for s in S:
        r=roots[s]; new=[0j]*(len(poly)+1)
        for i,c in enumerate(poly):
            new[i]+=c*(-r); new[i+1]+=c
        poly=new
    H=[poly[i] for i in range(1,len(poly),2)]
    dH=-1
    for i,c in enumerate(H):
        if abs(c)>1e-7: dH=i
    return dH

def check(N):  # N=4k = group order
    k=N//4; roots=[cmath.exp(2j*math.pi*t/N) for t in range(N)]; half=N//2
    dyadic = (N & (N-1))==0
    bad_A=0; bad_B=0; tot=0; checked=0
    for S in itertools.combinations(range(N),2*k):
        tot+=1
        Sset=set(S)
        antisym = all(((s+half)%N) in Sset for s in S)   # S = -S
        e1=sum(roots[s] for s in S); e1z = abs(e1)<1e-7
        # CLAIM A: e1==0 <=> antisym
        if e1z != antisym: bad_A+=1
        # CLAIM B: if not antisym (H!=0) then deg H == k-1
        if not antisym:
            checked+=1
            dH=build(S,roots)
            if dH != k-1: bad_B+=1
    tag="DYADIC" if dyadic else "non-dyadic"
    print(f" N={N:3d} (k={k}, {tag}): subsets={tot}  ClaimA(e1=0<=>S=-S) violations={bad_A}  "
          f"ClaimB(H!=0=>degH=k-1) violations={bad_B}/{checked}", flush=True)

for N in (8,16,32):   # dyadic: both claims should hold (0 violations)
    check(N)
for N in (12,24):     # non-dyadic: claims FAIL (cube/other roots break Lam-Leung)
    check(N)
