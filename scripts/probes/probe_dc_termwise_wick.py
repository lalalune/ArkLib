#!/usr/bin/env python3
"""Probe the DC-subtracted termwise Wick bound:
   q*E_r - n^{2r} <= q*(2r-1)!!*n^r   (the SAME RHS as the raw producer)
vs the RAW termwise:
   q*E_r        <= q*(2r-1)!!*n^r
Both sum (with the (2r)! denom + y^{2r}) to q*exp(n y^2/2). The DC version subtracts the
b=0 mass n^{2r}. Question: where the RAW termwise FAILS (n>=2^6, deep r), does the DC version still hold?
E_r(G) = #{(v,w) in G^r x G^r : sum v = sum w}, computed exactly char-0 on proper mu_n (roots of unity)
via subset-sum convolution over the GROUP (here mu_n in C, so sums are complex; we count multiplicity
of each complex sum value). For SPEED use the cyclic structure: mu_n = {zeta^j}, additive sums live in
Z[zeta]; we hash by (rounded re, im).
PROPER mu_n, n=2^a. NEVER n=q-1 (char-0 has no q; this is the char-0 termwise object, the DCEnergyEssential input).
"""
import math, cmath
from collections import Counter
from math import comb, factorial

def doublefact(m):
    if m<=0: return 1
    r=1
    while m>0:
        r*=m; m-=2
    return r

def Er_charzero(n, r):
    # mu_n = n-th roots of unity. E_r = sum over t of (#{w in mu_n^r : sum w = t})^2
    # build distribution of r-fold sums by convolution
    pts=[cmath.exp(2j*math.pi*j/n) for j in range(n)]
    # dist: dict val->count  (val rounded)
    def key(z): return (round(z.real,6), round(z.imag,6))
    dist=Counter({key(p):1 for p in pts})
    cur=dict(dist)
    for _ in range(r-1):
        nxt=Counter()
        for (kr,ki),c in cur.items():
            for p in pts:
                z=complex(kr,ki)+p
                nxt[key(z)]+=c
        cur=dict(nxt)
    if r==0:
        return 1
    return sum(c*c for c in cur.values())

print("char-0 termwise DC vs RAW Wick:  q*E_r - n^{2r} <= q*(2r-1)!! n^r  vs  q*E_r <= ...")
for n in [4,8,16]:
    for beta in [4.0]:
        q=int(n**beta)  # the q that scales the MGF (the field size in the finite-field analogue)
        print(f"-- n={n} q=n^{beta}={q}")
        rmax = min(2*int(math.log2(q))+2, 14)
        for r in range(1, rmax):
            Er=Er_charzero(n,r)
            wick = q*doublefact(2*r-1)*(n**r)
            raw_lhs = q*Er
            dc_lhs  = q*Er - n**(2*r)
            raw_ok = raw_lhs <= wick
            dc_ok  = dc_lhs  <= wick
            flag = "" if (raw_ok and dc_ok) else ("  <-- RAW FAILS, DC ok" if (dc_ok and not raw_ok) else ("  <-- BOTH FAIL" if not dc_ok else ""))
            if (not raw_ok) or (not dc_ok) or r<=4:
                print(f"   r={r:2d}  E_r={Er:>14d}  q*E_r={raw_lhs:.3e}  q*E_r-n^2r={dc_lhs:.3e}  Wick={wick:.3e}  raw<=W:{raw_ok} dc<=W:{dc_ok}{flag}")
