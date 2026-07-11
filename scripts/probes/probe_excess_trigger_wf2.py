#!/usr/bin/env python3
"""
The arithmetic TRIGGER for energy excess (#389 Fable wf2).

Findings so far:
 - excess(mu_n)>0  <=>  some t!=0 has rep r(t)>=3
 - generically (Sidon-mod-neg) every t!=0 has r(t)<=2.
 - the #high-rep t is a small integer multiple of n.

The excess comes from EXTRA solutions to a+b=c+d beyond {a,b}={c,d}/antipodal,
i.e. genuine NONTRIVIAL parallelograms among n-th roots, which exist mod p iff
p divides the relevant cyclotomic-integer norm. We pin the exact trigger.

Cleanest reformulation:
  a 3-term coincidence r(t)>=3 means  a+b = a'+b' = a''+b''  (3 distinct unordered pairs).
  Subtract:  (a-a') = (b'-b)  ... i.e. a NONTRIVIAL additive relation among 4 roots
  a+b-a'-b'=0 with {a,b} != {a',b'}.  Over Q (unit circle) this is FORBIDDEN
  (unitCircle_sidon).  So it requires p | N where N = the cyclotomic norm of
  (zeta^i + zeta^j - zeta^k - zeta^l) for some forbidden config.

GOAL: confirm excess>0  <=>  p divides one of the differences
      D_{ijkl} = N_{Q(zeta_n)/Q}( zeta^i+zeta^j-zeta^k-zeta^l ),
  the analogue of the Fermat-number characterization for the u=1 BGK obstruction.
"""
import sympy
from sympy import isprime, primefactors, GF, Poly, symbols, ZZ
from sympy import cyclotomic_poly, resultant
from collections import Counter
import itertools, math

X=symbols('X')

def w_of_order(p,n):
    g=sympy.primitive_root(p); return pow(g,(p-1)//n,p)
def mu_n_list(p,n):
    w=w_of_order(p,n); return [pow(w,i,p) for i in range(n)]
def excess(p,n):
    G=mu_n_list(p,n); cnt=Counter()
    for a in G:
        for b in G: cnt[(a+b)%p]+=1
    E=sum(v*v for v in cnt.values()); return E-(3*n*n-3*n)

print("="*78)
print("PROBE 3a: the set of EXCESS-triggering primes for small n (find the pattern)")
print("="*78)
for n in (4,8,16):
    bad=[]; good=[]
    cnt=0
    p=n+1
    while cnt<40 and p<200000:
        if isprime(p) and (p-1)%n==0:
            e=excess(p,n); cnt+=1
            (bad if e>0 else good).append((p,e))
        p+=1
    print(f"n={n}: bad primes (excess>0): {[b[0] for b in bad][:15]}")
    print(f"       (with excess):        {[(b[0],b[1]) for b in bad][:8]}")
    # factor the bad primes' relation: are they all ≡ special residue?
    if bad:
        print(f"       bad primes mod small: ", [(b[0]%3,b[0]%5,b[0]%7) for b in bad][:8])
    print()

print("="*78)
print("PROBE 3b: cyclotomic-norm trigger. For n, list the norms of 4-term forbidden configs.")
print("Hypothesis: excess(p,n)>0  <=>  p | one of these norms.")
print("="*78)
def cyclo_norm(n, coeffs):
    """coeffs: dict exponent->integer coeff of sum c_i zeta^i; return N_{Q(zeta)/Q}=Res(Phi_n, poly)."""
    Phi = cyclotomic_poly(n, X)
    poly = sum(c* X**(e % n) for e,c in coeffs.items())
    poly = Poly(poly, X)
    r = resultant(Poly(Phi,X), poly)
    return int(r)

for n in (4,8):
    norms=set()
    rng=range(n)
    # forbidden 4-term: zeta^i+zeta^j-zeta^k-zeta^l, {i,j}!={k,l}, not antipodal-trivial
    for i,j,k,l in itertools.product(rng,repeat=4):
        if frozenset([i,j])==frozenset([k,l]): continue
        c=Counter(); c[i]+=1; c[j]+=1; c[k]-=1; c[l]-=1
        cc={e:v for e,v in c.items() if v!=0}
        if not cc: continue
        try:
            N=cyclo_norm(n, cc)
        except Exception as ex:
            continue
        if N!=0:
            for pf in primefactors(abs(N)):
                norms.add(pf)
    norms=sorted(p for p in norms if p>n)
    print(f"n={n}: prime factors of forbidden 4-term cyclotomic norms (>n): {norms[:25]}")
    # cross-check against actual bad primes
    actual_bad=[]
    p=n+1; cnt=0
    while cnt<60 and p<5000:
        if isprime(p) and (p-1)%n==0:
            cnt+=1
            if excess(p,n)>0: actual_bad.append(p)
        p+=1
    print(f"      actual bad primes (excess>0, p<5000): {actual_bad}")
    print(f"      all actual-bad in norm-factor set? {all(b in norms for b in actual_bad)}")
    print()
