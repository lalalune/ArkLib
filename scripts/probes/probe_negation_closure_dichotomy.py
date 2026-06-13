#!/usr/bin/env python3
"""
probe(#389): the prize's smooth-domain obstruction is EXACTLY negation-closure (2 | n).

Verified (generic p>P_max): the additive energy of the order-n multiplicative subgroup is
    E^+(mu_n) = 2n^2 - n            (pure Sidon, additively GENERIC)      if n is ODD
    E^+(mu_n) = 3n^2 - 3n = (2n^2-n) + (n^2-2n)  (antipodal excess)       if n is EVEN
The single discriminating feature is whether -1 in mu_n, i.e. whether 2 | n (the antipodal pair
a + (-a) = 0 is the only short vanishing sum; Lam-Leung). Confirmed n in {3,5,7,9,11,13,15} (odd,
excess 0) vs {4,6,8,12,16,32} (even, excess = n^2-2n).

WHY THIS MATTERS FOR THE PRIZE. Both faces of the open core trace to this one feature:
  - MCA face: the energy excess n^2-2n (antipodal solutions a+b=c+d=0) is the non-generic part that
    the line-incidence / character-sum bound must control past Johnson.
  - LD face: mu_n fails higher-order MDS (fleet's formalized mu_8 RIM counterexample,
    PermanentlyBlocked.lean) -- a low-degree vanishing relation among roots of unity, same cyclotomic
    origin.
The prize REQUIRES a 2-power (NTT/FFT) domain, so it is forced into the antipodal-rich WORST case; an
odd-order smooth domain would be additively generic (Sidon). The prize's hardness is intrinsic to the
2-power requirement, not to "smooth domains" in general.

SPECULATIVE ROUTE (flagged, NOT a claim): if the antipodal involution is the ONLY non-generic
structure (Lam-Leung: all 2^k-th-root vanishing sums are antipodal), then list-decoding past Johnson
might reduce to the antipodal-quotient/folded code, which could be generic. Untested; would need the
quotient to preserve the RS/list structure -- a concrete next experiment, not a result.
"""
import sympy
from collections import Counter

def energy(n):
    m=(n**6-1)//n
    while True:
        p=m*n+1; m+=1
        if sympy.isprime(p):
            g=int(sympy.primitive_root(p)); z=pow(g,(p-1)//n,p)
            H=[pow(z,j,p) for j in range(n)]
            c=Counter()
            for a in H:
                for b in H: c[(a+b)%p]+=1
            return sum(v*v for v in c.values())

def main():
    print(f"{'n':>4} {'odd/even':>9} {'E^+':>8} {'2n^2-n':>8} {'excess':>7} {'pred n^2-2n':>11}")
    for n in [3,5,7,9,11,13,15, 4,6,8,12,16,32]:
        E=energy(n); sidon=2*n*n-n
        pred = 0 if n%2 else n*n-2*n
        print(f"{n:>4} {('odd' if n%2 else 'even'):>9} {E:>8} {sidon:>8} {E-sidon:>7} {pred:>11}")
    print("=> excess = 0 (odd, generic Sidon) / n^2-2n (even, antipodal). Obstruction = negation-closure.")

if __name__=="__main__":
    main()
