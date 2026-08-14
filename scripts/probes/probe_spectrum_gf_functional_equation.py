#!/usr/bin/env python3
"""Probe for SpectrumGFFunctionalEquation.lean (#444).

Discharges Sweep_A50's asserted functional-equation consequence:
  x^(2m) * G(1/x) = G(x)   for x != 0,   G(x)=spectrumGF(x,m).
Equivalently G is self-reciprocal (palindromic), i.e. N_r = N_{2m-r}.

MECHANISM (inner reindex, NO cancellation): the term C(m,k)2^k x^(k+2i) maps under x->1/x then
*x^(2m) to C(m,k)2^k x^(2m-k-2i), and 2m-k-2i = k+2((m-k)-i), with i'=(m-k)-i ranging over the
same range(m-k+1) (reflection involution). So the double sum is invariant.

Tested exactly over the rationals (Fraction) to avoid float error.
"""
from fractions import Fraction as Fr
from math import comb

def G(x, m):
    return sum(comb(m, k) * 2 ** k * sum(x ** (k + 2 * i) for i in range(m - k + 1))
               for k in range(m + 1))

def main():
    fails = 0
    tested = 0
    xs = [Fr(2), Fr(3), Fr(3, 2), Fr(7, 5), Fr(1, 2), Fr(5, 3), Fr(-2), Fr(-3, 4)]
    for m in range(0, 13):
        # coefficient palindrome N_r = N_{2m-r}
        coeff = {}
        for k in range(m + 1):
            for i in range(m - k + 1):
                r = k + 2 * i
                coeff[r] = coeff.get(r, 0) + comb(m, k) * 2 ** k
        deg = max(coeff) if coeff else 0
        sym = all(coeff.get(r, 0) == coeff.get(2 * m - r, 0) for r in range(2 * m + 1))
        if deg != 2 * m or not sym:
            fails += 1
            print(f"FAIL coeff m={m}: deg={deg} sym={sym}")
        # functional equation at concrete nonzero x
        for xv in xs:
            tested += 1
            if xv ** (2 * m) * G(1 / xv, m) != G(xv, m):
                fails += 1
                print(f"FAIL fe m={m} x={xv}")
    print(f"functional eq x^(2m)G(1/x)=G(x) + coeff palindrome N_r=N_(2m-r): "
          f"{fails} fails / m=0..12 x {len(xs)} points ({tested} fe-evals)")

if __name__ == "__main__":
    main()
