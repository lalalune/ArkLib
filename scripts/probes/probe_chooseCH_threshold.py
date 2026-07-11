"""PROBE v3: pin the EXACT constraint.

v2 showed: #{distinct h_r(R) : R in binom(mu_n, k+1)}  >  C(n+r-1, r)  whenever r is SMALL
relative to k. Characterize the violation region precisely, and test reading (C): the
quantity ABF26 bounds is the # of distinct MONOMIAL DIRECTIONS (leading monomials of degree r
in n variables), which is exactly C(n+r-1,r) BY DEFINITION (the monomial multiset count), NOT
a count of evaluated values. i.e. the bound is on the INDEX SET, tautological as a cardinality,
and the open content is that #bad <= that index set via the forced-gamma INJECTION, which only
holds when the gamma map is injective on monomial directions.

CONCLUSION TO LAND: the spectrum bound CANNOT be read as 'distinct h-values over subsets'
(false at small r); it MUST be read as 'distinct monomial-multiset DIRECTIONS' = chooseCH n r
by the Sym-card identity (Mathlib card_sym_eq_choose). The brick = formalize that cardinality
identity + the constraint that the value-count reading is refuted (so the bound is a
DIRECTION-count, discharged by Sym.card, NOT an analytic value bound).
"""
from itertools import combinations_with_replacement, combinations
from math import comb
import sympy


def hd(nodes, d):
    tot = 0
    for m in combinations_with_replacement(range(len(nodes)), d):
        prod = 1
        for i in m:
            prod *= nodes[i]
        tot += prod
    return tot


print("=== violation map: distinct h_r-VALUES over (k+1)-subsets vs chooseCH(n,r) ===")
for (n, p) in [(8, 4129), (16, 4129), (32, 4129)]:
    if (p - 1) % n != 0:
        continue
    gg = sympy.primitive_root(p)
    zeta = pow(gg, (p - 1) // n, p)
    mu = [pow(zeta, i, p) for i in range(n)]
    for k in range(1, 5):
        row = []
        for r in range(1, 7):
            kk = k + 1
            if kk > n:
                row.append("  -  ")
                continue
            vals = set()
            for R in combinations(mu, kk):
                vals.add(hd(list(R), r) % p)
            ceil = comb(n + r - 1, r)
            row.append("VIOL " if len(vals) > ceil else " ok  ")
        print(f"n={n:2d} k={k}: r=1..6  " + "".join(row))

# Reading (C) sanity: chooseCH n r == |Sym (Fin n) r| == #deg-r monomial multisets, tautological.
ok = all(comb(n + r - 1, r) == len(list(combinations_with_replacement(range(n), r)))
         for n in range(1, 12) for r in range(0, 8))
print(f"\nchooseCH == #monomial-multisets (Sym card identity): {'CLEAN' if ok else 'FAIL'}")
