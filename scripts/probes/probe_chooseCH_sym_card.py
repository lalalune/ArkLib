"""PROBE: the open CompleteHomogeneousSpectrumBound reduction brick.

Claim chain:
 (1) chooseCH s r := C(s+r-1, r) == number of degree-r monomial-multisets on s nodes
     == |Sym (Fin s) r| == multichoose s r   (Mathlib: card_sym_eq_choose / multichoose_eq).
 (2) the distinct h_r-VALUE spectrum is the IMAGE of a map (monomial-multiset -> value),
     hence its card <= #monomial-multisets = chooseCH s r.  (image card <= domain card)
 This is the structural mechanism that DISCHARGES the open spectrum bound GIVEN the
 monomial-basis surjection (h_r = sum over deg-r monomials, SchurLagrangeBridge).
"""
from itertools import combinations_with_replacement, combinations
from math import comb
import sympy

fails = 0
checks = 0

# (1) chooseCH == multiset count == brute multiset enumeration, exact, sweep
for s in range(1, 14):
    for r in range(0, 10):
        chooseCH = comb(s + r - 1, r)
        nm = comb(s + r - 1, r) if s >= 1 else (1 if r == 0 else 0)
        brute = len(list(combinations_with_replacement(range(s), r)))
        checks += 1
        if not (chooseCH == nm == brute):
            print(f"FAIL card s={s} r={r}: chooseCH={chooseCH} nm={nm} brute={brute}")
            fails += 1


def hr(nodes, r):
    tot = 0
    for m in combinations_with_replacement(range(len(nodes)), r):
        prod = 1
        for i in m:
            prod *= nodes[i]
        tot += prod
    return tot


# (2) image-of-map bound: distinct h_r VALUES over (k+1)-subsets of mu_s <= chooseCH s r
for (n, p) in [(4, 4129), (8, 4129), (8, 4177), (16, 4129)]:
    if (p - 1) % n != 0:
        continue
    gg = sympy.primitive_root(p)
    zeta = pow(gg, (p - 1) // n, p)
    mu = [pow(zeta, i, p) for i in range(n)]
    s = n
    for k in range(1, 4):
        for r in range(1, 5):
            kk = k + 1
            if kk > s:
                continue
            vals = set()
            for R in combinations(mu, kk):
                vals.add(hr(list(R), r) % p)
            checks += 1
            ceil = comb(s + r - 1, r)
            if len(vals) > ceil:
                print(f"FAIL spectrum n={n} p={p} k={k} r={r}: |vals|={len(vals)} > chooseCH={ceil}")
                fails += 1

print(f"checks={checks} fails={fails}")
