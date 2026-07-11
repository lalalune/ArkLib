"""Restrict to GENUINE distinct parallelograms (the case the in-tree hdist hypothesis governs):
i,j,k,l with the multiset {i,j} != {k,l} AND the four powers zeta^i,zeta^j,zeta^k,zeta^l pairwise
distinct (i.e. i,j,k,l pairwise distinct mod n). Measure max |Res(Phi_n, X^i+X^j-X^k-X^l)| over those.
Compare to n^3 and the in-tree AM-GM bound. This is the apples-to-apples threshold comparison.
"""
import sympy
from sympy import Poly, resultant, cyclotomic_poly, symbols

X = symbols('X')


def four_term(i, j, k, l):
    return Poly(X**i + X**j - X**k - X**l, X, domain='ZZ')


for a in (2, 3, 4):
    n = 2**a
    phin = sympy.totient(n)
    Phi = Poly(cyclotomic_poly(n, X), X, domain='ZZ')
    maxres = 0
    maxres_tuple = None
    maxres_doubled = 0  # j=i but i,k,l distinct (the S=6 doubled case)
    md_tuple = None
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    powers = {i, j, k, l}
                    # genuine relation, NOT a swap
                    if sorted([i, j]) == sorted([k, l]):
                        continue
                    f = four_term(i, j, k, l)
                    if f.is_zero:
                        continue
                    R = abs(int(resultant(Phi, f)))
                    if R == 0:
                        continue
                    if len(powers) == 4:  # all distinct, S=4
                        if R > maxres:
                            maxres = R; maxres_tuple = (i, j, k, l)
                    elif i == j and len({i, k, l}) == 3:  # doubled distinct, S=6
                        if R > maxres_doubled:
                            maxres_doubled = R; md_tuple = (i, j, k, l)
    print(f"n={n:2d}: max|Res| DISTINCT(S=4) = {maxres} at {maxres_tuple}; "
          f"DOUBLED(S=6) = {maxres_doubled} at {md_tuple}; "
          f"n^2={n*n} n^3={n**3} 8^(phi/2)={int(8**(phin/2))} 12^(phi/2)={int(12**(phin/2))}")
