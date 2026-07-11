"""The DOUBLED (S=6) four-term 2X^i - X^k - X^l. In-tree bound |Res|^2 <= 12^{phi(n)} (threshold
12^{n/4}). Probe showed max doubled |Res| = 100 (n=8) < 144=12^2, 10000 (n=16) < 20736=12^4 -- the
12-bound is NOT tight. Find the TRUE max doubled resultant and its closed form: is it 10^{phi/2}?
10^2=100 (n=8 match!), 10^4=10000 (n=16 match!). Conjecture: max doubled |Res| = 10^{phi(n)/2}.
Identify the extremizer (i,k,l) and its per-root modulus (should be sqrt(10), the doubled max).
"""
import sympy
from sympy import Poly, resultant, cyclotomic_poly, symbols

X = symbols('X')


def doubled(i, k, l):
    return Poly(2 * X**i - X**k - X**l, X, domain='ZZ')


for a in (2, 3, 4):
    n = 2**a
    phin = sympy.totient(n)
    Phi = Poly(cyclotomic_poly(n, X), X, domain='ZZ')
    maxres = 0
    arg = None
    for i in range(n):
        for k in range(n):
            for l in range(n):
                if len({i, k, l}) != 3:
                    continue
                f = doubled(i, k, l)
                if f.is_zero:
                    continue
                R = abs(int(resultant(Phi, f)))
                if R > maxres:
                    maxres = R
                    arg = (i, k, l)
    import math
    ten = int(round(10 ** (phin / 2)))
    twelve = int(round(12 ** (phin / 2)))
    print(f"n={n:2d} phi={phin}: max doubled |Res| = {maxres} at (i,k,l)={arg}  "
          f"10^(phi/2)={ten} (match={maxres==ten})  12^(phi/2)={twelve}")
