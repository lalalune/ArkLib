"""How large is |Res(Phi_n, fourTerm_{i,j,k,l})| ACTUALLY, vs the in-tree AM-GM bound 8^{phi(n)/2}?
The in-tree threshold p > 2^{3n/4} (distinct) / 12^{n/4} (doubled) comes from |Res|^2 <= 8^{phi(n)}
resp 12^{phi(n)}. We measure the ACTUAL max over all (i,j,k,l) of |Res(Phi_n, X^i+X^j-X^k-X^l)|
for n=2^a, and compare to:
  - the AM-GM bound sqrt(8^phi(n)) = 8^{phi(n)/2}
  - n^3, n^2, the empirical largest-bad-prime.
This pins WHETHER the looseness is in the AM-GM step (Res actually poly-small) -> a genuine
sharpenable gap, with a constraint lemma: the true no-parallelogram threshold is p > max|Res| ~ poly(n).
"""
import sympy
from sympy import Poly, resultant, cyclotomic_poly, symbols, Integer

X = symbols('X')


def four_term(i, j, k, l):
    return Poly(X**i + X**j - X**k - X**l, X, domain='ZZ')


for a in (2, 3, 4):
    n = 2**a
    phin = sympy.totient(n)
    Phi = Poly(cyclotomic_poly(n, X), X, domain='ZZ')
    maxres = 0
    maxres_tuple = None
    # enumerate genuine non-swap (i,j,k,l), i<=j, k<=l, {i,j}!={k,l}, exponents in 0..n-1
    for i in range(n):
        for j in range(i, n):
            for k in range(n):
                for l in range(k, n):
                    if {i, j} == {k, l}:
                        continue
                    f = four_term(i, j, k, l)
                    if f.is_zero:
                        continue
                    R = resultant(Phi, f)
                    Ra = abs(int(R))
                    if Ra > maxres:
                        maxres = Ra
                        maxres_tuple = (i, j, k, l)
    amgm = int(8**(phin/2))
    amgm12 = int(12**(phin/2))
    print(f"n={n:2d} phi(n)={phin}: MAX |Res| = {maxres} at {maxres_tuple}; "
          f"n^2={n*n} n^3={n**3} | AM-GM(8)^.5={amgm} AM-GM(12)^.5={amgm12}")
