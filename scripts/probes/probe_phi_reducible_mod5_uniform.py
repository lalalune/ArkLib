#!/usr/bin/env python3
# Exact probe: Phi_{2^m}(X)=X^{2^{m-1}}+1 over F_5 factors by the lifted square-root-of--1 chain.
# If g_m = X^{2^{m-2}} + 2 and h_m = X^{2^{m-2}} - 2, then g_m*h_m = X^{2^{m-1}} - 4 = X^{2^{m-1}}+1 mod 5.
import sympy as sp
X=sp.Symbol('X')
for m in range(3,10):
    phi = X**(2**(m-1)) + 1
    g = X**(2**(m-2)) + 2
    h = X**(2**(m-2)) - 2
    rem = sp.Poly(phi - g*h, X, modulus=5)
    fac = sp.factor_list(sp.Poly(phi, X, modulus=5))[1]
    assert rem.is_zero, (m, rem)
    assert 0 < sp.degree(g) < sp.degree(phi)
    print(f"m={m}: deg Phi={sp.degree(phi)}, factor degrees {sp.degree(g)}+{sp.degree(h)}, factorization={fac}")
print("PASS: Phi_{2^m} reducible over F_5 for m=3..9 via (X^{2^{m-2}}+2)(X^{2^{m-2}}-2)")
