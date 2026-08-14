#!/usr/bin/env python3
"""Exact probe: Phi_{2^m} factors over F_17 as (X^{2^{m-2}}+4)(X^{2^{m-2}}-4)."""
import sympy as sp
X = sp.symbols('X')
for m in range(3, 10):
    a = 2 ** (m - 2)
    phi = sp.Poly(X ** (2 ** (m - 1)) + 1, X, modulus=17)
    rhs = sp.Poly((X**a + 4) * (X**a - 4), X, modulus=17)
    assert phi == rhs, (m, phi, rhs)
    fac = sp.factor_list(phi.as_expr(), modulus=17)[1]
    print(f"m={m}: deg={phi.degree()}, factor degrees {[sp.Poly(f, X, modulus=17).degree() for f,_ in fac]}, factorization={fac}")
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+4)(X^{2^{m-2}}-4) over F_17 for m=3..9")
