#!/usr/bin/env python3
"""Exact probe for issue #444: Phi_{2^m} over F_73 has a uniform half-degree split.

For m >= 2, Phi_{2^m}=X^{2^{m-1}}+1. Since 27^2=-1 mod 73, it should factor as
(X^{2^{m-2}}+27)(X^{2^{m-2}}-27). This is only a cyclotomic reducibility check, not a CORE claim.
"""
import sympy as sp
X = sp.symbols('X')
p = 73
r = 27
assert (r*r + 1) % p == 0
for m in range(2, 11):
    phi = X ** (2 ** (m - 1)) + 1
    lhs = sp.Poly(phi, X, modulus=p)
    rhs = sp.Poly((X ** (2 ** (m - 2)) + r) * (X ** (2 ** (m - 2)) - r), X, modulus=p)
    assert lhs == rhs, (m, lhs, rhs)
    coeff, factors = sp.factor_list(lhs, modulus=p)
    degs = [f.degree() for f, mult in factors for _ in range(mult)]
    print(f"m={m} deg={lhs.degree()} factor_degrees={degs}")
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+27)(X^{2^{m-2}}-27) over F_73 for m=2..10")
