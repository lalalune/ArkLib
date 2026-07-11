#!/usr/bin/env python3
"""Exact probe for the p=41 dyadic cyclotomic half-degree factorization.

Checks Phi_{2^m}(X) = (X^(2^(m-2)) + 9)(X^(2^(m-2)) - 9) over F_41,
since 9^2 = -1 mod 41. Reducibility necessary condition only, not a spur collision or CORE claim.
"""
import sympy as sp
X = sp.symbols('X')
p = 41
r = 9
assert (r * r + 1) % p == 0
for m in range(2, 11):
    lhs = sp.Poly(sp.cyclotomic_poly(2 ** m, X), X, modulus=p)
    rhs = sp.Poly((X ** (2 ** (m - 2)) + r) * (X ** (2 ** (m - 2)) - r), X, modulus=p)
    if lhs != rhs:
        raise SystemExit(f"FAIL m={m}: {lhs.as_expr()} != {rhs.as_expr()}")
    factors = sp.factor_list(lhs.as_expr(), modulus=p)[1]
    degs = [sp.Poly(f, X, modulus=p).degree() for f, _ in factors]
    print(f"m={m}: deg={lhs.degree()}, factor_degrees={degs}")
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+9)(X^{2^{m-2}}-9) over F_41 for m=2..10")
