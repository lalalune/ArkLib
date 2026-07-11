#!/usr/bin/env python3
"""Probe Φ_{2^m}(X)=(X^{2^{m-2}}+6)(X^{2^{m-2}}-6) over F_37."""
import sympy as sp
X = sp.symbols('X')
p = 37
a = 6
assert (a*a + 1) % p == 0
for m in range(2, 11):
    lhs = sp.Poly(X ** (2 ** (m - 1)) + 1, X, modulus=p)
    rhs = sp.Poly((X ** (2 ** (m - 2)) + a) * (X ** (2 ** (m - 2)) - a), X, modulus=p)
    if lhs != rhs:
        raise SystemExit(f"FAIL m={m}: {lhs.as_expr()} != {rhs.as_expr()}")
    fac = sp.factor_list(lhs.as_expr(), modulus=p)[1]
    degs = sorted(sp.Poly(f, X, modulus=p).degree() for f, _ in fac)
    print(f"m={m}: identity PASS; factor degrees {degs}")
print("PASS: mod37 half-degree dyadic tower, m=2..10")
