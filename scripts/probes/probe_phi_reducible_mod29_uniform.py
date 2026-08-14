#!/usr/bin/env python3
"""Exact probe for the p=29 dyadic cyclotomic half-degree factorization.

Checks Phi_{2^m}(X) = X^(2^(m-1)) + 1 = (X^(2^(m-2)) + 12)(X^(2^(m-2)) - 12) over F_29,
since 12^2 = -1 mod 29. This is only a reducibility necessary-condition probe,
not a short-relation or CORE claim.
"""
import sympy as sp

X = sp.symbols('X')
p = 29
r = 12
assert (r * r + 1) % p == 0
for m in range(3, 10):
    lhs = sp.Poly(X ** (2 ** (m - 1)) + 1, X, modulus=p)
    rhs = sp.Poly((X ** (2 ** (m - 2)) + r) * (X ** (2 ** (m - 2)) - r), X, modulus=p)
    if lhs != rhs:
        raise SystemExit(f"FAIL m={m}: {lhs.as_expr()} != {rhs.as_expr()}")
print("PASS p=29 dyadic cyclotomic factorization for m=3..9; 12^2=-1 mod 29")
