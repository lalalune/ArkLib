#!/usr/bin/env python3
"""Exact probe for the F_137 dyadic sqrt(-1) factorization."""
import sympy as sp
x = sp.symbols('x')
p = 137
i = 37
assert (i*i + 1) % p == 0
for m in range(2, 11):
    lhs = sp.Poly(sp.cyclotomic_poly(2**m, x), x, modulus=p)
    e = 2 ** (m - 2)
    rhs = sp.Poly((x**e + i) * (x**e - i), x, modulus=p)
    if lhs != rhs:
        raise SystemExit(f"FAIL m={m}: {lhs.as_expr()} != {rhs.as_expr()}")
    fac = sp.factor_list(lhs.as_expr(), modulus=p)[1]
    degs = [sp.Poly(g, x, modulus=p).degree() for g, _ in fac]
    print(f"m={m} deg={lhs.degree()} factor_degrees={degs} ok")
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+37)(X^{2^{m-2}}-37) over F_137 for m=2..10")
