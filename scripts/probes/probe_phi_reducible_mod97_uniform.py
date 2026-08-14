#!/usr/bin/env python3
# Exact probe for Issue #444: Phi_{2^m} half-degree factorization over F_97.
# Proper dyadic cyclotomic tower arithmetic only; no n=q-1/full-group validation.
import sympy as sp

X = sp.Symbol('X')
p = 97
r = 22
assert (r * r + 1) % p == 0
for m in range(2, 11):
    e = 2 ** (m - 2)
    phi = X ** (2 ** (m - 1)) + 1
    rhs = (X**e + r) * (X**e - r)
    rem = sp.Poly(phi - rhs, X, modulus=p)
    assert rem.is_zero, (m, rem)
    fl = sp.factor_list(sp.Poly(phi, X, modulus=p))[1]
    degs = sorted([sp.degree(f) for f, mult in fl for _ in range(mult)])
    print(f"m={m} deg={sp.degree(phi)} factor_degrees={degs} ok")
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+22)(X^{2^{m-2}}-22) over F_97 for m=2..10")
