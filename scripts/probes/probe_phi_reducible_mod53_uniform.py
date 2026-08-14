#!/usr/bin/env python3
import sympy as sp
x = sp.Symbol('x')
p = 53
r = 23
assert (r*r + 1) % p == 0
for m in range(2, 11):
    e = 2 ** (m - 2)
    phi = sp.Poly(x ** (2 ** (m - 1)) + 1, x, modulus=p)
    rhs = sp.Poly((x ** e + r) * (x ** e - r), x, modulus=p)
    diff = sp.Poly(phi.as_expr() - rhs.as_expr(), x, modulus=p)
    factors = sp.factor_list(phi.as_expr(), modulus=p)[1]
    degs = [sp.Poly(f, x, modulus=p).degree() for f, _ in factors for __ in range(_)]
    print(f"m={m} deg={phi.degree()} factor_degrees={degs}")
    if not diff.is_zero:
        raise SystemExit(f"FAIL identity at m={m}: {diff}")
    if sorted(degs) != [e, e]:
        raise SystemExit(f"FAIL factor degrees at m={m}: {degs}, expected {[e,e]}")
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+23)(X^{2^{m-2}}-23) over F_53 for m=2..10")
