#!/usr/bin/env python3
import sympy as sp
X = sp.symbols('X')
for m in range(3, 10):
    phi = X ** (2 ** (m - 1)) + 1
    a = X ** (2 ** (m - 2))
    rhs = (a + 5) * (a - 5)
    rem = sp.Poly(phi - rhs, X, modulus=13)
    fac = sp.factor_list(sp.Poly(phi, X, modulus=13))[1]
    assert rem.is_zero
    print(f"m={m}: deg={2**(m-1)}, factor degrees {2**(m-2)}+{2**(m-2)}, factorization={fac}")
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+5)(X^{2^{m-2}}-5) over F_13 for m=3..9")
