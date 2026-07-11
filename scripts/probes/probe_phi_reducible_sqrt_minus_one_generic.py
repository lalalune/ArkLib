#!/usr/bin/env python3
"""Probe the generic square-root-of-minus-one dyadic cyclotomic factorization.

For primes p with an explicit i^2 = -1, verify for m=2..10 that
Phi_{2^m}(X) = (X^{2^{m-2}} + i)(X^{2^{m-2}} - i) over F_p.
This is a one-sweep sanity check for the Lean generic lemma, not a CORE claim.
"""
from sympy import Poly, symbols
from sympy.polys.domains import GF

X = symbols('X')
# explicit roots of -1 modulo p, including the already-landed tower rungs and next p=101
cases = [(5, 2), (13, 5), (17, 4), (29, 12), (37, 6), (41, 9),
         (53, 23), (61, 11), (73, 27), (89, 34), (97, 22), (101, 10)]

for p, i in cases:
    assert (i * i + 1) % p == 0, (p, i)
    F = GF(p)
    for m in range(2, 11):
        lhs = Poly(X ** (2 ** (m - 1)) + 1, X, domain=F)
        rhs = Poly((X ** (2 ** (m - 2)) + i) * (X ** (2 ** (m - 2)) - i), X, domain=F)
        if lhs != rhs:
            raise SystemExit(f"FAIL p={p} i={i} m={m}: {lhs.as_expr()} != {rhs.as_expr()}")
    print(f"p={p:3d} i={i:2d}: PASS m=2..10")

print("PASS: generic sqrt(-1) factorization verified for all sampled p,m")
