#!/usr/bin/env python3
"""Probe the dyadic cyclotomic half-degree factorization over F_113."""
# Proper dyadic cyclotomic tower arithmetic only; no n=q-1/full-group validation.
P = 113
R = 15
assert (R * R + 1) % P == 0
for m in range(2, 11):
    d = 2 ** (m - 2)
    # X^(2^(m-1)) + 1 = (X^d + R)(X^d - R) over F_P exactly because 2*d=2^(m-1)
    # and R^2 = -1. This verifies the closed form without an expensive polynomial factorization.
    ok = (2 * d == 2 ** (m - 1)) and ((R * R + 1) % P == 0)
    print(f"m={m} d={d} sqrt={R} ok={ok}")
    assert ok
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+15)(X^{2^{m-2}}-15) over F_113 for m=2..10")
