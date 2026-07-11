#!/usr/bin/env python3
"""Probe the dyadic cyclotomic half-degree factorization over F_101."""
P = 101
R = 10
assert (R * R + 1) % P == 0
for m in range(2, 11):
    d = 2 ** (m - 2)
    ok = ((R * R + 1) % P == 0) and (2 * d == 2 ** (m - 1))
    print(f"m={m} d={d} sqrt={R} ok={ok}")
    assert ok
print("PASS: Phi_{2^m}=(X^{2^{m-2}}+10)(X^{2^{m-2}}-10) over F_101 for m=2..10")
