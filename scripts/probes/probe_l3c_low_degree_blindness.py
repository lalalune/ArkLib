#!/usr/bin/env python3
"""Probe L3c low-degree frequency-blindness fence on finite prime fields.
Checks one sweep: every monomial x^i with i < p-1 sums to 0 mod p, while x^(p-1)
sums to -1 mod p. This is the concrete finite-field kernel behind the Lean corollary.
"""
PRIMES = [5, 7, 17, 41, 97, 257]
print("=== L3c low-degree full-field-sum blindness probe ===")
for p in PRIMES:
    bad = []
    for i in range(p - 1):
        s = sum(pow(x, i, p) for x in range(p)) % p
        if s != 0:
            bad.append((i, s))
    top = sum(pow(x, p - 1, p) for x in range(p)) % p
    print(f"p={p:3d}: below-top bad={len(bad)} top_sum={top} expected_top={p-1}")
    assert not bad
    assert top == p - 1
print("PASS: low-degree (<p-1) full-field sums are zero; the first sensitive degree is p-1")
