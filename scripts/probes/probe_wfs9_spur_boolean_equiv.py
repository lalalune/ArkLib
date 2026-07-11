#!/usr/bin/env python3
"""Probe the wf-S9 split-prime Boolean equivalence on integer products.

A product norm is p-divisible iff at least one local split residue is p-divisible.
This is arithmetic sanity, not a CORE claim; includes empty/nonempty rows.
"""
import random

for p in [3, 5, 17, 257]:
    for n in [0, 1, 2, 5, 9]:
        for _ in range(200):
            arr = [random.randint(-500, 500) or 1 for _ in range(n)]
            prod = 1
            for a in arr:
                prod *= a
            lhs = (prod % p) == 0
            rhs = any((a % p) == 0 for a in arr)
            assert lhs == rhs, (p, arr, prod, lhs, rhs)

print("PASS: prime divides product iff one local residue vanishes, empty/nonempty/random rows")
