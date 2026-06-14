#!/usr/bin/env python3
"""Fully independent certificate check: evaluate the raw vanishing sum
   sum_{i<j} zeta^(a_i+a_j) + sum_i zeta^(2 o_i) + sum_{f in B} zeta^(2f) + zeta^(3s/2)
in complex arithmetic (zeta = primitive 2s-th root of unity). A certificate is
good iff |sum| ~ 0. Shares NO logic with verify_hit.py / diag.c / search.c
(no antipodal-balance combinatorics anywhere). Reads HIT lines on stdin.
"""
import sys, cmath

ok = bad = 0
for line in sys.stdin:
    if not line.startswith("HIT"):
        continue
    parts = [p.strip() for p in line.split("|")]
    head = parts[0].split()
    s, r = int(head[2]), int(head[4])
    O = list(map(int, parts[1].split()[1:]))
    m = int(parts[2].split()[1])
    B = list(map(int, parts[3].split()[1:]))
    n, b = 2 * s, (s + 1 - r) // 2
    assert len(O) == r == len(set(O)) and len(B) == b == len(set(B))
    assert not set(O) & set(B)
    a = [O[0]] + [O[i] + s * ((m >> (i - 1)) & 1) for i in range(1, r)]
    z = lambda e: cmath.exp(2j * cmath.pi * e / n)
    tot = sum(z(a[i] + a[j]) for i in range(r) for j in range(i + 1, r))
    tot += sum(z(2 * o) for o in O) + sum(z(2 * f) for f in B) + z(3 * s // 2)
    # scale tolerance with term count and s
    T = r * (r - 1) // 2 + r + b + 1
    tol = 1e-9 * T * s
    if abs(tot) < tol:
        ok += 1
    else:
        bad += 1
        print(f"NUMERIC-FAIL s={s} r={r} |sum|={abs(tot):.3e} O={O} m={m}")
print(f"NUMERIC SUMMARY ok={ok} bad={bad}")
