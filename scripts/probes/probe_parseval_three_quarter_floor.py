#!/usr/bin/env python3
"""Probe q>=4n Parseval floor: M(mu_n)^2 >= 3n/4 on proper 2-power subgroups."""
import cmath
import math


def is_prime(p):
    if p < 2:
        return False
    if p % 2 == 0:
        return p == 2
    d = 3
    while d * d <= p:
        if p % d == 0:
            return False
        d += 2
    return True


def factor(n):
    fs = []
    d = 2
    while d * d <= n:
        if n % d == 0:
            fs.append(d)
            while n % d == 0:
                n //= d
        d += 1
    if n > 1:
        fs.append(n)
    return fs


def primroot(p):
    fs = factor(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // r, p) != 1 for r in fs):
            return g
    raise RuntimeError


def subgroup(p, n):
    g = primroot(p)
    h = pow(g, (p - 1) // n, p)
    xs = []
    x = 1
    for _ in range(n):
        xs.append(x)
        x = (x * h) % p
    assert len(set(xs)) == n
    return xs


def eta(p, G, b):
    return sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in G)

cases = []
for n in [4, 8, 16, 32, 64]:
    for m in range(4, 2500):
        p = m * n + 1
        if m > 1 and p > 4 * n and is_prime(p):
            cases.append((p, n))
            break
for p in [257, 65537]:
    for n in [4, 8, 16, 32, 64]:
        if n < p - 1 and (p - 1) % n == 0 and p >= 4 * n:
            cases.append((p, n))

fails = 0
worst_margin = 10**9
for p, n in cases:
    G = subgroup(p, n)
    M = max(abs(eta(p, G, b)) for b in range(1, p))
    margin = M * M - 0.75 * n
    worst_margin = min(worst_margin, margin)
    if margin < -1e-7:
        print("FAIL", p, n, M * M, 0.75 * n, margin)
        fails += 1
print(f"cases={len(cases)} fails={fails} worst_margin={worst_margin:.6g}")
assert fails == 0
