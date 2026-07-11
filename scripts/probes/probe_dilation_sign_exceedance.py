#!/usr/bin/env python3
"""Probe the sign-cocycle exceedance implication on proper thin 2-power subgroups.
If |eta_{G∪zG}(b)| exceeds the child level maximum M_G, then the two child real periods
must have positive product. Never validates on full group.
"""
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
    return xs, g


def eta(p, G, b):
    return sum(cmath.exp(2j * math.pi * ((b * x) % p) / p) for x in G)


cases = []
for n in [4, 8, 16, 32, 64]:
    for m in range(max(2, n * n), max(2, n * n) + 2000):
        p = m * n + 1
        if is_prime(p) and p > n ** 3 and m > 1:
            cases.append((p, n))
            break
for p in [257, 65537]:
    for n in [4, 8, 16, 32, 64]:
        if n < p - 1 and (p - 1) % n == 0:
            cases.append((p, n))

fail = 0
total = 0
exceed = 0
for p, n in cases:
    Gfull, g = subgroup(p, n)
    h = pow(g, (p - 1) // n, p)
    G = []
    x = 1
    for _ in range(n // 2):
        G.append(x)
        x = (x * (h * h % p)) % p
    z = h
    zG = [(z * x) % p for x in G]
    assert set(G).isdisjoint(set(zG)) and set(G) | set(zG) == set(Gfull)
    vals = [eta(p, G, b) for b in range(p)]
    M = max(abs(v) for v in vals)
    for b in range(p):
        child1 = vals[b]
        child2 = vals[(z * b) % p]
        parent = eta(p, Gfull, b)
        total += 1
        if abs(parent) > M + 1e-8:
            exceed += 1
            prod = child1.real * child2.real
            if not (prod > -1e-7):
                print("FAIL", p, n, b, abs(parent), M, prod, child1, child2)
                fail += 1
print(f"cases={len(cases)} total_freq={total} exceed={exceed} fails={fail}")
assert fail == 0
