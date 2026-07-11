#!/usr/bin/env python3
from math import gcd

def is_prime(p):
    if p < 2:
        return False
    d = 2
    while d * d <= p:
        if p % d == 0:
            return False
        d += 1
    return True

def order_mod(x, p):
    x %= p
    if x == 0:
        return 0
    y = 1
    for k in range(1, p):
        y = y * x % p
        if y == 1:
            return k
    return 0

def inv_mod(a, n):
    for b in range(n):
        if (a * b) % n == 1 % n:
            return b
    return None

cases = []
for n in [8, 16, 32, 64]:
    for r in range(4, 10):
        for p in range(n * 2 + 1, min(200000, max(n ** 4 // 2, n * 3000)), n):
            if not is_prime(p):
                continue
            if (p - 1) % n:
                continue
            if order_mod(-r, p) != n:
                continue
            for a in range(1, n):
                if gcd(a, n) != 1:
                    continue
                b = inv_mod(a, n)
                g = pow(-r, b, p)
                ok = (
                    order_mod(g, p) == n
                    and pow(g, a, p) == (-r) % p
                    and (r - (r - 1) * pow(g, a, p) - pow(g, 2 * a, p)) % p == 0
                )
                if not ok:
                    raise SystemExit(
                        f"FAIL n={n} r={r} p={p} a={a} b={b} g={g} ordg={order_mod(g,p)}"
                    )
            cases.append((n, r, p))
            break
print(f"PASS char-p general inverse root-lift: {len(cases)} carrier primes checked, proper dyadic n only")
print(cases[:20])
