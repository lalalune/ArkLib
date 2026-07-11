#!/usr/bin/env python3
"""Falsifiable sign over E3RouteBridge.e3_routes_agree (#444).

The bridge claims  (negSymCount G 6 : Z) = balancedCount 6 m   for |G| = 2m, char 0.
negSymCount and balancedCount both count NEGATION-SYMMETRIC (antipodally count-balanced)
6-tuples. Two precise, independent checks:

  (1) BRIDGE (holds for ALL m): balancedCount(6,m) [convolution]
        == 15(2m)^3 - 45(2m)^2 + 40(2m) [strata closed form].

  (2) LAM-LEUNG SCOPE (holds only for 2-POWER n=2m): the negation-symmetric count
        == the DIRECT zero-sum count E_3(mu_n). For non-2-power n (e.g. n=6) the direct
        count is strictly LARGER (extra non-antipodal zero-sums, e.g. double 3-cycles),
        which is exactly why the bridge is char-0 / 2-power and NOT the char-p prize.
"""
from math import comb
from itertools import product

def balancedCount(k, m):
    if m == 0:
        return 1 if k == 0 else 0
    return sum(comb(k, 2*j) * comb(2*j, j) * balancedCount(k - 2*j, m - 1)
              for j in range(k // 2 + 1))

def strata(m):
    n = 2 * m
    return 15*n**3 - 45*n**2 + 40*n

def first_prime_one_mod(n, lo=1000):
    def isprime(x):
        i = 2
        while i*i <= x:
            if x % i == 0: return False
            i += 1
        return x > 1
    p = lo
    while not ((p - 1) % n == 0 and isprime(p)): p += 1
    return p

def e3_direct(m):
    n = 2 * m
    p = first_prime_one_mod(n)
    g = next(a for a in range(2, p)
             if pow(a, n, p) == 1 and len({pow(a, i, p) for i in range(n)}) == n)
    roots = [pow(g, i, p) for i in range(n)]
    return sum(1 for t in product(roots, repeat=6) if sum(t) % p == 0)

def is_pow2(n):
    return n & (n - 1) == 0

ok = True
print("(1) BRIDGE  balancedCount(6,m) == strata closed form  [must hold for all m]")
print(f"{'m':>3} {'conv':>10} {'strata':>10}  verdict")
for m in range(1, 7):
    c, s = balancedCount(6, m), strata(m)
    match = (c == s); ok = ok and match
    print(f"{m:>3} {c:>10} {s:>10}  {'OK' if match else 'MISMATCH'}")

print()
print("(2) SCOPE  neg-symmetric count vs direct E_3(mu_n)  [equal iff n=2m is a 2-power]")
print(f"{'m':>3} {'n':>3} {'2pow?':>6} {'conv':>10} {'directE3':>10}  verdict")
for m in [1, 2, 3, 4]:
    n = 2*m; c = balancedCount(6, m); d = e3_direct(m); pw = is_pow2(n)
    # 2-power: equal; non-2-power: direct strictly larger (extra non-antipodal zero-sums)
    good = (c == d) if pw else (d > c)
    ok = ok and good
    tag = ('EQ-OK' if c == d else 'gap') if pw else ('gap-OK' if d > c else 'UNEXPECTED-EQ')
    print(f"{m:>3} {n:>3} {str(pw):>6} {c:>10} {d:>10}  {tag}")

print()
print("ALL SIGNS GREEN" if ok else "A SIGN FAILED")
import sys; sys.exit(0 if ok else 1)
