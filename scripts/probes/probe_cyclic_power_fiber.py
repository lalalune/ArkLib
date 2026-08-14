#!/usr/bin/env python3
"""Probe: in F_p^* (cyclic order p-1), the m-th power map (m=(p-1)/n) is uniformly
gcd(p-1,m)-to-1 onto its image, image = mu_n (subgroup of order n), 0 off image.
Prize regime: n=2^a, p prime, p == 1 mod n, p >> n^3 (Fermat-type incl.). ONE sweep."""
from sympy import isprime
from math import gcd
from collections import Counter

fails = 0
tot = 0
cases = []
for a in range(2, 7):
    n = 2 ** a
    plist = []
    x = max(n * ((n ** 3) // n + 1) + 1, n + 1)
    while len(plist) < 3:
        if x % n == 1 and isprime(x):
            plist.append(x)
        x += n
    for fp in (257, 65537):
        if (fp - 1) % n == 0 and fp not in plist:
            plist.append(fp)
    for p in plist:
        m = (p - 1) // n
        g = gcd(p - 1, m)
        fib = Counter(pow(x, m, p) for x in range(1, p))
        mu = set(pow(x, (p - 1) // n, p) for x in range(1, p))
        img = set(fib.keys())
        okA = all(v == g for v in fib.values())
        okB = (img == mu) and (len(mu) == n)
        okC = (g == m)
        tot += 1
        if not (okA and okB and okC):
            fails += 1
            cases.append((n, p, m, g, len(img), len(mu), okA, okB, okC))
        else:
            cases.append((n, p, m, g, 'OK'))
for c in cases[:18]:
    print(c)
print("\nTOTAL %d  FAILS %d" % (tot, fails))
if fails == 0:
    print("VERDICT: m-th power map on F_p^* is uniformly m-to-1 onto mu_n (order n); gcd(p-1,m)=m.")
else:
    print("VIOLATION")
