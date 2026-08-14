#!/usr/bin/env python3
"""
t=2 OPTIMALITY (provable special case): a nonzero binomial a*X^i + b*X^j (i != j mod n) has at
most n/2 roots in mu_n (n=2^mu), with equality iff gcd(i-j,n)=n/2.

#roots in mu_n of a*X^i+b*X^j = #{x in mu_n : x^{i-j} = -b/a}.
Let d=gcd(i-j,n). The map x->x^{i-j} on mu_n has image mu_{n/d} and is d-to-1 onto its image.
So the equation has either 0 or d solutions. d=gcd(i-j,n) | n=2^mu, and i!=j mod n => d<n => d<=n/2.
Hence #roots <= n/2, with equality achievable (i-j=n/2 => d=n/2, target=-b/a a square... = the
X^{n/2}+1 binomial). VALIDATE exactly over F_p, proper mu_n.
"""
import sympy as sp


def find_prime(n):
    k = max(n**3 * 50, 2**40) // n + 1
    while True:
        p = k * n + 1
        if sp.isprime(p):
            return p
        k += 1


def binom_roots(n, i, j, a, b, p, h):
    # count x in mu_n (x=h^t) with a*x^i + b*x^j = 0
    cnt = 0
    for t in range(n):
        x = pow(h, t, p)
        if (a * pow(x, i, p) + b * pow(x, j, p)) % p == 0:
            cnt += 1
    return cnt


import math
for mu in [3, 4, 5]:
    n = 2**mu
    p = find_prime(n)
    g = int(sp.primitive_root(p))
    h = pow(g, (p - 1) // n, p)
    maxr = 0
    worst = None
    # sweep all i!=j and a few nonzero a,b
    for i in range(n):
        for j in range(n):
            if i == j:
                continue
            for (a, b) in [(1, 1), (1, 2), (3, 5)]:
                r = binom_roots(n, i, j, a, b, p, h)
                d = math.gcd(abs(i - j), n)
                # check r in {0, d}
                assert r in (0, d), "r=%d not in {0,%d} at i=%d j=%d" % (r, d, i, j)
                if r > maxr:
                    maxr = r; worst = (i, j, a, b, d)
    print("n=%2d p=%d: max binomial roots = %2d (<= n/2 = %d) at (i,j,a,b,gcd)=%s  %s" %
          (n, p, maxr, n // 2, worst, "OK" if maxr <= n // 2 else "VIOL"))
