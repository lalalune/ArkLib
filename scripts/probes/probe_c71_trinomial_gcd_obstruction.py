#!/usr/bin/env python3
"""Exact C71 trinomial gcd-obstruction probe.

Shows the smallest explicit failure of the tempting trinomial analog
  incidence <= gcd(i-j, j-k, n)
on a proper thin 2-power subgroup: n=8, p=17, f=X^2-X-2.
The two roots 2 and -1 lie in mu_8(F_17), while gcd(1,1,8)=1.
"""
from math import gcd

p = 17
n = 8
i, j, k = 2, 1, 0
c1, c2 = 1, 2
mu = [x for x in range(1, p) if pow(x, n, p) == 1]
roots = [x for x in mu if (pow(x, i, p) - c1 * pow(x, j, p) - c2 * pow(x, k, p)) % p == 0]
gap_gcd = gcd(i - j, gcd(j - k, n))
print(f"p={p} n={n} mu_n={mu}")
print(f"f=X^{i}-{c1}*X^{j}-{c2}*X^{k}; roots_in_mu={roots}; count={len(roots)}")
print(f"gap_gcd=gcd({i-j},{j-k},{n})={gap_gcd}")
if not (len(roots) == 2 and set(roots) == {2, 16} and gap_gcd == 1 and len(roots) > gap_gcd):
    raise SystemExit("FAIL: obstruction not reproduced")
print("PASS: trinomial gap-gcd cap fails exactly (2 roots > gcd 1)")
