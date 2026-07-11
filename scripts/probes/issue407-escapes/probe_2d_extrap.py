#!/usr/bin/env python3
"""
#407 prize-regime JOINT-LIMIT extrapolation. The prize is the (n->inf, m->inf) corner
(n=2^30, m=2^128). Prior probes covered only edges: const-index (m small fixed, n grows)
and v2-gating (m grows with n). Here: full 2D grid R(n,m)=M(n)/sqrt(n log m) over reachable
(n=2^mu, index m), fit  log R = a + b*log2(n) + c*log2(m) + d*log2(n)*log2(m), and report the
EFFECTIVE n-slope  dR-exponent/d log2(n) = b + d*log2(m)  AT LARGE m. If it stays <= 0 as m grows,
the floor survives the joint limit; if it turns positive at large m, BGK bites in the corner.
"""
import numpy as np
from sympy import isprime

def Mmax(p, n):
    g = 2
    # primitive root
    fac = set(); x = p - 1; d = 2
    while d * d <= x:
        while x % d == 0: fac.add(d); x //= d
        d += 1
    if x > 1: fac.add(x)
    while not all(pow(g, (p - 1) // q, p) != 1 for q in fac): g += 1
    h = pow(g, (p - 1) // n, p)
    ind = np.zeros(p); cur = 1
    for _ in range(n): ind[cur] = 1.0; cur = cur * h % p
    F = np.abs(np.fft.rfft(ind)); F[0] = -1.0
    return F.max()

rows = []  # (log2 n, log2 m, log R)
for mu in range(3, 18):
    n = 1 << mu
    # sweep index m so p=n*m+1 prime, m from 2 up, a few per n, p<=8e6
    got = 0
    for m in range(2, 4_000_000):
        p = n * m + 1
        if p > 8_000_000: break
        if not isprime(p): continue
        M = Mmax(p, n)
        R = M / np.sqrt(n * np.log(max(m, 2)))
        rows.append((mu, np.log2(m), np.log(R)))
        got += 1
        # sample geometrically in m: skip ahead
        if got >= 12: break
        m_skip = int(m * 1.6)
        # advance loop by jumping (handled by continue scanning; cheap)
    # also ensure a few large-m points
print(f"collected {len(rows)} (n,m) points")
A = np.array([[1, mu, lm, mu * lm] for (mu, lm, _) in rows])
y = np.array([lr for (_, _, lr) in rows])
coef, *_ = np.linalg.lstsq(A, y, rcond=None)
a, b, c, d = coef
print(f"fit: log R = {a:+.4f} {b:+.4f}*log2 n {c:+.4f}*log2 m {d:+.5f}*log2 n*log2 m")
print(f"   (R = M/sqrt(n log m); log here is natural log of R)")
print("\nEffective n-slope of (log R)  =  b + d*log2(m)  at various m:")
for log2m in [1, 4, 8, 16, 32, 64, 128]:
    slope = b + d * log2m
    print(f"   log2 m={log2m:>4} (m=2^{log2m}): d(logR)/d(log2 n) = {slope:+.5f}  => {'R GROWS in n (BGK bites)' if slope>0.005 else 'R flat/decreasing in n (floor holds)'}")
print("\nPRIZE corner: n=2^30, m=2^128.  Verdict driven by sign of (b + d*128).")
print("Caveat: extrapolation in log2 m from <=22 to 128 is a long reach; trend only.")
