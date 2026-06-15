#!/usr/bin/env python3
"""
#407 PRIZE-REGIME test: the defining feature of the prize is CONSTANT index m=(p-1)/n=2^128
with n -> infinity. Every prior 'R is flat ~1.3' result had m GROWING (random-like regime).
Here we fix a small constant index m and grow n=2^mu, p = n*m + 1 (when prime), and track
   R(n) = M(n) / sqrt(n * log(p/n)),   M(n)=max_{b!=0}|sum_{x in mu_n} e_p(b x)|.
If R GROWS with n at fixed m  => the constant-index regime is genuinely harder (the prize floor
is in danger / this is exactly where BGK bites). If R stays FLAT => evidence the floor survives
into the constant-index regime. This is the cleanest computable shadow of the prize regime.
m=2 gives the Fermat primes (5,17,257,65537) = the known worst structured primes.
"""
import numpy as np
from sympy import isprime

def mu_n_max(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    cur = 1; ind = np.zeros(p, dtype=np.float64)
    for _ in range(n):
        ind[cur] = 1.0; cur = (cur * h) % p
    F = np.abs(np.fft.rfft(ind)); F[0] = -1.0
    return F.max()

def primitive_root(p):
    fac = factorize(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def factorize(x):
    fs = set(); d = 2
    while d * d <= x:
        while x % d == 0: fs.add(d); x //= d
        d += 1
    if x > 1: fs.add(x)
    return fs

print(f"{'m':>4} {'mu':>3} {'n':>7} {'p':>9} {'M(n)':>9} {'R=M/sqrt(n ln(p/n))':>20} {'M/sqrt(n)':>10}")
print("-" * 70)
trend = {}
for m in [2, 4, 6, 8, 16, 32]:
    for mu in range(2, 18):
        n = 1 << mu
        p = n * m + 1
        if p > 6_000_000: break
        if not isprime(p): continue
        M = mu_n_max(p, n)
        R = M / np.sqrt(n * np.log(p / n))
        print(f"{m:>4} {mu:>3} {n:>7} {p:>9} {M:>9.2f} {R:>20.4f} {M/np.sqrt(n):>10.3f}")
        trend.setdefault(m, []).append((mu, n, R, M / np.sqrt(n)))
    print()

print("=== TREND of R vs n at FIXED constant index m (the prize regime shadow) ===")
for m in sorted(trend):
    pts = trend[m]
    if len(pts) < 2:
        print(f"  m={m}: only {len(pts)} prime(s) {[ (n,round(R,3)) for _,n,R,_ in pts]}"); continue
    mus = np.array([x[0] for x in pts]); Rs = np.array([x[2] for x in pts])
    slope = np.polyfit(mus, Rs, 1)[0]   # dR/dmu = dR per doubling of n
    print(f"  m={m}: R = {[round(R,3) for _,_,R,_ in pts]} over n={[n for _,n,_,_ in pts]}  |  dR/d(log2 n) = {slope:+.4f}")
print("\nGROWTH (slope>0, esp. accelerating) => constant-index regime harder = BGK bites = crack toward DANGER.")
print("FLAT (slope~0)  => floor plausibly survives into the prize's constant-index regime.")
