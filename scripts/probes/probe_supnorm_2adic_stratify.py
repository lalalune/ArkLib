#!/usr/bin/env python3
# NOVEL STRATIFICATION: is the Gauss-period sup-norm constant R = M/sqrt(n ln m) controlled by
# v2(m), the 2-adic valuation of the INDEX m=(p-1)/n?  Hypothesis (from the resonance at the
# Fermat prime p=65537, index 2^10): resonances live where the index is 2-power-rich; for ODD
# index R stays ~1.5.  THE PRIZE REGIME uses FFT primes p = k*2^mu + 1 with k odd, so n=2^mu is
# the 2-SYLOW subgroup (= the set of k-th powers, k odd), i.e. v2(index)=0.  If R is small and
# flat exactly on v2=0, the prize-faithful conjecture sharpens to the ODD-INDEX case, off the
# 2-power Stickelberger-alignment resonances.
import sympy, cmath, math

def supnorm(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    G = [pow(h, j, p) for j in range(n)]
    m = (p - 1) // n
    w = 2 * math.pi / p
    mx = 0.0; rep = 1
    for c in range(m):
        s = 0j
        for x in G:
            s += cmath.exp(1j * w * ((rep * x) % p))
        a = abs(s)
        if a > mx: mx = a
        rep = (rep * g) % p
    return mx, m

def v2(x):
    v = 0
    while x % 2 == 0:
        x //= 2; v += 1
    return v

# Bin R by v2(index). For each n, scan primes; group by v2(m).
from collections import defaultdict
print("R = M/sqrt(n ln m), binned by v2(index m).  Prize regime = v2(m)=0 (odd index, 2-Sylow).")
print(f"{'n':>5} | " + " ".join(f"v2={v}:maxR/meanR" for v in range(0, 6)))
for mu in range(4, 9):
    n = 2 ** mu
    byv = defaultdict(list)
    m = 1
    scanned = 0
    while n * m + 1 < 350000 and scanned < 500:
        p = n * m + 1
        if sympy.isprime(p):
            M, mm = supnorm(n, p)
            if mm >= 2:
                R = M / math.sqrt(n * math.log(mm))
                byv[v2(mm)].append(R)
            scanned += 1
        m += 1
    cells = []
    for v in range(0, 6):
        if byv[v]:
            cells.append(f"{max(byv[v]):.2f}/{sum(byv[v])/len(byv[v]):.2f}(#{len(byv[v])})")
        else:
            cells.append("   --   ")
    print(f"{n:>5} | " + " ".join(cells))

print()
print("CONTROL: explicit ODD-INDEX (2-Sylow) check on real-FFT-prime-style p = k*2^mu+1, k odd.")
print(f"{'n=2^mu':>8}{'k(odd)':>9}{'p':>12}{'M/sqrtn':>9}{'R':>8}")
for mu in [4,5,6,7,8]:
    n = 2**mu
    # find a few primes p = k*2^mu+1 with k odd
    found = 0
    k = 1
    while found < 2 and k < 4000:
        if k % 2 == 1:
            p = k * n + 1
            if sympy.isprime(p) and p > n*8:
                M, mm = supnorm(n, p)
                R = M / math.sqrt(n*math.log(mm))
                print(f"{n:>8}{k:>9}{p:>12}{M/math.sqrt(n):>9.3f}{R:>8.3f}")
                found += 1
        k += 1
