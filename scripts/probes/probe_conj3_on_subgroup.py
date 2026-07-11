"""
PROBE (audit my LANE-1 refutation): test conj #3 exactness on the ACTUAL subgroup mu_n, not a generic set.
conj #3: A_r^char0 = Wick * prod(1-j/n)  where A_r is the subgroup energy (DC-subtracted in char-p, but
char-0 = the raw additive energy E_r since no DC term in char-0/over-Z... actually we use mod p large).

Compute E_r(mu_n) for a genuine subgroup at p >> n^(2r) (so no wraparound up to depth r => 'char-0' energy),
compare to Wick*prod(1-j/n) and to the Wick-model (2r-1)!!(n)_r.
"""
import math
from collections import Counter

def isprime(m):
    i = 2
    while i * i <= m:
        if m % i == 0:
            return False
        i += 1
    return m > 1

def subgroup(p, n):
    e = (p - 1) // n
    for c in range(2, p):
        h = pow(c, e, p)
        if pow(h, n, p) == 1 and len({pow(h, i, p) for i in range(n)}) == n:
            return [pow(h, i, p) for i in range(n)]
    return None

def add_energy_modp(S, p, r):
    c = Counter({0: 1})
    for _ in range(r):
        nc = Counter()
        for v, m in c.items():
            for x in S:
                nc[(v + x) % p] += m
        c = nc
    return sum(m * m for m in c.values())

def dfac(k):
    r = 1
    for i in range(1, 2 * k, 2):
        r *= i
    return r

def perm(n, k):
    p = 1
    for j in range(k):
        p *= (n - j)
    return p

def find_prime_big(n, R):
    base = n ** (2 * R + 1)
    p = base + 1
    while True:
        if isprime(p) and (p - 1) % n == 0:
            return p
        p += 1

print("conj #3 on the SUBGROUP: E_r(mu_n) vs Wick*prod(1-j/n) vs Wick-model (2r-1)!!(n)_r:")
for n in [4, 8]:
    R = 4
    p = find_prime_big(n, R)
    S = subgroup(p, n)
    print(f" n={n} p={p}:")
    print(f"  {'r':>2} {'E_r(sub)':>14} {'Wick*prod(1-j/n)':>17} {'(2r-1)!!(n)_r':>14} {'E/[Wick*prod]':>13}")
    for r in range(2, R + 1):
        E = add_energy_modp(S, p, r)
        wick = dfac(r) * n ** r
        prodff = 1.0
        for j in range(1, r):
            prodff *= (1 - j / n)
        wickprod = wick * prodff
        wickmodel = dfac(r) * perm(n, r)
        print(f"  {r:>2} {E:>14} {wickprod:>17.1f} {wickmodel:>14} {E/wickprod:>13.4f}")
    print()
print("If E_r(sub) ~ Wick*prod(1-j/n) (ratio ~1), conj #3 is approx TRUE for the subgroup (my generic")
print("refutation would then be about the WRONG object). If clearly != 1, refutation stands for subgroup too.")
print("Also compare E_r(sub) to (2r-1)!!(n)_r [Wick-model]: if equal, the subgroup IS the Wick-model.")
