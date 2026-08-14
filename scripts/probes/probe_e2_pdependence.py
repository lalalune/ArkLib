"""
AUDIT (codex caught this): is E_2(mu_n) = 3n^2-3n universal, or p-dependent / n-dependent?
Codex showed: n=3 gives 15 not 18; small p gives larger E_2. Investigate.
"""
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

# scan multiple primes per n, see if E_2 stabilizes and to what value
print("E_2(mu_n) across primes (n | p-1), vs 3n^2-3n and 2n^2-n:")
for n in [3, 4, 5, 6, 8, 16]:
    vals = []
    p = n + 1
    cnt = 0
    while cnt < 8 and p < 5_000_000:
        if isprime(p) and (p - 1) % n == 0:
            S = subgroup(p, n)
            if S:
                vals.append((p, add_energy_modp(S, p, 2)))
                cnt += 1
        p += 1
    big = vals[-3:]
    print(f" n={n}: 2n^2-n={2*n*n-n}, 3n^2-3n={3*n*n-3*n}; E_2 at largest primes {[(p,e) for p,e in big]}")
print()
print("If E_2 stabilizes to 3n^2-3n only for n a power of 2 (or n>=4), or never for n=3,5, then the")
print("'3n^2-3n' anchor is REGIME/structure-specific, NOT a universal subgroup identity. Record honestly.")
