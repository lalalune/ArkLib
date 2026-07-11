import math

def find_prime_1modn(n, lo):
    p = ((lo + n - 1)//n)*n + 1
    while True:
        if p > 1 and all(p % d for d in range(2, int(p**0.5)+1)):
            return p
        p += n

def primroot(p):
    fac = set()
    mm = p-1
    d = 2
    while d*d <= mm:
        while mm % d == 0:
            fac.add(d); mm //= d
        d += 1
    if mm > 1:
        fac.add(mm)
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in fac):
            return g
    return None

def mu_n(n, p):
    g = primroot(p)
    h = pow(g, (p-1)//n, p)
    return [pow(h, t, p) for t in range(n)]

cases = 0
ok = 0
sharper = 0
for a in [2, 3, 4]:
    n = 2**a
    primes = []
    primes.append(find_prime_1modn(n, 73))
    primes.append(find_prime_1modn(n, n**3 + 1))
    for c0 in [17, 257, 65537]:
        if (c0 - 1) % n == 0:
            primes.append(c0)
            break
    for p in primes:
        if p % n != 1:
            continue
        if n == p - 1:
            continue  # NEVER full group
        G = mu_n(n, p)
        if len(set(G)) != n:
            continue
        for i in range(1, n):
            for j in range(0, i):
                d = i - j
                gd = math.gcd(d, n)
                for c in G:
                    cnt = sum(1 for x in G if x != 0 and (pow(x, i, p) - (c*pow(x, j, p))) % p == 0)
                    cases += 1
                    if cnt in (0, gd):
                        ok += 1
                    else:
                        print("VIOLATION n=%d p=%d i=%d j=%d d=%d gcd=%d cnt=%d" % (n, p, i, j, d, gd, cnt))
                    if cnt > 0 and gd < d:
                        sharper += 1

print("cases=%d ok=%d gcd-law-holds=%s rows-where-gcd<d=%d" % (cases, ok, ok == cases, sharper))
