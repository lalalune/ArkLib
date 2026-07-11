from collections import Counter

def isprime(n):
    if n < 2:
        return False
    i = 2
    while i * i <= n:
        if n % i == 0:
            return False
        i += 1
    return True

def mu_n(p, n):
    def order(x):
        o = 1
        v = x % p
        while v != 1:
            v = (v * x) % p
            o += 1
        return o
    g = None
    for cand in range(2, p):
        if order(cand) == p - 1:
            g = cand
            break
    h = pow(g, (p - 1) // n, p)
    S = set()
    x = 1
    for _ in range(n):
        S.add(x)
        x = (x * h) % p
    return sorted(S)

def rEnergy3(p, n):
    S = mu_n(p, n)
    cnt = Counter()
    for a in S:
        for b in S:
            ab = (a + b) % p
            for c in S:
                cnt[(ab + c) % p] += 1
    return sum(v * v for v in cnt.values())

def formula(n):
    return 15 * n**3 - 45 * n**2 + 40 * n

tests = []
for a in [2, 3, 4]:
    n = 2**a
    found = 0
    p = ((n**3) // n + 1) * n + 1
    while found < 3:
        if isprime(p) and (p - 1) % n == 0:
            tests.append((p, n))
            found += 1
        p += n
for p, n in [(17, 8), (257, 8), (257, 16), (65537, 16)]:
    if isprime(p) and (p - 1) % n == 0:
        tests.append((p, n))

print("%4s %8s %12s %16s %6s %6s" % ("n", "p", "rEnergy3", "15n^3-45n^2+40n", "match", "p>n^3"))
for p, n in tests:
    if p > 100000:
        continue
    re3 = rEnergy3(p, n)
    f = formula(n)
    ge = re3 >= f
    print("%4d %8d %12d %16d %6s %6s %6s" % (n, p, re3, f, str(re3 == f), str(re3 >= f), str(p > n**3)))
