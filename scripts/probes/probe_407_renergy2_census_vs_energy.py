import math
from itertools import product
from collections import Counter

def isprime(x):
    if x < 2:
        return False
    d = 2
    while d * d <= x:
        if x % d == 0:
            return False
        d += 1
    return True

def primitive_root(p):
    if p == 2:
        return 1
    phi = p - 1
    facs = set()
    m = phi
    d = 2
    while d * d <= m:
        while m % d == 0:
            facs.add(d)
            m //= d
        d += 1
    if m > 1:
        facs.add(m)
    for g in range(2, p):
        if all(pow(g, phi // f, p) != 1 for f in facs):
            return g
    return None

def muN(p, n):
    g = primitive_root(p)
    e = (p - 1) // n
    base = pow(g, e, p)
    s = set()
    x = 1
    for _ in range(n):
        s.add(x)
        x = x * base % p
    return sorted(s)

def zerosum_census(G, r, p):
    cnt = 0
    for tup in product(G, repeat=r):
        if sum(tup) % p == 0:
            cnt += 1
    return cnt

def add_energy(G, p):
    cs = Counter((a + b) % p for a in G for b in G)
    return sum(v * v for v in cs.values())

cases = [(4, 521), (4, 4129), (8, 4129), (8, 8273), (16, 65537)]
for n, p in cases:
    if not isprime(p) or (p - 1) % n != 0:
        print(f"skip n={n} p={p} (need prime, n|p-1)")
        continue
    G = muN(p, n)
    assert len(G) == n, (n, len(G))
    if n == p - 1:
        print("SKIP full group")
        continue
    E = add_energy(G, p)
    expect = 3 * n * n - 3 * n
    W4 = zerosum_census(G, 4, p)
    beta = math.log(p) / math.log(n)
    # negation closure check
    Gset = set(G)
    negclosed = all((p - x) % p in Gset for x in G)
    print(f"n={n:3d} p={p:7d} beta={beta:.2f}  E={E}  3n^2-3n={expect}  W4={W4}  E==expect:{E==expect}  W4==E:{W4==E}  negclosed:{negclosed}")
