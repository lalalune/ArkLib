from sympy import primerange, primitive_root
from collections import Counter
import math

def doublefact(k):
    r = 1
    while k > 1:
        r *= k; k -= 2
    return r

def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, k, p) for k in range(n)]

def rEnergy(G, p, r):
    f = Counter({0: 1})
    for _ in range(r):
        f2 = Counter()
        for d, c in f.items():
            for s in G:
                f2[(d + s) % p] += c
        f = f2
    return sum(c * c for c in f.values())

def crossMass(G, p, r):
    n = len(G)
    return rEnergy(G, p, r + 1) - n * rEnergy(G, p, r)

cases = []
for a in range(2, 6):
    n = 2 ** a
    target = n ** 3 * 3
    p = None
    for cand in primerange(target, target * 6):
        if (cand - 1) % n == 0:
            p = cand; break
    if p:
        cases.append((n, p))

for n, p in cases:
    G = mu_n(p, n)
    assert len(G) == n
    print(f"n={n} p={p} beta={math.log(p, n):.2f}")
    for r in range(1, 5):
        Er = rEnergy(G, p, r)
        wick = doublefact(2 * r - 1) * n ** r
        cr = crossMass(G, p, r)
        bound = 2 * r * doublefact(2 * r - 1) * n ** (r + 1)
        print(f"  r={r}: E_r={Er} Wick={wick} E_r<=Wick? {Er<=wick}  | cross_r={cr} stepBnd={bound} ratio={cr/bound:.3f} ok? {cr<=bound}")
