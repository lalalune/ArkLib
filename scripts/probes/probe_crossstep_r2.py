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

# r=2 rung of M3CrossStepBound: cross_2 = E_3 - n*E_2 <= 2*2*(2*2-1)!!*n^3 = 4*3*n^3 = 12 n^3
# Question: does this follow from E_2 <= 3n^2 (Sidon, proven) and E_3 <= 15n^3 (RepThree)?
# cross_2 = E_3 - n*E_2.  Upper bound cross_2 <= E_3 <= 15n^3 -- but stepBound = 12n^3 < 15n^3.
# So cross_2 <= E_3 alone is NOT enough; we need the n*E_2 subtraction.
# cross_2 <= 15n^3 - n*E_2.  Need n*E_2 >= 3n^3 i.e. E_2 >= 3n^2. But E_2 = 3n^2-3n < 3n^2.
# So n*E_2 = 3n^3 - 3n^2, giving cross_2 <= 15n^3 - (3n^3-3n^2) = 12n^3 + 3n^2. SLIGHTLY OVER 12n^3.
# => the r=2 rung does NOT follow cleanly from the loose E_3<=15n^3 + E_2 ceilings. Need exact-ish.
# Measure the truth + the gap.

for a in range(2, 6):
    n = 2 ** a
    target = n ** 4 * 2  # bigger prime to keep E_3 char-0 faithful
    p = None
    for cand in primerange(target, target * 8):
        if (cand - 1) % n == 0:
            p = cand; break
    if not p:
        continue
    G = mu_n(p, n)
    E2 = rEnergy(G, p, 2)
    E3 = rEnergy(G, p, 3)
    cross2 = E3 - n * E2
    stepBound = 2 * 2 * doublefact(3) * n ** 3  # = 12 n^3
    # the loose composite bound from E3<=15n^3, E2 actual:
    looseTop = 15 * n ** 3 - n * E2
    print(f"n={n} p={p} beta={math.log(p,n):.2f}: E2={E2} (Sidon 3n^2-3n={3*n*n-3*n}) E3={E3} (15n^3={15*n**3})")
    print(f"   cross_2={cross2}  stepBound(12n^3)={stepBound}  cross_2<=12n^3? {cross2<=stepBound}  ratio={cross2/stepBound:.4f}")
    print(f"   E3-n*E2 via ceilings <= 15n^3 - n*E2 = {looseTop} (ratio to 12n^3 = {looseTop/stepBound:.4f})")
