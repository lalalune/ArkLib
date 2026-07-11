import itertools, sympy
from collections import Counter

def mu_n(p, n):
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)
    return sorted({pow(h, k, p) for k in range(n)})

def rEnergy(G, r, p):
    cnt = Counter()
    for v in itertools.product(G, repeat=r):
        cnt[sum(v) % p] += 1
    return sum(c*c for c in cnt.values())

for n in [4, 8]:
    p = None
    cand = n*1000 + 1
    while p is None:
        if cand % n == 1 and sympy.isprime(cand):
            p = cand
        cand += 1
    G = mu_n(p, n)
    print(f"n={n} p={p} |G|={len(G)}")
    for r in range(1, 5):
        E = rEnergy(G, r, p)
        Gr = len(G)**r
        triv = len(G)**(2*r-1)
        print(f"  r={r}: E_r={E}  |G|^r={Gr}  |G|^(2r-1)={triv}  E/|G|^r={E/Gr:.3f}  E/|G|^(2r-1)={E/triv:.4f}")
