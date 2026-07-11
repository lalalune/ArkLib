#!/usr/bin/env python3
"""
Elementary-symmetric confinement count (p=12289, mu_16).

The factor confinement (RungClassFamily): all class factor products
Phi_j = m_{A_j} h_j lie in one 3-dim coset (pairwise diff deg < 3). In the
D = a case (h_j constant), Phi_j = c * m_{A_j}, so the monic vanishing
polys m_{A_j} pairwise agree in ALL coefficients from index 3 upward -
i.e. the agreement sets A_j (size a) share the top (a-3) elementary
symmetric functions of their roots, differing only in e_{a-2}, e_{a-1},
e_a (the bottom 3 coeffs).

This probe: for a-subsets of mu_16 (a = 5,6,7,8), how many share the most
common top-symmetric profile (e_1..e_{a-3})? That count = max number of
size-a classes coexisting in the D=a regime; cap n-a each, so the
contribution is (count)*(16-a). If small, the sum bound closes.
Also: do the record-22 stack's two big agreement sets actually share their
(e1,e2,e3)? (validates the mechanism applies to the real extremal).
"""
import itertools
from collections import Counter

p, n = 12289, 16
g0 = next(g for g in range(2, 500)
          if all(pow(g, (p - 1) // f, p) != 1 for f in (2, 3)))
w = pow(g0, (p - 1) // n, p)
D = [pow(w, j, p) for j in range(n)]

def esym(roots):
    """elementary symmetric e_1..e_len of the roots (mod p), as a tuple."""
    # coeffs of prod (x - r): poly[k] = coeff of x^k
    poly = [1]
    for r in roots:
        poly = [(poly[i] - r * (poly[i-1] if i-1 >= 0 else 0)) % p
                if i < len(poly) else (-r * poly[i-1]) % p
                for i in range(len(poly) + 1)]
    a = len(roots)
    # e_j = (-1)^j * coeff of x^{a-j}; we want top ones e_1..e_{a-3}
    # poly[a-j] is coeff of x^{a-j}; e_j = (-1)^j poly[a-j]
    return tuple(((-1)**j * poly[a - j]) % p for j in range(1, a + 1))

for a in (5, 6, 7, 8):
    topk = a - 3  # number of top e's that must match (e_1..e_{a-3})
    profiles = Counter()
    for sub in itertools.combinations(range(n), a):
        roots = [D[i] for i in sub]
        e = esym(roots)
        profiles[e[:topk]] += 1
    mx = max(profiles.values())
    # how many distinct profiles hit the max; distribution tail
    dist = Counter(profiles.values())
    contribution = mx * (n - a)
    print(f"a={a}: top-{topk}-esym profiles, max coincidence = {mx} "
          f"(=> up to {mx} size-{a} classes, contribution {contribution}); "
          f"profile-count distribution tail: "
          f"{sorted(dist.items(), reverse=True)[:4]}")

# validate on the record stack's two big blocks A1={0..5}, A2={6..11}
A1 = list(range(6)); A2 = list(range(6, 12))
e1 = esym([D[i] for i in A1])[:3]
e2 = esym([D[i] for i in A2])[:3]
print(f"record-22 big blocks: A1 top-3-esym {e1}, A2 top-3-esym {e2}, "
      f"share = {e1 == e2}")
