from sympy import primerange, primitive_root
from collections import Counter
import numpy as np

def mu_n(p, n):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    return [pow(h, k, p) for k in range(n)]

def rEnergy(G, p, r):
    # E_r = sum over d of (number of r-fold sums from G equal to d)^2
    f = Counter({0: 1})
    for _ in range(r):
        f2 = Counter()
        for d, c in f.items():
            for s in G:
                f2[(d + s) % p] += c
        f = f2
    return sum(c * c for c in f.values())

# Known exact: E_1=n, E_2=3n^2-3n, E_3=15n^3-45n^2+40n.
# Leading coeffs (2r-1)!! = 1,3,15,105 -> E_4 leading = 105 n^4.
# Probe-first: PROPER mu_n, n=2^a, p >> n^6 (char-0 faithful for r=4), multi-prime, NEVER n=q-1.
print("PROBE E_4 on PROPER mu_n, n=2^a, p>>n^6, multi-prime, NEVER n=q-1")
print("n     E4                105n^4            diff=E4-105n^4     primes  consistent")
data = []
for a in range(2, 7):
    n = 2 ** a
    target = n ** 6
    ps = []
    for c in primerange(target, target * 6):
        if (c - 1) % n == 0:
            ps.append(c)
            if len(ps) >= 2:
                break
    if not ps:
        continue
    vals = [rEnergy(mu_n(p, n), p, 4) for p in ps]
    consistent = len(set(vals)) == 1
    E4 = vals[0]
    diff = E4 - 105 * n ** 4
    data.append((n, E4, diff))
    print(f"{n:<5} {E4:<17} {105*n**4:<17} {diff:<17} {ps} {consistent}")

if len(data) >= 4:
    ns = np.array([d[0] for d in data], dtype=float)
    diffs = np.array([d[2] for d in data], dtype=float)
    A = np.vstack([ns ** 3, ns ** 2, ns]).T
    coef, res, _, _ = np.linalg.lstsq(A, diffs, rcond=None)
    print(f"\nfit diff = E4-105n^4 ~ {coef[0]:.4f} n^3 + {coef[1]:.4f} n^2 + {coef[2]:.4f} n")
    rc = [round(x) for x in coef]
    print(f"rounded: E_4 = 105 n^4 + ({rc[0]}) n^3 + ({rc[1]}) n^2 + ({rc[2]}) n")
    ok = all(abs(d[1] - (105 * d[0] ** 4 + rc[0] * d[0] ** 3 + rc[1] * d[0] ** 2 + rc[2] * d[0])) < 1e-6 for d in data)
    print(f"EXACT match all n: {ok}")

    # Now: does E_4 discharge the r=3 cross-step rung?
    # crossMass G 3 = E_4 - n*E_3, target bound 2*3*(2*3-1)!!*n^4 = 6*15*n^4 = 90 n^4.
    print("\n--- r=3 cross-step rung check: crossMass G 3 = E_4 - n*E_3 <= 90 n^4 ? ---")
    def E3(n): return 15*n**3 - 45*n**2 + 40*n
    def E4f(n): return 105*n**4 + rc[0]*n**3 + rc[1]*n**2 + rc[2]*n
    print("n     crossMass3       90n^4            ratio")
    for d in data:
        n = int(d[0])
        cm = E4f(n) - n * E3(n)
        print(f"{n:<5} {cm:<17} {90*n**4:<17} {cm/(90*n**4):.4f}")
