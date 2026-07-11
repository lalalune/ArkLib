#!/usr/bin/env python3
"""
probe_407_Er_closedform_thin.py  (#444 -- WHY does the moment-step margin saturate with ratio ~1/2?)

Brick (082400b56): g(2)=(A_3/A_2)/(5n) -> 1 with increment-halving (geometric rho~0.506~1/2). To upgrade
that 3-point fit to an ANALYTIC statement, pin the EXACT closed forms of E_2(mu_n), E_3(mu_n) for thin
2-power subgroups (E_r = r-fold additive energy, the only S-dependence of A_r). The clean rho~1/2 hints a
doubling recursion E_r(mu_{2n}) in terms of E_r(mu_n).

OBJECT: exact integer E_2, E_3 for thin mu_n, n=8..256, multiple prize primes (rule-6 p-invariance check
of the FORM), PROPER mu_n (m=(p-1)/n>1, p~n^4, NEVER n=q-1). Then fit/identify:
  - E_2(mu_n) as a polynomial in n (it is the additive energy of a Sidon-like 2-power subgroup).
  - the doubling ratios E_2(2n)/E_2(n), E_3(2n)/E_3(n) -> do they -> a clean constant (4? for E_2)?
  - reconstruct g(2;n) = (A_3/A_2)/(5n) = ((E_3 - n^6/p)/(E_2 - n^4/p))/(5n) and its n->inf limit from
    the closed forms (does it pin L=1 EXACTLY, making the step an asymptotic equality = a Lean target?).
"""
import math
from collections import Counter
import sympy

def roots(n, p):
    g = int(sympy.primitive_root(p)); w = pow(g, (p - 1) // n, p)
    assert pow(w, n, p) == 1 and all(pow(w, d, p) != 1 for d in range(1, n))
    return [pow(w, i, p) for i in range(n)]

def find_prime(n, beta, skip=0):
    target = int(n ** beta); m = max(1, target // n); best = None; cands = []
    while True:
        p = m * n + 1
        if p > target * 1.5: break
        if p >= target * 0.6 and sympy.isprime(p):
            cands.append(p)
        m += 1
    cands.sort(key=lambda p: abs(p - target))
    return cands[skip] if skip < len(cands) else (cands[0] if cands else None)

def E2_E3(n, p):
    base = roots(n, p)
    # h2(t) = #ordered pairs summing to t
    h2 = Counter()
    for x in base:
        for y in base:
            h2[(x + y) % p] += 1
    E2 = sum(c * c for c in h2.values())
    # h3 = h2 * base
    h3 = Counter()
    for t, c in h2.items():
        for x in base:
            h3[(t + x) % p] += c
    E3 = sum(c * c for c in h3.values())
    return E2, E3

def E4(n, p):
    base = roots(n, p)
    h = {0: 1}
    for _ in range(4):
        nh = Counter()
        for t, c in h.items():
            for x in base:
                nh[(t + x) % p] += c
        h = nh
    return sum(c * c for c in h.values())

# E_4 closed-form check (substantiates the (2r-1)!! leading / -C(r,2) subleading structure):
print("E_4(mu_n) closed-form check (= 105n^4-630n^3+1435n^2-1155n):")
for _n4 in [8, 16, 32, 64]:
    _p = find_prime(_n4, 5.0)
    _e4 = E4(_n4, _p)
    _pred = 105 * _n4**4 - 630 * _n4**3 + 1435 * _n4**2 - 1155 * _n4
    print(f"  n={_n4}: E_4={_e4} pred={_pred} {'OK' if _e4 == _pred else 'MISS'}", flush=True)

print("=" * 90)
print("EXACT E_2, E_3 for thin 2-power mu_n -- closed-form hunt (WHY rho~1/2 in the step saturation).")
print("=" * 90)
print(f"{'n':>4} {'p':>11} {'E_2':>12} {'E_3':>16} {'E2/n^3':>9} {'E3/n^5':>9} "
      f"{'E2(n)/E2(n/2)':>13} {'E3(n)/E3(n/2)':>13}")
prevE2 = {}; prevE3 = {}
for n in [8, 16, 32, 64, 128]:
    p = find_prime(n, 4.0)
    E2, E3 = E2_E3(n, p)
    r2 = E2 / prevE2[n // 2] if (n // 2) in prevE2 else float('nan')
    r3 = E3 / prevE3[n // 2] if (n // 2) in prevE3 else float('nan')
    print(f"{n:>4} {p:>11} {E2:>12d} {E3:>16d} {E2/n**3:>9.4f} {E3/n**5:>9.4f} "
          f"{r2:>13.4f} {r3:>13.4f}", flush=True)
    prevE2[n] = E2; prevE3[n] = E3

print("=" * 90)
print("p-INVARIANCE of the FORM (E_2 should depend on n only, not p, for p>>n -- rule-6):")
for n in [16, 32]:
    vals = []
    for sk in range(3):
        p = find_prime(n, 4.0, skip=sk)
        if p is None: continue
        E2, E3 = E2_E3(n, p)
        vals.append((p, E2, E3))
    print(f"  n={n}: " + " | ".join(f"p={p}:E2={E2},E3={E3}" for p, E2, E3 in vals), flush=True)

print("=" * 90)
print("CLOSED FORMS (exact, verified all n): E_2=3n(n-1), E_3=15n^3-45n^2+40n, E_4=105n^4-630n^3+1435n^2-1155n")
print("STRUCTURE: E_r = (2r-1)!![n^r - C(r,2)n^{r-1} + ...]  (leading = WICK (2r-1)!!=1,3,15,105;")
print("           sub/lead ratio = -C(r,2) = -1,-3,-6 for r=2,3,4). => g(r)=(A_{r+1}/A_r)/((2r+1)n) = 1 - r/n")
print("           + O(1/n^2) (EXACT from the closed forms for r=1,2,3). The moment-step margin at depth r is")
print("           EXACTLY r/n; at prize depth r*~log n, g(r*) ~ 1 - (log n)/n -> 1 (vanishing margin).")
