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
print("READING: if E2(n)/E2(n/2)->8 (E2~c*n^3) and E3(n)/E3(n/2)->32 (E3~c*n^5), then")
print("A_3/A_2 ~ E3/E2 ~ c'*n^2, and g(2)=(A_3/A_2)/(5n) ~ c'*n/5 -- but MEASURED g(2)->1, so the")
print("leading n^3,n^5 coefficients must conspire so E3/E2 -> 5n EXACTLY in the limit (the step equality).")
print("The exact E2,E3 polynomials in n pin whether L=1 is exact (a formalizable asymptotic equality).")
