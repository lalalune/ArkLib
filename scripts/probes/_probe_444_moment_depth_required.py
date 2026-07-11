#!/usr/bin/env python3
"""
#444 — how DEEP a moment does the prize bound require? (extends the Delsarte-LP degree-1 no-go)

The only live handle on house = M(μ_n) = max_J |η_J| is the moment method:
    house ≤ (Σ_J |η_J|^{2d})^{1/(2d)} = (E_d)^{1/(2d)}      (the degree-d ℓ^{2d}→ℓ^∞ bound)
where d=1 is Parseval (= the Delsarte-LP no-go ceiling √(p−n)), and d→∞ → house exactly.

QUESTION: for the prize bound house ≤ √(2n·ln m) to be CERTIFIED by the degree-d moment, we need
    (E_d)^{1/(2d)} ≤ √(2n·ln m)·(1+ε).
At what d* does the degree-d bound first reach √(2n ln m)? If d* GROWS (and exceeds the char-0 "clean
regime" depth where E_d ≈ char-0), the moment method provably needs moments DEEPER than any bounded
SDP/Lasserre level — i.e. EVERY bounded-degree relaxation is blind, only the full r~ln m surplus reaches
the prize. This generalizes "LP is degree-1-blind" to "degree-k SDP is blind for every fixed k".

Char-0 (circle) reference: E_d^{c0}/period ~ (2d−1)!!·n^d, so (E_d^{c0})^{1/2d}/√n ~ √((2d−1)!!^{1/d}) ~ √(2d/e).
Setting √(2d/e)·√n = √(2n ln m) ⟹ d* ≈ e·ln m. The probe checks the TRUE (char-p) depth vs this.
"""
from math import gcd, log, sqrt, factorial
import sympy
import mpmath as mp

def primitive_root(p):
    fac = sympy.factorint(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def periods(p, n, dps=50):
    mp.mp.dps = dps
    m = (p - 1) // n
    g = primitive_root(p)
    sub = set(pow(g, (m * j) % (p - 1), p) for j in range(n))
    zeta = mp.e ** (2j * mp.pi / p)
    eta = []
    for i in range(m):
        rep = pow(g, i, p)
        C = [(rep * s) % p for s in sub]
        eta.append(mp.fsum(zeta ** z for z in C))
    return m, [abs(e) for e in eta]   # |η_J|

def dblfac_odd(d):
    v = 1
    for t in range(1, d + 1):
        v *= (2 * t - 1)
    return v

CASES = [(4, 53), (8, 97), (16, 193), (16, 241), (32, 257), (32, 353)]
R = 14
print(f"{'p':>5} {'n':>3} {'m':>4} | {'house':>7} {'sqrt(2n lnm)':>11} {'ratio':>6} | "
      f"{'d* (deg to certify)':>19} {'e·lnm (c0 pred)':>14}")
print("-" * 92)
for n, p in CASES:
    if (p - 1) % n:
        continue
    m, mags = periods(p, n)
    house = float(max(mags))
    tgt = sqrt(2 * n * log(m)) if m >= 2 else float('nan')
    # degree-d bound (E_d)^{1/2d} = (Σ |η|^{2d})^{1/2d}
    dstar = None
    for d in range(1, R + 1):
        Ed = sum(mp.mpf(x) ** (2 * d) for x in mags)
        bnd = float(Ed ** (mp.mpf(1) / (2 * d)))
        if dstar is None and bnd <= tgt * 1.02:
            dstar = d
    c0pred = 2.718281828 * log(m)
    print(f"{p:>5} {n:>3} {m:>4} | {house:>7.3f} {tgt:>11.3f} {house/tgt:>6.3f} | "
          f"{str(dstar):>19} {c0pred:>14.2f}")
print("-" * 92)
print("ratio = house/√(2n lnm) (the TRUE house already obeys the prize bound, <~1).")
print("d* = least moment degree whose bound (E_d)^{1/2d} certifies house ≤ 1.02·√(2n lnm).")
print()
print("Reading: d* > 1 ALWAYS ⟹ the degree-1 LP/Parseval ceiling NEVER certifies the prize (confirms")
print("the Delsarte-LP no-go). If d* tracks e·ln m and grows with m, then NO fixed-degree SDP/Lasserre")
print("level reaches the prize — only moments of depth ~ln m do, exactly where the char-p surplus is")
print("uncontrolled = the open wall. This QUANTIFIES the moment depth the prize requires.")
