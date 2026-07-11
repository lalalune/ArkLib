#!/usr/bin/env python3
"""
probe_407_step_at_rstar_n128.py  (#444 -- EXACT-INTEGER low-r additive-energy n-trend, thin n=32..256)

THE open content (DISPROOF_LOG '★ SHARPENING'/'⚠️ TEMPERING'): the surviving thin-essential lever is the
moment-ratio STEP  A_{r+1}/A_r <= (2r+1)*n  at r*=round(log p). The FFT-measured g(r*) stalled at n=64
(size-p FFT infeasible/slow). This gives a RIGOROUS EXACT-INTEGER companion at LOW r (r=2,3,4), extensible
to n=128, 256, via the in-tree identity Sum_b |eta_b|^{2r} = p*E_r(mu_n), E_r = r-fold additive energy.
The early-r step g(r) and its n-trend test the SAME monotone-increasing-in-n phenomenon at rungs we can
prove exactly. This complements (does not replace) the deep-r FFT data; honest scope = low r only.

E_r(mu_n) = #{(x_1..x_r),(y_1..y_r) in mu_n^{2r} : sum x = sum y} = Sum_t r_r(t)^2,
  r_r(t) = #{r-tuples (with order, from mu_n) summing to t mod p}.
We build r_r exactly by nested histogram convolution in EXACT integer arithmetic (dense dict), only for
r small enough that the cost C(n,*)~n^r is feasible: r<=4 for n<=64, r<=3 for n<=256.
A_r := E_r - n^{2r}/p (DC-subtracted). STEP g(r) = (A_{r+1}/A_r)/((2r+1)n) < 1 iff the step holds.
PROPER thin mu_n (2-power subgroup, m=(p-1)/n>1, p~n^4, NEVER n=q-1).
"""
import math
from collections import Counter

import sympy

def is_prime(m):
    return bool(sympy.isprime(m))

def primroot(p):
    return int(sympy.primitive_root(p))

def roots(n, p):
    g = primroot(p); w = pow(g, (p - 1) // n, p)
    assert pow(w, n, p) == 1 and all(pow(w, d, p) != 1 for d in range(1, n))
    return [pow(w, i, p) for i in range(n)]

def find_prime(n, beta):
    target = int(n ** beta); m = max(1, target // n); best = None
    while True:
        p = m * n + 1
        if p > target * 1.4: break
        if p >= target * 0.7 and is_prime(p):
            if best is None or abs(p - target) < abs(best - target): best = p
        m += 1
    return best

def energy_lowr(n, p, rmax):
    """E_r for r=1..rmax via exact dense convolution of the ordered r-tuple sum histogram."""
    base = roots(n, p)
    h = {0: 1}      # r=0
    E = {}
    for r in range(1, rmax + 1):
        nh = Counter()
        for t, c in h.items():
            for x in base:
                nh[(t + x) % p] += c
        h = nh
        E[r] = sum(c * c for c in h.values())
    return E

def run(n, rmax):
    p = find_prime(n, 4.0)
    if not p:
        print(f"n={n}: no prime"); return
    be = math.log(p) / math.log(n)
    E = energy_lowr(n, p, rmax)
    def Ar(r): return E[r] - (n ** (2 * r)) / p
    line = [f"n={n:>4} p={p:>11} beta={be:.2f}"]
    gs = {}
    for r in range(2, rmax):
        a, a1 = Ar(r), Ar(r + 1)
        g = (a1 / a) / ((2 * r + 1) * n)
        gs[r] = g
    print("  ".join(line), flush=True)
    for r in range(2, rmax):
        if r in gs:
            print(f"      r={r}: E_r={E[r]:<14d} E_{{r+1}}={E[r+1]:<16d} "
                  f"A_{{r+1}}/A_r={ (Ar(r+1)/Ar(r)):.4f}  g(r)={gs[r]:.4f}", flush=True)
    return gs

print("=" * 84)
print("EXACT-INTEGER low-r additive-energy STEP trend (thin 2-power mu_n, beta~4). g(r)<1 = step holds.")
print("Tests the monotone-increasing-in-n step margin at provable low rungs; extends to n=128, 256.")
print("=" * 84)
allg = {}
for n, rmax in [(32, 5), (64, 4), (128, 3)]:
    allg[n] = run(n, rmax)
print("=" * 84)
print("n-TREND of g(r) at FIXED r (does the step margin increase then DECELERATE in n?):")
for r in [2, 3]:
    row = []
    for n in [32, 64, 128]:
        g = allg.get(n, {}).get(r)
        row.append(f"n={n}:{g:.4f}" if g is not None else f"n={n}:--")
    print(f"  r={r}:  " + "   ".join(row))
print("Increments g(2n)-g(n) at fixed r: SHRINKING => margin saturates (encouraging); "
      "HOLDING/GROWING => creeps toward the step bound (BGK-tight). Honest: low-r companion to deep-r FFT.")
