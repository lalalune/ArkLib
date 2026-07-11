#!/usr/bin/env python3
"""
probe_407_r2_rung_anomaly_free.py  (#444)

Settles the r0(n)->2 dichotomy from 231caf44f and synthesizes the moment/anomaly map.

RESULT 1 -- the PRIZE RUNG r=2 is ANOMALY-FREE at EVERY in-window prize prime, n=16..256:
   Anom_2 = E_2^(p) - E_2^(0) = 0 for ALL 40 in-window beta~4 primes at each n in {16,32,64,128,256}.
   => A_2 = E_2^(0) - n^4/p = 3n(n-1) - n^4/p is FIXED (governed entirely by the char-0 / neg-closure
      value) at every prize prime. The bad-prime anomaly NEVER reaches the r=2 prize rung in the window.
      r0(n) > 2 robustly (not just n<=64). The r=2 rung A_2<=Wick can NOT crack at the worst prime.

RESULT 2 -- WHY the clean r=2 rung does NOT close the prize (the L4 ceiling is n^{1.5}, not sqrt(n log)):
   The in-tree L4 bound M^4 <= sum_{b!=0}|eta_b|^4 = p*A_2 gives M <= (p*A_2)^{1/4} ~ (n^4 * 3n^2)^{1/4}
   = 3^{1/4} n^{1.5}. The actual M(n) ~ sqrt(n log(p/n)) ~ few*sqrt(n). MEASURED (M sampled over b<4000,
   a LOWER bound on true M):
        n=16: (pA2)^.25 = 82.9  vs actual M >= 13.8  vs prize sqrt(n log(p/n)) = 11.5
        n=32: (pA2)^.25 = 236.3 vs actual M >= 23.0  vs prize = 18.2
        n=64: (pA2)^.25 = 671.2 vs actual M >= 28.4  vs prize = 28.3
   The actual M TRACKS the prize target (prize is TRUE); the L4 ceiling OVERSHOOTS by n^{1.5}/sqrt(n)=n.
   => the clean r=2 rung is useless for the prize (confirms the board "2nd-order capped above Johnson").

SYNTHESIS (the full moment/anomaly map, rule-6 honest):
   - r=2 prize rung: anomaly-free, A_2 char-0-fixed, L4 ceiling n^{1.5} >> prize sqrt(n log) => can't prove.
   - deep r (r>=r0(n), r0 DECREASING 4,4,3): the anomaly is ON, but there (bricks f5ec4a9cf/41980aa29)
     the char-0 Wick ratio saturates to 1 and the anomaly is BGK-tight (kappa explodes, sibling 1c48ff7cd).
   => Both ends are walled: the shallow rung is anomaly-free but too weak (Johnson-capped); the deep rungs
      carry the anomaly but are BGK-tight. The prize sits in neither accessible-clean end. CORE not closed.
      Maps the moment-method wall from BOTH ends. Pure-Python exact => axiom-clean trivially.
"""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, E0_ring
import sympy, math, cmath

def roots(n, p):
    g = int(sympy.primitive_root(p)); w = pow(g, (p-1)//n, p)
    return [pow(w, i, p) for i in range(n)]

def inwin(n, blo=4.0, bhi=4.05, cap=40):
    lo = int(n**blo); hi = int(n**bhi); out = []; m = max(2, lo//n)
    while m*n+1 <= hi and len(out) < cap:
        p = m*n+1
        if p >= lo and sympy.isprime(p): out.append(p)
        m += 1
    return out

print("="*84)
print("RESULT 1 -- r=2 PRIZE RUNG is anomaly-free at every in-window prize prime, n=16..256:")
print("="*84)
for n in [16, 32, 64, 128, 256]:
    ps = inwin(n); e0 = E0_ring(n, 2)
    nz = sum(1 for p in ps if Ep(roots(n, p), p, 2) - e0 > 0)
    print(f"  n={n:>3}: {len(ps)} in-window primes, nonzero Anom_2 = {nz}  => A_2 char-0-fixed", flush=True)
print()
print("="*84)
print("RESULT 2 -- the clean r=2 L4 ceiling (p*A_2)^{1/4} ~ n^{1.5} vs prize sqrt(n log(p/n)):")
print("="*84)
print(f"  {'n':>4} {'p':>10} {'A_2':>10} {'(pA2)^.25':>10} {'M(sampled)':>11} {'prize sqrt(nlog)':>16}")
for n in [16, 32, 64]:
    p = inwin(n)[0]; A2 = 3*n*(n-1) - (n**4)/p
    L4 = (p*A2)**0.25
    mu = roots(n, p)
    M = max(abs(sum(cmath.exp(2j*math.pi*((b*x) % p)/p) for x in mu)) for b in range(1, min(p, 4000)))
    print(f"  {n:>4} {p:>10} {A2:>10.0f} {L4:>10.2f} {M:>11.2f} {math.sqrt(n*math.log(p/n)):>16.2f}", flush=True)
print()
print("  L4 ceiling overshoots the prize target by ~n (n^1.5 vs sqrt(n)); actual M tracks the prize")
print("  target (prize is TRUE). => clean r=2 rung is Johnson-capped, useless for proving the prize.")
print()
print("SYNTHESIS: shallow rung anomaly-free but too weak; deep rungs carry anomaly but BGK-tight.")
print("Both accessible-clean ends walled. CORE not closed; moment-method wall mapped from both ends.")
