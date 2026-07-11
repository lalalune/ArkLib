#!/usr/bin/env python3
"""Probe the single-defect FIRST-POWER deficit sandwich.

For M phases with one defect w=e^{i theta}, exact deficit is
  D = M - |(M-1)+w|.
The already-landed lower floor is L=(M-1)(1-Re w)/M.  This probe checks
  L <= D <= 2L
for M=2..256 and dense theta samples, including near-alignment.
"""
import cmath, math

worst_low = float('inf')
worst_high = 0.0
bad = []
for M in range(2, 257):
    for k in range(1, 2000):
        theta = 2*math.pi*k/2000
        w = cmath.exp(1j*theta)
        d = 1 - w.real
        L = (M-1)*d/M
        D = M - abs((M-1)+w)
        if L > D + 1e-10 or D > 2*L + 1e-10:
            bad.append((M,k,L,D,2*L))
        if L > 0:
            worst_low = min(worst_low, D/L)
            worst_high = max(worst_high, D/L)
print(f"checked M=2..256, theta grid 1999 points each")
print(f"bad={len(bad)} ratio_min={worst_low:.12f} ratio_max={worst_high:.12f}")
if bad:
    print(bad[:5])
    raise SystemExit(1)
