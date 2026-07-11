#!/usr/bin/env python3
"""The large-m frontier of the SHARP closed-form deep-band machine (#389, follow-up iv).

For each parameter shape, sweep bands m and report the deepest m where the sharp
closed-form floor V/Lam'^2 (Lam' = P//q^(m+1) + C'//q + 3, V = P*Lam'//q^m) is
(a) nonvacuous (>= 1) and (b) saturated (>= q/2). Measured law: at rate 1/2 the
saturation zone grows LINEARLY in n (m* = 8, 14, 27 at n = 128, 256, 512) -- the
concrete shape of the Theta(n H(rho)/log q) bandwidth law, now with the sharp
constant; at low rate the reach is the witness-mass cliff (m* small).
"""
from math import comb
import sys
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8")
for (n, k, q) in ((128, 2, 131), (128, 64, 131), (128, 64, 257),
                  (256, 128, 257), (256, 8, 257), (512, 256, 521)):
    mmax_nv = mmax_sat = -1
    for m in range(0, n - k - 1):
        t = k + m + 1
        if t > n:
            break
        P = comb(n, t)
        Cp = comb(t, k + 1) * comb(n - (k + 1), m)
        Lam = P // q ** (m + 1) + Cp // q + 3
        V = P * Lam // q ** m
        floor = V // Lam ** 2
        if floor >= 1:
            mmax_nv = m
        if floor >= q // 2:
            mmax_sat = m
    print(f"n={n} k={k} q={q}: nonvacuous to m={mmax_nv}, "
          f"saturated to m={mmax_sat}, bands below capacity={n-k-1}")
print("frontier mapped")
