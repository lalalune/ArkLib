#!/usr/bin/env python3
# Probe: the explicit M~sqrt(q) instantiation of weil_stepanov_card_le_one.
# Proven in tree:  |V| <= D0 // M   where D0 = ((q-1)//2)*d + (q-1)  (Nat floor division),
# under |V|*M < 2*(A+1), 2A+d<q.  Goal: cleanest explicit closed form at M = isqrt(q),
# valid for ALL odd q (prize regime q = n^beta, n = 2^a) and ALL d>=1.
import math

def D0(q, d):
    return ((q - 1) // 2) * d + (q - 1)

worst_ratio = 0.0
fails_dp2_sq = []      # candidate: D0 // isqrt q <= (d+2)*isqrt q
fails_dp2_sqp1 = []    # candidate: D0 // isqrt q <= (d+2)*(isqrt q + 1)
for q in range(3, 200001, 2):       # odd q only
    sq = math.isqrt(q)
    if sq == 0:
        continue
    for d in range(1, 40):
        rhs = D0(q, d) // sq                       # the proven divided-bound VALUE
        if rhs > (d + 2) * sq:
            fails_dp2_sq.append((q, d, rhs, (d + 2) * sq))
        if rhs > (d + 2) * (sq + 1):
            fails_dp2_sqp1.append((q, d, rhs, (d + 2) * (sq + 1)))
        target = (d / 2.0) * math.sqrt(q)          # classical (d/2) sqrt q
        worst_ratio = max(worst_ratio, rhs / target if target > 0 else 0.0)

print("D0 // isqrt(q) <= (d+2)*isqrt(q)        for ALL odd q in [3,2e5], d in [1,40):",
      len(fails_dp2_sq) == 0, "| first fails:", fails_dp2_sq[:4])
print("D0 // isqrt(q) <= (d+2)*(isqrt(q)+1)    for ALL:",
      len(fails_dp2_sqp1) == 0, "| first fails:", fails_dp2_sqp1[:4])
print("worst  (D0 // isqrt q) / ((d/2) sqrt q) :", round(worst_ratio, 4),
      "(asymptotic target is 1.0; finite-n overhead expected)")
