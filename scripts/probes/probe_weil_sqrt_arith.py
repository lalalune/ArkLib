#!/usr/bin/env python3
# Verify the EXACT Nat arithmetic that makes  D0 // M <= (d+2)*M  provable cleanly,
# with M = isqrt(q).  Nat lemma chain candidates:
#   (a) Nat.div_le_of_le_mul:  a // b <= c  if  a <= c * b   -- WRONG direction, that's a<=cb => a//b<=c? check.
#   Actually  Nat.div_le_iff_le_mul_add_pred / Nat.div_le_of_le_mul (a <= b*c -> a//b <= c).
# So we need:  D0 <= (d+2)*M * M  = (d+2)*M^2.  Since M=isqrt q, M^2 <= q.  Is D0 <= (d+2)*M^2 ?
# D0 = ((q-1)//2)*d + (q-1).  Test directly.
import math

def D0(q, d):
    return ((q - 1) // 2) * d + (q - 1)

# Path A: D0 <= (d+2) * M^2  (then div_le_of_le_mul gives D0 // M <= (d+2)*M)
failsA = []
# Path B (weaker, always-true fallback): D0 <= (d+2) * M * (M+1) might be needed if M^2 too tight
failsB = []
for q in range(3, 300001, 2):
    M = math.isqrt(q)
    if M == 0:
        continue
    for d in range(1, 50):
        d0 = D0(q, d)
        if d0 > (d + 2) * M * M:
            failsA.append((q, d, d0, (d + 2) * M * M))
        if d0 > (d + 2) * M * (M + 1):
            failsB.append((q, d, d0, (d + 2) * M * (M + 1)))

print("Path A  D0 <= (d+2)*M^2          all odd q<=3e5, d<50:", len(failsA) == 0,
      "| first fails:", failsA[:6])
print("Path B  D0 <= (d+2)*M*(M+1)      all:", len(failsB) == 0,
      "| first fails:", failsB[:6])
# If A fails, the clean provable target is via M*(M+1) >= q (since (isqrt q +1)^2 > q):
#   D0 < (d+2)/2 * ... -- report the tightest constant K with D0 <= K*M^2 holding for all.
worstK = 0.0
for q in range(3, 300001, 2):
    M = math.isqrt(q)
    if M == 0: continue
    for d in range(1, 50):
        d0 = D0(q, d)
        worstK = max(worstK, d0 / (M * M * (d + 2)))
print("tightest constant K in D0 <= K*(d+2)*M^2 :", round(worstK, 5))
