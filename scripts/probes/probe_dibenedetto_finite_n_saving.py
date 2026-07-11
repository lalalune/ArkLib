#!/usr/bin/env python3
"""
Probe (ONE sweep): the di Benedetto near-Sidon edge saving at the TRUE realised finite-n
log-exponents t_k(n) = log E_k(n)/log n, NOT the idealised (2,3).

E2(n) = 3n^2 - 3n   (char-0 exact, in tree: B4_closed / REnergyTwoExact)
E3(n) = 15n^3 - 45n^2 + 40n  (char-0 exact, in tree: B6_eq_E3)
saving(t2,t3) = (10 - 2*t3 - t2/2)/72

Claim under test (the envelope file's UNDISCHARGED prose):
  (A) realised t_k(n) > k strictly at every finite n>=4 (so the idealised hypothesis t<=k is NEVER met)
  (B) realised saving(t2(n),t3(n)) < 1/24 STRICTLY at every finite n (saving approaches 1/24 FROM BELOW)
  (C) realised saving -> 1/24 as n->inf (the idealisation is the limit)
  (D) realised saving is MONOTONE INCREASING in n (each octave gets closer to 1/24)
NEVER validate on n=q-1; n=2^a is the prize subgroup order itself (intrinsic, p-independent here:
the char-0 energies are p-independent closed forms, so this probe is over the closed forms directly).
"""
import math
from fractions import Fraction as F

def E2(n): return 3*n*n - 3*n
def E3(n): return 15*n**3 - 45*n*n + 40*n
def t2(n): return math.log(E2(n))/math.log(n)
def t3(n): return math.log(E3(n))/math.log(n)
def saving(t2v, t3v): return (10 - 2*t3v - t2v/2)/72

target = 1/24
print(f"{'n':>10} {'t2(n)':>8} {'t3(n)':>8} {'saving':>12} {'1/24-sav':>12} {'<1/24?':>7} {'t2>2?':>6} {'t3>3?':>6}")
fails_A2 = fails_A3 = fails_B = 0
prev_sav = None
mono_ok = True
rows = []
for a in range(2, 31):  # n = 2^2 .. 2^30
    n = 2**a
    tv2, tv3 = t2(n), t3(n)
    sv = saving(tv2, tv3)
    a2 = tv2 > 2.0
    a3 = tv3 > 3.0
    b = sv < target
    if not a2: fails_A2 += 1
    if not a3: fails_A3 += 1
    if not b: fails_B += 1
    if prev_sav is not None and sv < prev_sav - 1e-15:
        mono_ok = False
    prev_sav = sv
    rows.append((n, tv2, tv3, sv))
    print(f"{n:>10} {tv2:>8.4f} {tv3:>8.4f} {sv:>12.8f} {target-sv:>12.8f} {str(b):>7} {str(a2):>6} {str(a3):>6}")

print()
print(f"(A2) t2(n) > 2 at every finite n>=4:   fails = {fails_A2}/29  -> {'CONFIRMED' if fails_A2==0 else 'FALSE'}")
print(f"(A3) t3(n) > 3 at every finite n>=4:   fails = {fails_A3}/29  -> {'CONFIRMED' if fails_A3==0 else 'FALSE'}")
print(f"(B)  saving(t2(n),t3(n)) < 1/24:       fails = {fails_B}/29  -> {'CONFIRMED' if fails_B==0 else 'FALSE'}")
print(f"(C)  saving -> 1/24 (limit): saving(2^30)={rows[-1][3]:.10f}, 1/24={target:.10f}, gap={target-rows[-1][3]:.2e}")
print(f"(D)  saving MONOTONE INCREASING in n:  {'CONFIRMED' if mono_ok else 'FALSE'}")

# The CLEAN structural reason (the theorem skeleton): since E_k(n) > n^k strictly (leading constant>1),
# t_k(n) = log E_k / log n > k, so saving(t2,t3) = (10 - 2 t3 - t2/2)/72 < (10 - 2*3 - 2/2)/72 = (10-6-1)/72 = 3/72 = 1/24.
# i.e. ANY (t2>2, t3>3) gives saving < 1/24 by the same antitone formula already proven (diBenedettoSaving_le_ceiling
# is the >= side; this is the STRICT < side under STRICT t2>2 OR t3>3). The finite-n realised energies satisfy
# E2 = 3n^2-3n > n^2 (n>=2) and E3 = 15n^3-... > n^3, so t_k>k STRICTLY -> saving < 1/24 STRICTLY.
print()
print("STRUCTURAL: E2(n)=3n^2-3n satisfies n^2 < E2 (n>=2); E3(n) satisfies n^3 < E3 (all n>=1).")
print("So realised t_k(n)>k strictly => saving(t2,t3) < saving(2,3) = 1/24 strictly (antitone, strict).")
print("Check n^2<E2: ", all(n*n < E2(n) for n in [2**a for a in range(2,31)]))
print("Check n^3<E3: ", all(n**3 < E3(n) for n in [2**a for a in range(2,31)]))
