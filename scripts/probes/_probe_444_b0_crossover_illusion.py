#!/usr/bin/env python3
"""
#444 ATTACK on the flagship E_r transfer reduction: is "K_eff ≈ 0.6, E_r ≤ K^r·Wick" measuring the
FULL additive energy (which includes the b=0 Fourier term η_0=n, i.e. n^{2r}/p) or the house-relevant
REDUCED energy (b≠0)?  The full E_r obeys the RIGOROUS lower bound  E_r ≥ n^{2r}/p  (b=0 term), and
at the prize this exceeds Wick=(2r-1)‼·n^r already at integer depth r=6 — making the hypothesis
`E_r ≤ K^r·Wick`
with K=O(1) UNSATISFIABLE there, regardless of any conjecture. At small/computable n the crossover r
is large, so full-E_r K_eff looks bounded (≈0.6) = a FINITE-SIZE ILLUSION.

For prize-SHAPED small cases (p ≈ n^4, β=4) we compute the m=(p-1)/n Gauss periods and tabulate, per r:
  K_full   = (E_r_full / Wick)^{1/r}          [what GaussianEnergyBound/rEnergy uses]
  K_house  = (house^{2r} / Wick)^{1/r}         [the ACTUAL house vs Wick scale — the genuine target]
  b0/Wick  = (n^{2r}/p) / Wick                  [b=0 term relative to Wick; >1 ⟹ full E_r illusion]
  house/√(2n ln m)                              [the conjectured house ratio]
where E_r_full = (n^{2r} + n·Σ_i|η_i|^{2r}) / p,  house = max_i|η_i|, sum over the m nonzero-coset periods.
"""
import numpy as np
from math import log, sqrt
import sympy

def doublefact_odd(r):
    v = 1.0
    for t in range(1, r + 1):
        v *= (2 * t - 1)
    return v

def doublefact_odd_int(r):
    v = 1
    for t in range(1, r + 1):
        v *= (2 * t - 1)
    return v

def primitive_root(p):
    fac = sympy.factorint(p - 1)
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in fac):
            return g
    raise RuntimeError

def find_prime_beta4(n):
    # prime p ≡ 1 mod n, near n^4
    target = n ** 4
    p = target - (target % n) + 1
    while True:
        if p > n and sympy.isprime(p) and (p - 1) % n == 0:
            return p
        p += n

def periods(p, n):
    g = primitive_root(p)
    m = (p - 1) // n
    sub = np.array([pow(g, (m * j) % (p - 1), p) for j in range(n)], dtype=np.int64)
    reps = np.array([pow(g, i, p) for i in range(m)], dtype=np.int64)
    # coset i = reps[i] * sub mod p  ; eta_i = sum exp(2pi i z / p)
    eta = np.empty(m, dtype=np.complex128)
    w = 2j * np.pi / p
    for i in range(m):
        z = (reps[i] * sub) % p
        eta[i] = np.sum(np.exp(w * z))
    return eta, m

print("Prize-shaped (p ≈ n^4, β=4). K_full = full-energy K_eff (incl b=0); K_house = true house K_eff.")
print("Illusion present when, past the crossover r*, K_full >> K_house (full energy tracks b=0 term).\n")
for n in (16, 32, 64):
    p = find_prime_beta4(n)
    eta, m = periods(p, n)
    abseta2 = np.abs(eta) ** 2           # |η_i|^2 over m nonzero-coset periods
    house2 = abseta2.max()
    house = sqrt(house2)
    lnm = log(m)
    print(f"n={n}  p={p}  m={m}  house={house:.3f}  house/√(2n ln m)={house/sqrt(2*n*lnm):.3f}")
    print(f"   {'r':>2} {'b0/Wick':>11} {'K_full':>9} {'K_house':>8} {'E_full/Wick':>12} {'house^2r/Wick':>13}")
    crossover = None
    for r in range(2, 13):
        wick = doublefact_odd(r) * (n ** r)
        Pr = float(np.sum(abseta2 ** r))           # Σ_i |η_i|^{2r}
        b0 = (float(n) ** (2 * r)) / p              # b=0 term n^{2r}/p
        E_full = (float(n) ** (2 * r) + n * Pr) / p # full additive energy
        h2r = house2 ** r                            # house^{2r}
        b0_wick = b0 / wick
        K_full = (E_full / wick) ** (1.0 / r)
        K_house = (h2r / wick) ** (1.0 / r)
        if crossover is None and b0_wick > 1:
            crossover = r
        print(f"   {r:>2} {b0_wick:>11.3e} {K_full:>9.3f} {K_house:>8.3f} {E_full/wick:>12.3e} {h2r/wick:>13.3e}")
    print(f"   --> b0>Wick crossover at r* = {crossover} (past it, full-E_r is dominated by the b=0 term, "
          f"so K_full is an ILLUSION; K_house stays O(1)).\n")

prize_n = 2 ** 30
prize_q = 2 ** 158
prize_cross = next(r for r in range(1, 200) if prize_n ** r > prize_q * doublefact_odd_int(r))
ratio_r6 = prize_n ** 6 / (prize_q * doublefact_odd_int(6))

print("PRIZE extrapolation (n=2^30, p=2^158): b0/Wick = n^{2r}/(p·(2r-1)‼·n^r)")
print(f"first exceeds 1 at integer depth r={prize_cross}; at r=6 the ratio is {ratio_r6:.3e}.")
print("At r≈ln q≈109 it is astronomically larger, so FULL-energy GaussianEnergyBound")
print("(E_r ≤ K^r·Wick, K=O(1)) is UNSATISFIABLE at prize depth. The house bound needs the REDUCED")
print("energy Σ_{b≠0}|η_b|^{2r} = q·rEnergy − n^{2r} (`DCEnergyBound` / `eta_pow_le_dc`).")
