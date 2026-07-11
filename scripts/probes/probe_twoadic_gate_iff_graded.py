#!/usr/bin/env python3
# Probe: extend the 2-adic parity gate beyond the proven generic skeleton.
# Working in Z[zeta_{2^mu}], lambda=(1-zeta) the unique prime over 2.
# Generic skeleton (proven in _TwoAdicParityGate.lean): D - sigma(D) in (lambda); balanced => D in (lambda).
# QUESTIONS (probe-first, before formalizing a stronger brick):
#  Q1 (IFF gate): is  2 | N(D)  <=>  sigma(D) even ?  (proven side is one direction; verify the converse)
#  Q3 (weight-2 exact): N(1 - zeta^c) = 2^{2^{v2(c)}} pure 2-power (the W1=0 claim) -- check odd part == 1.
import cmath, math

def zeta(N):
    return cmath.exp(2j * math.pi / N)

def norm_of(coeffs, N):
    # full field norm in Q(zeta_N)/Q = product over k coprime to N of D(zeta^k)
    z = zeta(N)
    prod = 1.0 + 0j
    for k in range(1, N):
        if math.gcd(k, N) == 1:
            val = sum(c * (z ** (k * a)) for a, c in coeffs.items())
            prod *= val
    return prod

def v2(m):
    if m == 0:
        return 99
    v = 0
    while m % 2 == 0:
        m //= 2
        v += 1
    return v

def oddpart(m):
    m = abs(m)
    if m == 0:
        return 0
    while m % 2 == 0:
        m //= 2
    return m

print("=== Q3: weight-2 norm N(1 - zeta_n^c), n=2^mu : pure 2-power? v2(N)=2^{v2(c)}? ===")
allgood_q3 = True
for mu in range(2, 7):
    n = 2 ** mu
    bad = 0
    for c in range(1, n):
        coeffs = {0: 1, c: -1}
        nv = norm_of(coeffs, n)
        nr = round(nv.real)
        if abs(nv.imag) > 1e-5:
            print(f"  n={n} c={c}: NONREAL norm {nv}")
            bad += 1
            continue
        op = oddpart(nr)
        predv2 = 2 ** v2(c)  # claim: v2(N) = 2^{v2(c)}
        gotv2 = v2(abs(nr))
        if op != 1 or gotv2 != predv2:
            print(f"  n={n} c={c}: N={nr} oddpart={op} v2={gotv2} pred_v2={predv2}  <-- MISMATCH")
            bad += 1
            allgood_q3 = False
    print(f"  n={n}: weight-2 cases checked, mismatches={bad}")
print(f"Q3 verdict (pure 2-power AND v2=2^v2(c)): {'PASS' if allgood_q3 else 'FAIL'}")

print()
print("=== Q1: full IFF parity gate  2 | N(D)  <=>  sigma(D) even,  over enumerated signed relations ===")
# enumerate signed combos: choose r support points (distinct powers) with signs, check both directions.
from itertools import combinations, product as iproduct
fails = 0
total = 0
for mu in range(2, 5):
    n = 2 ** mu
    powers = list(range(n))
    # support sizes 2..4, signs in {+1,-1}
    for r in range(2, 5):
        for supp in combinations(powers, r):
            for signs in iproduct([1, -1], repeat=r):
                coeffs = {}
                for a, s in zip(supp, signs):
                    coeffs[a] = coeffs.get(a, 0) + s
                # collapse; skip the all-zero coefficient case
                coeffs = {a: c for a, c in coeffs.items() if c != 0}
                if not coeffs:
                    continue
                sigma = sum(coeffs.values())
                nv = norm_of(coeffs, n)
                nr = round(nv.real)
                if abs(nv.imag) > 1e-4:
                    continue
                two_divides_N = (nr % 2 == 0)
                sigma_even = (sigma % 2 == 0)
                total += 1
                if two_divides_N != sigma_even:
                    fails += 1
                    if fails <= 8:
                        print(f"  n={n} coeffs={coeffs} sigma={sigma} N={nr} 2|N={two_divides_N} sigma_even={sigma_even} VIOLATION")
    print(f"  n={n}: enumerated, running fails={fails}")
print(f"Q1 verdict over {total} relations: {'PASS (full IFF holds)' if fails == 0 else f'FAIL ({fails} violations)'}")
