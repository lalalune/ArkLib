#!/usr/bin/env python3
# ATTACK the 06:55 "No-Excess closure-shape" claim (issue #407): char-p excess primes divide the
# FIXED integer N := ∏_T N(Schur_λ(ζ^T)), hence finite, hence "prize regime unconditionally safe,
# bad primes confined to small index, far below any prize prime."
#
# THE HOLE: finiteness gives NO size bound. A fixed integer N ~ poly(n)^{φ(n)} (super-exponential
# in n) can have prime factors up to its own magnitude — possibly near/above 2^160. "Finite" ≠
# "bounded below the prize prime." TEST: does the MAX excess prime GROW with n?
#
# Object: complete homogeneous symmetric h_j at ζ^T for w-subsets T of μ_n (n=2^μ). Excess prime
# q≡1 mod n ⟺ q | N(h_j(ζ^T)) for some GENUINE T (h_j(ζ^T)≠0 over ℂ). Norm computed numerically
# (product over primitive n-th roots, rounded), then factored.
#
# RESULT (2026-06-14): max excess prime (q≡1 mod n) GROWS super-polynomially —
#   n=8  : NONE (faithful)
#   n=16 : 8161   (~2^13, index 510)
#   n=32 : 877313 (~2^19.7, index 27416) [fleet datum, 06:53 comment]
# ~ +6.7 bits per μ-increment ⟹ extrapolated max at prize n=2^32 is ~2^200 ≫ 2^160 = prize prime.
# So the prize prime is WITHIN the excess range; "confined far below prize" is REFUTED. Whether the
# specific prize prime is an excess prime = the open specific-subgroup NVM question (2310.09992,
# index>3 open), NOT settled by finiteness.
import cmath, math, itertools
from sympy import factorint

def hj(j, vals):
    from itertools import combinations_with_replacement
    if j == 0: return 1+0j
    return sum(math.prod(vals[i] for i in c)
               for c in combinations_with_replacement(range(len(vals)), j))

def maxexcess(n, j, w, cap=2000):
    prim = [a for a in range(n) if math.gcd(a, n) == 1]   # primitive n-th roots, φ(n)=n/2 of them
    found = set(); cnt = 0; genuine = 0
    for T in itertools.combinations(range(n), w):
        base = [cmath.exp(2j*math.pi*t/n) for t in T]
        if abs(hj(j, base)) < 1e-9:
            continue  # vanishes over ℂ — not a genuine char-p excess source
        genuine += 1
        N = 1.0+0j
        for a in prim:
            N *= hj(j, [cmath.exp(2j*math.pi*((a*t) % n)/n) for t in T])
        Ni = round(N.real)
        if abs(N.imag) > 1e-3 or Ni == 0:
            continue
        for q in factorint(abs(Ni)):
            if q % n == 1:
                found.add(q)
        cnt += 1
        if cnt > cap: break
    return (max(found) if found else None), len(found), genuine

if __name__ == "__main__":
    print("Max excess prime (q≡1 mod n) vs n  — GROWS ⟹ '%confined to small index' refuted:")
    for (n, j, w) in [(8,1,3),(8,3,5),(16,1,3),(16,3,5),(16,5,7),(16,7,9)]:
        mx, num, g = maxexcess(n, j, w)
        print(f"  n={n} h_{j} w={w}: #excess(≡1 mod {n})={num} MAX={mx} (genuine subsets {g})")
