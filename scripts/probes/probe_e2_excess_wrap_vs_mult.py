#!/usr/bin/env python3
"""
PROBE: decompose the E_2(mu_n) additive-energy EXCESS over the char-0 baseline 3n^2-3n
into a WRAPAROUND part and a MULTIPLICATIVE-COINCIDENCE part, in the prize regime.

Frontier object (from WickStepOneEnergyThreshold, commit ee4d66435):
  excess(n,p) := E_2(mu_n) - (3n^2 - 3n)
The in-tree char-0 closed form rEnergy(mu_n) 2 = 3n^2 - 3n holds under hypothesis 2^n < p,
which FAILS in the prize regime q ~ n^beta << 2^n for n >= 64. The previous worker asserted
the excess = (a) wraparound quadruples a+b >= p  +  (b) genuine extra additive coincidences,
both turning on at n>=64, but did NOT separate/quantify them.

E_2(S) = #{(a,b,c,d) in S^4 : a+b = c+d}   (additive energy, S = mu_n subset of F_p, as INTEGERS in [1,p-1]).

We split the equation a+b = c+d (mod p) by whether the INTEGER sums wrap:
  - "no-wrap, no-wrap": a+b < p and c+d < p, equal as integers (a+b == c+d).
  - "wrap-class": at least one side reduces mod p (a+b >= p or c+d >= p) but a+b == c+d (mod p).
The char-0 / lifted additive energy E_2^Z(S) counts only INTEGER equality a+b == c+d.
The mod-p energy E_2^Fp(S) = E_2^Z + (extra solutions created by wraparound).

So:  excess = [E_2^Z(mu_n) - (3n^2-3n)]   +   [E_2^Fp(mu_n) - E_2^Z(mu_n)]
            =      MULT_part                +        WRAP_part
where MULT_part = genuine integer-additive coincidences of the MULTIPLICATIVE set beyond the
generic 3n^2-3n, and WRAP_part = solutions ONLY present mod p (wraparound).

Verify this decomposition numerically and report the size of each part across prize-regime cells.
"""
import sympy

def subgroup(p, n):
    # unique order-n subgroup of F_p^* (n | p-1). returns sorted ints in [1,p-1].
    g = sympy.primitive_root(p)
    h = pow(g, (p-1)//n, p)   # generator of order-n subgroup
    S = set()
    x = 1
    for _ in range(n):
        S.add(x)
        x = (x*h) % p
    assert len(S) == n, (p, n, len(S))
    return sorted(S)

def energy_Z(S):
    # integer additive energy: #{(a,b,c,d): a+b == c+d} over integer values
    from collections import Counter
    cnt = Counter()
    for a in S:
        for b in S:
            cnt[a+b] += 1
    return sum(v*v for v in cnt.values())

def energy_Fp(S, p):
    from collections import Counter
    cnt = Counter()
    for a in S:
        for b in S:
            cnt[(a+b) % p] += 1
    return sum(v*v for v in cnt.values())

def wrap_part_direct(S, p):
    # count quadruples (a,b,c,d) with (a+b)%p == (c+d)%p but a+b != c+d (integer)
    # = E_Fp - E_Z
    return energy_Fp(S, p) - energy_Z(S)

print(f"{'p':>8} {'n':>5} {'beta':>5} {'2^n<p?':>7} {'E2_Fp':>8} {'E2_Z':>8} {'base=3n^2-3n':>12} {'EXCESS':>8} {'WRAP':>7} {'MULT':>7}")
print("-"*92)

cells = [
    # (p, n) prize-regime proper subgroups
    (193, 8), (257, 16), (7681, 16), (12289, 16),
    (40961, 16), (40961, 64), (40961, 128), (40961, 256), (40961, 512),
    (786433, 16), (786433, 64), (786433, 256),
    (12289, 64), (12289, 128), (12289, 256), (12289, 1024),
    (40961, 1024),
]
for p, n in cells:
    if (p-1) % n != 0:
        continue
    S = subgroup(p, n)
    eFp = energy_Fp(S, p)
    eZ = energy_Z(S)
    base = 3*n*n - 3*n
    excess = eFp - base
    wrap = eFp - eZ
    mult = eZ - base
    import math
    beta = math.log(p)/math.log(n)
    twonltp = (2**n < p)
    print(f"{p:>8} {n:>5} {beta:>5.2f} {str(twonltp):>7} {eFp:>8} {eZ:>8} {base:>12} {excess:>8} {wrap:>7} {mult:>7}")

print()
print("KEY: EXCESS = WRAP + MULT must hold exactly (decomposition identity).")
print("If MULT==0 everywhere in regime => the ENTIRE excess is wraparound (a clean modular count,")
print("   axiom-clean countable, separable from the irreducible BGK content).")
print("If MULT>0 => the multiplicative set has genuine extra integer-additive coincidences =")
print("   the irreducible piece; quantify its size vs WRAP.")
