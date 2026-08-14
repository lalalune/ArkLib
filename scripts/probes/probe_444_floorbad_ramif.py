#!/usr/bin/env python3
"""
Probe for #464 §9 (bad-prime localization, the off-BGK δ* FLOOR lever):
does the n=32 defect resultant's DISCRIMINANT/RAMIFICATION locus identify the floor-bad prime?

§9 states, for n=32:
  - defect core polynomial S(u) = u^4 - 196u^3 + 4486u^2 - 21700u + 1  (= R^(32)(g), u=g^4),
  - disc(S) = 2^41 * 17^2 * 257^2,  "root-count drops exactly at {17,257}",
  - FLOOR-bad = the single smallest prime ≡ 1 mod n; for n=32 that is 97.

VERDICT (this probe): the disc-ramification set {2,17,257} is DISJOINT from the floor-bad prime 97.
  - disc(S) factors EXACTLY as 2^41*17^2*257^2 (matches §9).
  - At p=17 and p=257 (p | disc) S has a REPEATED root => root-count drops to 3 (generic = 4).
  - 97 ∤ disc (UNRAMIFIED) and S has the FULL 4 roots mod 97.
  - 17 ≢ 1 mod 32 (not in the AP); 257 ≡ 1 mod 32 but 257 ≠ 97 (not the least).
So ramification (p|disc, root-count drop) and floor-badness (least p≡1 mod n) are governed by
DIFFERENT arithmetic and are disjoint at n=32. The off-BGK floor route cannot be closed by a
"ramified ⟹ bad / unramified ⟹ good" reading. (Consistent with _AvD2: Linnik existence ⊬ divisibility.)

Formalized: ArkLib/.../Frontier/_FloorBadRamificationDisjoint.lean (axiom-clean, decidable).
Run: python3 scripts/probes/probe_444_floorbad_ramif.py
"""
import sympy as sp

u = sp.symbols('u')
S = u**4 - 196*u**3 + 4486*u**2 - 21700*u + 1

disc = sp.discriminant(S, u)
print("S(u) =", S)
print("disc(S) =", disc, "=", sp.factorint(disc))
assert disc == 2**41 * 17**2 * 257**2, "disc factorization mismatch vs §9"

def nroots_mod(p):
    return sum(1 for x in range(p) if int(S.subs(u, x)) % p == 0)

def repeated_root_mod(p):
    Sp = sp.Poly(S, u, modulus=p)
    g = sp.Poly(sp.gcd(Sp, Sp.diff(u)))
    return g.degree() > 0

def least_prime_cong1(n):
    p = n + 1
    while not sp.isprime(p):
        p += n
    return p

n = 32
floor_bad = least_prime_cong1(n)
print(f"\nleast prime ≡ 1 mod {n} (floor-bad) = {floor_bad}")
assert floor_bad == 97

print("\np    | p|disc | repeated-root | #roots mod p | p≡1 mod32")
for p in [17, 257, 97]:
    print(f"{p:4d} | {disc % p == 0!s:6} | {repeated_root_mod(p)!s:13} | "
          f"{nroots_mod(p):12d} | {p % 32 == 1}")

# disjointness assertions
assert disc % 17 == 0 and nroots_mod(17) == 3 and 17 % 32 != 1
assert disc % 257 == 0 and nroots_mod(257) == 3 and 257 % 32 == 1 and 257 != 97
assert disc % 97 != 0 and nroots_mod(97) == 4 and 97 % 32 == 1
print("\nVERDICT: ramification set {17,257} DISJOINT from floor-bad prime {97}. "
      "Discriminant does NOT identify the floor-bad prime. All assertions pass.")
