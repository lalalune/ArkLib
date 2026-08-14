#!/usr/bin/env python3
"""
probe_444_floorbad_defect_tower_invariant.py

§9 floor route (#464) — TOWER-INVARIANCE of the defect resultant's ramification locus.

Backs the dossier §9 claim that the bad-prime set is "0-dimensional / p-independent / flat in p"
(a fixed cyclotomic resultant, NOT a growing √p character sum). The kernel lemma
`floorBad_defect_ramification_tower_invariant_export` locks the decidable facts; this probe
verifies them + the MECHANISM (why the odd-ramification set is preserved across the tower).

Facts verified:
  1. R^(32)(g) = S(g^4) exactly over Z, where S(u) = u^4 - 196u^3 + 4486u^2 - 21700u + 1
     (the n=8 excess quartic; u = g^4 is the (p-1)/n subgroup-dilation between n=8 and n=32).
  2. S(0) = 1 (UNIT constant term => all roots units, product = 1).
  3. disc(S)   = 2^41  * 17^2 * 257^2   -> odd-ramification {17, 257}.
  4. disc(R32) = 2^196 * 17^8 * 257^8   -> odd-ramification {17, 257}  (SAME SET).
  5. MECHANISM: oddrad(disc(P(g^4))) = oddrad(disc P) ∪ oddrad(P(0)). With P(0)=1 the second
     set is empty => the dilation adds NO new odd prime => ramification locus is tower-invariant.
     NON-TRIVIAL: random quartics generically GAIN extra odd primes under u->g^4.
"""
import sympy as sp

g, u = sp.symbols('g u')
S = u**4 - 196*u**3 + 4486*u**2 - 21700*u + 1
R32 = g**16 - 196*g**12 + 4486*g**8 - 21700*g**4 + 1

def oddrad(x):
    x = abs(int(x))
    return sorted(p for p in sp.factorint(x) if p != 2) if x else []

# 1. tower self-identity
assert sp.expand(R32 - S.subs(u, g**4)) == 0, "R32 != S(g^4)"
print("[1] R^(32)(g) = S(g^4) exactly over Z:           OK")

# 2. unit constant term
assert int(S.subs(u, 0)) == 1, "S(0) != 1"
print("[2] S(0) = 1 (unit constant term):                OK")

# 3,4. discriminants + odd-ramification
dS = sp.discriminant(S, u)
dR = sp.discriminant(R32, g)
assert sp.factorint(dS) == {2: 41, 17: 2, 257: 2}, sp.factorint(dS)
assert sp.factorint(dR) == {2: 196, 17: 8, 257: 8}, sp.factorint(dR)
print(f"[3] disc(S)   = 2^41  * 17^2 * 257^2  oddrad={oddrad(dS)}: OK")
print(f"[4] disc(R32) = 2^196 * 17^8 * 257^8  oddrad={oddrad(dR)}: OK")
assert oddrad(dS) == oddrad(dR) == [17, 257], "odd-ramification not tower-invariant"
print("    => odd-ramification TOWER-INVARIANT {17,257}:  OK")

# 5. mechanism + non-triviality
import random
random.seed(11)
union_formula_ok = True
gained_count = 0
trials = 0
for _ in range(40):
    a, b, c, d = [random.randint(-40, 40) for _ in range(4)]
    P = u**4 + a*u**3 + b*u**2 + c*u + d
    dP = sp.discriminant(P, u)
    if dP == 0:
        continue
    dPg4 = sp.discriminant(P.subs(u, g**4), g)
    if dPg4 == 0:
        continue
    trials += 1
    const = int(P.subs(u, 0))
    predicted = sorted(set(oddrad(dP)) | set(oddrad(const)))
    if oddrad(dPg4) != predicted:
        union_formula_ok = False
    if set(oddrad(dPg4)) != set(oddrad(dP)):
        gained_count += 1
assert union_formula_ok, "union formula oddrad(disc P(g^4)) = oddrad(disc P) ∪ oddrad(P(0)) FAILED"
print(f"[5] mechanism union-formula holds on {trials} random quartics: OK")
print(f"    non-trivial: {gained_count}/{trials} random quartics GAINED odd primes under u->g^4")
assert gained_count > 0, "invariance would be trivial if no random quartic ever gained a prime"

# S vs floor-bad disjointness sanity (sibling fact, not re-proved here, just sanity):
print()
print("ALL TOWER-INVARIANCE CHECKS PASS.")
print("Conclusion: the §9 defect ramification locus {17,257} is a FIXED finite set, invariant")
print("under the n=8 -> n=32 subgroup dilation, FORCED by S having a unit constant term.")
print("Hardens §9's '0-dimensional / flat-in-p bad-prime set' claim. No CORE claim. CORE OPEN.")
