#!/usr/bin/env python3
"""
PROBE (#407/#444): crossCell is p-INDEPENDENT (char-0 structural) and SUPER-random in the thin
prize regime => the "sub-random via spurious mod-p collisions" open input proposed by
CrossCellShkredovBound.lean is WALLED (no saving to extract).

Context.  CrossCellShkredovBound.lean's conclusion states the genuine open input the prize needs
"must come from the *arithmetic* of the q-reduction (spurious mod-p collisions), not from
sum-product / BSG", i.e. it hopes crossCell is SUB-random (< the BCHKS-1.12 expectation) because
mod-p collisions cancel structure.  This probe tests that hope directly in the thin prize regime.

Object (exact char-p):  G = mu_n = H u zeta*H,  H = mu_{n/2} (squares),  n=2^mu, proper subgroup
of F_p*, p prime ==1 mod n, NEVER n=q-1.   N0(S,r)=#{(x_1..x_r) in S^r : sum=0 mod p}.
crossCell(r) = N0(G,r) - 2*N0(H,r)  (>=0 by the descent).
Random/BCHKS-1.12 expectation:  E_rand(r) = (2^r - 2)*|H|^r / p.   ratio = crossCell/E_rand.

FINDINGS (exact DP counting, multi-prime):
 1. crossCell is PERFECTLY p-INDEPENDENT in the thin regime (beta>=4): e.g. n=8 -> 96 (r=4),
    4320 (r=6) at EVERY prime; n=16 -> 384, 40320 at every prime.  => it is the char-0 STRUCTURAL
    relation count (#{sum u + zeta sum w = 0} holding over Z, hence at every large p), with ZERO
    spurious mod-p collision component (collisions would scale like 1/p; crossCell does not move).
 2. SUPER-random, diverging with thinness: ratio = crossCell/E_rand ~ (p-independent count)/(C/p)
    grows ∝ p.  At beta=4-5: ratios 100x-7000x.  crossCell is FAR ABOVE random, not below.
 3. rule-3 thinness control (thick beta~2.3 vs thin beta~4-5): thick ratio O(1)-5x; thin 100x-7000x.
    The super-random excess is the char-0 structural count dominating as p->infty (thin) -- a
    THINNESS-ESSENTIAL p-independent floor, NOT a collision artifact.
 4. At thick/small p the count can EXCEED the char-0 value (collisions ADD, e.g. n=16,r=6: 48000 at
    p=593 vs 40320 char-0) -- so collisions only INCREASE crossCell, never give a sub-random saving.

VERDICT (rule-4 constraint map; NOT a CORE result): there is no sub-random saving in crossCell to
extract.  crossCell >= char-0 structural count at all p (collisions only add).  The proposed
"arithmetic-of-the-q-reduction / mod-p-collision" open input is WALLED: the binding object is the
p-INDEPENDENT char-0 structural relation count, exactly the (super-random, BCHKS-1.12-saturating)
quantity, with no mod-p cancellation available.  Any CORE proof through crossCell must bound the
char-0 structural count itself (= Lam-Leung / vanishing-sums-of-roots-of-unity), not hope for
collision savings.
"""
import sympy
from collections import defaultdict


def N0_exact(S, p, r):
    """exact #{(x_1..x_r) in S^r : sum = 0 mod p} via running-sum DP."""
    dist = {0: 1}
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for x in S:
                nd[(s + x) % p] += c
        dist = nd
    return dist.get(0, 0)


def primes_for(n, beta, count):
    ps = []
    p = sympy.nextprime(int(n ** beta))
    while len(ps) < count:
        if (p - 1) % n == 0:
            ps.append(p)
        p = sympy.nextprime(p)
    return ps


def build(n, p):
    g = sympy.primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    G = []
    x = 1
    for _ in range(n):
        G.append(x); x = (x * h) % p
    h2 = (h * h) % p
    H = []
    x = 1
    for _ in range(n // 2):
        H.append(x); x = (x * h2) % p
    return G, H


def main():
    print("crossCell vs random (BCHKS-1.12 (2^r-2)|H|^r/p); ratio<1 = sub-random (the proposed saving)")
    print(f"{'n':>4} {'beta':>5} {'p':>10} {'r':>3} {'crossCell':>10} {'E_rand':>12} {'ratio':>9}")
    for n in [8, 16]:
        Hc = n // 2
        for beta in [2.3, 4.0, 5.0]:
            for p in primes_for(n, beta, 1):
                if p > 1_200_000:
                    continue
                G, H = build(n, p)
                for r in [4, 6]:
                    cross = N0_exact(G, p, r) - 2 * N0_exact(H, p, r)
                    Erand = (2 ** r - 2) * (Hc ** r) / p
                    ratio = cross / Erand if Erand > 0 else float('nan')
                    print(f"{n:>4} {beta:>5} {p:>10} {r:>3} {cross:>10} {Erand:>12.2f} {ratio:>9.2f}")
            print()
    print("p-INDEPENDENCE (thin beta=4, fixed n, prime sweep): constant => char-0 structural, no collision saving")
    for n in [8, 16]:
        print(f"  n={n}:")
        for p in primes_for(n, 4.0, 4):
            if p > 1_200_000:
                continue
            G, H = build(n, p)
            c4 = N0_exact(G, p, 4) - 2 * N0_exact(H, p, 4)
            c6 = N0_exact(G, p, 6) - 2 * N0_exact(H, p, 6)
            print(f"    p={p:>9}  crossCell(r=4)={c4:>7}  crossCell(r=6)={c6:>8}")
    print("\nVERDICT: crossCell is p-independent (char-0 structural) + super-random in the thin regime;")
    print("         collisions only ADD (thick small-p > char-0). No sub-random saving => the proposed")
    print("         'mod-p collision / arithmetic-of-q-reduction' open input is WALLED.")


if __name__ == '__main__':
    main()
