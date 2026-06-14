#!/usr/bin/env python3
"""
C1 CIRCULARITY CHECK — does object (A)'s closure secretly fold back to BGK?

The agent claims:
  (A) bad set = prime divisors of Res(Phi_s, Q)  [resultant/height object]
  (C) bad set = the additive energy / moment E_r = (1/p) sum_b |eta_b|^{2r}  [BGK sup-norm tail]
and that bad(A) STRICT SUBSET bad(C), so (A) "avoids" BGK.

ADVERSARIAL TEST OF CIRCULARITY.  There are TWO ways (A) could still BE BGK:

 (Z1) The closure target for the PRIZE is "max bad(A) prime < q".  Is bounding the MAX ELEMENT of
      Res(Phi_s,Q) divisors EQUIVALENT to a moment/sup-norm bound?  A prime p divides Res(Phi_s,Q)
      iff Q has a root in F_p that is a primitive s-th root of unity, i.e. iff sum_{l} zeta^{i_l} =
      sum_l zeta^{j_l} in F_p for the F_p s-th root zeta.  That is EXACTLY a char-p vanishing-sum
      collision -- the SAME event that creates char-p anomalous energy.  So bad(A) and bad(C) are
      the SAME KIND of event (a mod-p root-of-unity relation); (A) just counts FEWER of them
      (distinct-tuple pairs only).  TEST: is bad(A) exactly { p : some DISTINCT-tuple pair collides }
      and bad(C) = { p : ANY (incl. repeated-element) tuple pair collides }?  If so, the separation
      is real but BOTH are governed by the SAME vanishing-sum / resultant phenomenon at the SAME
      subgroup mu_s -- NOT a sup-norm-tail vs resultant dichotomy.

 (Z2) Is the relevant subgroup mu_s (order O(log n)) or mu_n (order n)?  If mu_s, the resultant has
      degree phi(s)=O(log n) and bad primes are genuinely small-subgroup (tractable, NOT prize-scale
      mu_n).  Confirm s = K log n from the construction; confirm the resultant is over Phi_s not Phi_n.

 (Z3) The DEEP-r wall.  worst-case r = rho s + 2.  r_cross (BGK crossover) ~ beta+1.  We verify the
      crossover claim by the EXACT BGK/moment mechanism:  E_r anomaly is O(Wick) (no char-p excess)
      iff r < r* where r* is where the diagonal Wick term n^r (2r-1)!! still dominates the char-p
      relation excess.  Compare r=rho s+2 to beta = log_n p.  Show r >> beta+1 for the construction
      parameters -> the single r IS deep.  Then the QUESTION: does "single deep r, set-cardinality"
      genuinely escape, or is the resultant max-element bound at deep r as hard as the moment?
"""
import math
from collections import Counter
from itertools import combinations, product
from sympy import isprime, primitive_root, factorint, cyclotomic_poly, Poly, symbols, resultant, totient


def fp_root(s, p):
    return pow(primitive_root(p), (p - 1) // s, p)


def char0_vecs(s):
    h = s // 2
    return [(((i % h)), (-1 if ((i // h) % 2 == 1) else 1)) for i in range(s)]


# ---- Z1: bad(A) = distinct-tuple collisions; bad(C) = any-tuple collisions; SAME event family ----
def collision_kinds(s, r, p):
    """Return (distinct_pair_collides, anytuple_pair_collides) booleans, comparing F_p to char0."""
    g = fp_root(s, p)
    roots = [pow(g, i, p) for i in range(s)]
    vecs = char0_vecs(s)
    h = s // 2

    # char-0 distinct sums and multiset multiplicities
    A0 = set(); mult0 = Counter()
    for comb in combinations(range(s), r):
        acc = [0] * h
        for i in comb:
            c, sg = vecs[i]; acc[c] += sg
        A0.add(tuple(acc))
    for tup in product(range(s), repeat=r):
        acc = [0] * h
        for i in tup:
            c, sg = vecs[i]; acc[c] += sg
        mult0[tuple(acc)] += 1

    Af = set(); multf = Counter()
    for comb in combinations(range(s), r):
        cc = 0
        for i in comb: cc = (cc + roots[i]) % p
        Af.add(cc)
    for tup in product(range(s), repeat=r):
        cc = 0
        for i in tup: cc = (cc + roots[i]) % p
        multf[cc] += 1

    distinct_collides = (len(Af) != len(A0))
    multiset_collides = (len(multf) != len(mult0)) or (sorted(multf.values()) != sorted(mult0.values()))
    return distinct_collides, multiset_collides


def Z1():
    print("=" * 90)
    print("[Z1] Are bad(A) and bad(C) the SAME event family (mod-p vanishing-sum at mu_s), differing")
    print("     only by distinct-vs-any tuples?  (If yes: separation is real but it is NOT")
    print("     'resultant vs sup-norm tail' -- both are resultant/relation events at the same mu_s.)")
    for (s, r) in [(8, 3), (16, 3)]:
        print(f"\n  s={s} r={r}:")
        bad_distinct_not_mult = []
        for k in range(1, 60):
            p = 1 + k * s
            if not isprime(p): continue
            d, m = collision_kinds(s, r, p)
            # the key implication: distinct-collide => multiset-collide ?
            if d and not m:
                bad_distinct_not_mult.append(p)
        print(f"    primes where DISTINCT collides but MULTISET does NOT: {bad_distinct_not_mult}")
        print(f"    (empty => bad(A) subset bad(B): distinct collision implies multiset collision)")


# ---- Z2: subgroup order; resultant degree ----
def Z2():
    print("\n" + "=" * 90)
    print("[Z2] subgroup order of the resultant object.  Kambire: H=<xi>, |H|=s=K log2 n.")
    print("     Res(Phi_s, Q): degree phi(s) = O(log n), NOT phi(n).  Confirm s grows like log n.")
    print(f"  {'mu':>4} {'n=2^mu':>10} {'s=K log2 n (K=4)':>18} {'phi(s)':>8} {'phi(n)':>12}")
    K = 4
    for mu in [20, 30, 40]:
        n = 2 ** mu
        s = K * mu  # = K log2 n
        # round s to a power of 2 (Kambire: s = 2^alpha); pick nearest pow2 >= s
        s2 = 2 ** math.ceil(math.log2(s))
        print(f"  {mu:>4} {n:>10} {s:>10}(->{s2:>4}) {int(totient(s2)):>8} {n//2:>12}")
    print("  => resultant is over mu_s, phi(s)=O(log n).  This is a SMALL-subgroup object,")
    print("     NOT the eval-domain mu_n.  (Corrects KB lines 908-918 'spurious live in mu_n'.)")


# ---- Z3: crossover r_cross vs worst-case r ----
def Z3():
    print("\n" + "=" * 90)
    print("[Z3] worst-case r = rho s + 2 vs deep-moment crossover.  Is the single r DEEP?")
    print("  Kambire: s=K log2 n, p in [4^s,8^s] => beta=log_n p in [2K,3K].")
    print("  Energy E_r is char-p-clean (=Wick) while r < r*; r* ~ where diagonal n^r(2r-1)!! >> char-p")
    print("  relation excess. Empirically (KB) crossover r* ~ beta+1. Compare.")
    print(f"  {'rho':>6} {'K':>3} {'mu':>4} {'s':>6} {'r=rho s+2':>10} {'beta=3K':>8} {'r_cross~beta+1':>14} {'r/r_cross':>9}")
    for rho in [0.5, 0.25, 0.125]:
        K = 4
        for mu in [20, 30, 40]:
            s = K * mu
            r = rho * s + 2
            beta = 3 * K
            rcross = beta + 1
            print(f"  {rho:>6} {K:>3} {mu:>4} {s:>6.0f} {r:>10.1f} {beta:>8} {rcross:>14} {r/rcross:>9.2f}")
    print("  => r = Theta(log n) GROWS; r_cross = O(1) FIXED.  The worst-case single r is DEEP.")
    print("  CONCLUSION: the count is single-r but that r is in the deep (BGK) regime. The escape, IF")
    print("  real, is that (A) is a SET CARDINALITY whose bad primes = Res(Phi_s,Q) divisors with")
    print("  |Res|<=s^s (ELEMENTARY height bound), vs (C) needing a moment/sup-norm bound at the same r.")


if __name__ == "__main__":
    Z1()
    Z3()
