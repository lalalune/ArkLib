#!/usr/bin/env python3
"""
Probe for C39 (Tao-Croot-Lev-Pach for the Bad-Scalar Set as a Cap Configuration in Z/p).

CONJECTURE C39 claims:
  - the bad-scalar set B_w forms a 3-AP-free / cap configuration in (Z/p, +),
  - so the polynomial-method (Croot-Lev-Pach / Ellenberg-Gijswijt) cap bound
    forces |B_w| <= p^{1-c} for some fixed c > 0,
  - which combined with the gcd-coset law (L3) caps the per-direction list
    below the budget n past Johnson.
  A polynomial-method (non-character) lever.

WHAT WE TEST (three independent horns; ANY one kills it):

 (H1) IS B_w EVEN 3-AP-FREE?  The single-codeword bad-alpha set for pencil (a,b)
      is, by the in-tree orbit-count law L3,
            B = { -z^{j(a-b)} : j in 0..n-1 }  subset of F_p,
      a GEOMETRIC progression (multiplicative coset of <r>, r = z^{a-b}, scaled
      by -1). A geometric progression {c, c r, c r^2, ...} contains a 3-AP
      x,y,z (x+z=2y) whenever c r^i + c r^k = 2 c r^j for some i<j<k, i.e.
      r^i + r^k = 2 r^j. We COUNT actual 3-APs inside B over proper mu_n,
      p prime, p >> n^3, never n=p-1. If B contains 3-APs, it is NOT a cap,
      and the cap hypothesis is FALSE on the very object L3 hands C39.

 (H2) THE CAP BOUND IS VACUOUS IN A CYCLIC GROUP.  Croot-Lev-Pach (Z/4^n) and
      Ellenberg-Gijswijt (F_q^n) give an EXPONENTIAL-IN-DIMENSION saving:
      a 3-AP-free subset of F_q^n has size <= (c_q)^n with c_q < q. The saving
      lives in the AMBIENT DIMENSION n -> infinity. The group Z/p is the n=1
      (one-dimensional) cyclic group; there the polynomial method gives NOTHING
      beyond trivial. The genuine 3-AP-free bound in Z/p is Behrend/Bloom-Sisask:
            r_3(p) = p / exp((log p)^c)  = p^{1-o(1)},
      i.e. |B_w| <= p^{1-o(1)}, which is NOT p^{1-c} for any fixed c>0, and is
      MASSIVELY larger than the budget n ~ p^{1/4}. We confirm the cap savings
      formula is dimensionally inapplicable and report the actual achievable
      bound size.

 (H3) THE NUMBERS: even the FALSE p^{1-c} would not help. The budget is O(n)
      with n ~ p^{1/beta}, beta ~ 4. p^{1-c} >> n for every fixed c < 1-1/beta.
      And |B_w| from L3 is ALREADY exactly n/gcd(b-a,n) <= n -- so any genuine
      cap bound of size p^{1-c} (>> n) is WEAKER than the trivial in-tree L3
      coset size. The cap lever can only LOSE against L3.
"""
import sympy
from math import gcd, exp, log

def find_p_and_subgroup(n):
    """p prime, p >> n^3 (here p ~ n^4), n | p-1, mu_n proper subgroup, never n=p-1."""
    target = n**4
    m = target // n
    while True:
        p = m * n + 1
        if sympy.isprime(p) and p > 100 * n**3:
            g = int(sympy.primitive_root(p))
            z = pow(g, (p - 1) // n, p)
            mu = [pow(z, j, p) for j in range(n)]
            assert len(set(mu)) == n
            assert p - 1 != n
            return p, z, mu
        m += 1

def bad_set(z, n, a, b, p):
    """L3 single-codeword bad-alpha coset: B = { -z^{j(a-b)} : j }."""
    return sorted({(-pow(z, (j * (a - b)) % n, p)) % p for j in range(n)})

def count_3aps(B, p):
    """Count nontrivial 3-APs (x,y,z) with x+z = 2y mod p, x,y,z in B, not all equal.
    Returns (#ordered nontrivial 3-AP triples, #with distinct x,z)."""
    Bset = set(B)
    nontrivial = 0
    distinct = 0
    for y in B:
        for x in B:
            zz = (2 * y - x) % p
            if zz in Bset:
                if not (x == y == zz):
                    nontrivial += 1
                if x != zz:
                    distinct += 1
    return nontrivial, distinct

print("=== C39 probe: is the bad-scalar set a cap (3-AP-free) and does CLP help? ===\n")
print("(H1) 3-AP COUNT inside the L3 bad-alpha set B = {-z^{j(a-b)}} over proper mu_n:\n")
print(f"{'n':>5} {'p':>14} {'(a,b)':>10} {'gcd':>4} {'|B|':>5} "
      f"{'#3AP(nontriv)':>13} {'#3AP(distinct)':>14} {'cap?':>6}")

any_cap_violation = False
for n in [16, 32, 64, 128]:
    p, z, mu = find_p_and_subgroup(n)
    k = n // 4
    pencils = [(k, 3*k), (k, 2*k), (1, 2), (1, n//2), (1, 3)]
    for (a, b) in pencils:
        if a == b:
            continue
        d = gcd((b - a) % n, n)
        B = bad_set(z, n, a, b, p)
        nt, dist = count_3aps(B, p)
        is_cap = (dist == 0)
        if not is_cap and len(B) >= 3:
            any_cap_violation = True
        print(f"{n:>5} {p:>14} {str((a,b)):>10} {d:>4} {len(B):>5} "
              f"{nt:>13} {dist:>14} {str(is_cap):>6}")

print()
print("HORN H1 verdict:", "B is NOT 3-AP-free (contains genuine 3-APs) -> cap hypothesis FALSE"
      if any_cap_violation else "B happened to be cap-free in all tested directions")
print()

print("(H2) CLP/Ellenberg-Gijswijt cap saving is DIMENSIONAL; vacuous in cyclic Z/p.\n")
print("  CLP (Z/4^N): 3-AP-free  <= 4^{0.926 N}; saving exponent in AMBIENT DIM N.")
print("  EG (F_3^N):  3-AP-free  <= (2.7551)^N;  saving exponent in AMBIENT DIM N.")
print("  Z/p is the N=1 cyclic group. Best PROVEN 3-AP-free bound in Z/p is")
print("  Behrend/Bloom-Sisask:  r_3(p) = p / exp(c (log p)^t),  t in (0,1).")
print("  That is p^{1-o(1)} -- NOT p^{1-c} for any FIXED c>0.\n")
print(f"{'n':>5} {'p':>14} {'budget n':>9} {'L3 |B|<=n':>10} "
      f"{'Behrend r_3(p)~p^{1-o(1)}':>26} {'claimed p^{1-c},c=0.1':>22}")
for n in [16, 32, 64, 128, 1024, 2**20, 2**30]:
    # use p ~ n^4 (prize-ish beta=4); for huge n we just compute analytically
    p = n**4
    budget = n
    L3 = n  # |B| <= n exactly (= n/gcd <= n) from the coset law
    # Behrend-type lower bound on max cap size in Z/p (what 3-AP-free CAN reach):
    # p / exp(c sqrt(log p)) with c ~ 2 sqrt(2 log 2) ~ 2.35
    lp = log(p)
    behrend = p / exp(2.35 * (lp ** 0.5))
    claimed = p ** 0.9  # the conjecture's "p^{1-c}", c=0.1
    print(f"{n:>5} {p:>14} {budget:>9} {L3:>10} {behrend:>26.3e} {claimed:>22.3e}")

print()
print("HORN H2/H3 verdict: even the CLAIMED p^{1-c} (>> n) is WEAKER than the")
print("trivial L3 coset size |B| <= n. A cap bound of size ~p^{1-c} caps NOTHING")
print("the orbit law L3 does not already give for free, and the 3-AP-freeness")
print("that would be needed is FALSE (H1). The open quantity is the MULTIPLICITY")
print("N_pencil (how many codewords realize the same bad alpha), not |B| -- which")
print("a size bound on a 3-AP-free set cannot address (L3: I = N * S; cap touches S only).")
