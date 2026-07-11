#!/usr/bin/env python3
"""
PROBE C27 (issue #444): Hasse-Davenport Dyadic-Lifting Telescope.

CONJECTURE C27 claims: the 2-power Gauss-sum tower mu_2 c ... c mu_{2^mu}, linked by
Hasse-Davenport lifting telescopes, expresses M(mu_n) = max_{a!=0}|Sum_{x in mu_n} e_p(ax)|
as a PRODUCT of Jacobi sums (each modulus sqrt(p)), the 2^mu levels contributing
sqrt(log p), giving M(mu_n) <= sqrt(n log p) PAST Johnson, via a PURELY MULTIPLICATIVE
recursion (claimed non-analytic, hence outside the moment-wall impossibility map).

REDUCES-TO (per the conjecture): Hasse-Davenport product/lifting (exact) + Jacobi
identities tau(chi)tau(chi') = J(chi,chi') tau(chi chi'), |J| = sqrt(p) (proven).

=============================================================================
THE STRUCTURAL POINT being tested (the suspected horn = reduces/secretly-open):
=============================================================================
The Gauss period eta_a = Sum_{x in H} e_p(a x) is an algebraic integer in Q(zeta_p).
Its conjugates under Gal(Q(zeta_p)/Q) = (Z/p)^x / H are exactly the m = (p-1)/n
DISTINCT periods {eta_c}. So:

    M(H) = max_{a != 0} |eta_a| = HOUSE(eta)   (max conjugate modulus).

Every PRODUCT/MULTIPLICATIVE telescope (Hasse-Davenport, Jacobi-sum identities,
norms) can only ever compute SYMMETRIC FUNCTIONS of the conjugates -- chiefly the
NORM  N = prod_c eta_c.  Indeed:
    tau(chi)tau(chibar) = chi(-1) p           (orthogonality / |tau|=sqrt p)
    prod over a Galois orbit of tau(chi)  ~  Jacobi-sum products of modulus p^{#/2}.
These pin |N| = prod_c |eta_c|.  By AM-GM the geometric mean of the |eta_c| is
    |N|^{1/m} = (prod_c |eta_c|)^{1/m}  ~  sqrt(n)   (the L^2-average scale).
This LOWER-bounds the house:  HOUSE(eta) >= |N|^{1/m} ~ sqrt(n).
It does NOT upper-bound it: the house exceeds the geometric mean by exactly the
CONJUGATE VARIATION (spread of the |eta_c|), which is the sqrt(log p) factor and is
INVISIBLE to any product. A product is blind to WHICH conjugate is largest.

So a telescope of Jacobi sums delivers N (a symmetric function), and N gives only
the geometric-mean / L^2 scale sqrt(n) = the Johnson-radius scale -- NOT the sup.

PREDICTIONS if the conjecture is on the "reduces / secretly-open" horn:
  P1. |N|^{1/m} ~ sqrt(n) (geometric mean is the average, ~ Johnson scale).
  P2. HOUSE / geomMean = M(H)/|N|^{1/m} GROWS (it is ~ sqrt(log(p/n))), i.e. the
      product MISSES the prize factor; the gap is real and grows with p.
  P3. The product/telescope value (Jacobi/norm) is INDEPENDENT of any argument
      data: two fields with identical |N| can have wildly different HOUSE -- so the
      telescope cannot determine M(H). (We exhibit the spread of HOUSE at fixed n.)
  P4. M(H) is NOT <= sqrt(n log p) by anything the telescope produces: the only
      bound a symmetric product yields is M(H) >= sqrt(n) (a LOWER bound, useless
      as an upper bound), and M(H) <= n (trivial). The claimed UPPER bound
      sqrt(n log p) is the TRUE value but NOT delivered by the product.

If P1-P4 hold, C27 = reduces-to-johnson (the product only reaches the sqrt(n) /
geometric-mean / Johnson scale; the sup needs the archimedean argument distribution
that no multiplicative telescope can supply) -- equivalently the prize step is
SECRETLY OPEN (the missing sqrt(log p) house-vs-norm gap = the BGK archimedean core).

CONSTRAINTS (honesty contract): proper subgroup mu_n, p PRIME, p >> n^3, NEVER n=p-1.
"""

import cmath
import math
from sympy import isprime, primitive_root


def find_prime(mu, mult_min):
    """Prime p with 2^mu | p-1, p > n^3, p PROPER (n != p-1). mult_min controls thinness."""
    n = 1 << mu
    m = max(mult_min, n * n + 2)  # ensures p > n^3 when m ~ n^2, and proper (m>1)
    while True:
        p = m * n + 1
        if p > n ** 3 and isprime(p):
            return p, n, m
        m += 1


def subgroup(p, n):
    g = primitive_root(p)
    f = (p - 1) // n
    gf = pow(g, f, p)
    H, cur = [], 1
    for _ in range(n):
        H.append(cur)
        cur = (cur * gf) % p
    assert len(set(H)) == n
    return g, f, H


def all_periods(p, n, g, f, H):
    """All m=(p-1)/n distinct conjugate periods eta_c (one per coset of H in F_p^x).
    eta_c = Sum_{x in H} e_p(g0^c * x). Returns the list of complex eta_c."""
    two_pi_i = 2j * math.pi
    etas = []
    coset_rep = 1
    for c in range(f):  # f = m = number of distinct conjugates
        s = sum(cmath.exp(two_pi_i * ((coset_rep * x) % p) / p) for x in H)
        etas.append(s)
        coset_rep = (coset_rep * g) % p
    return etas


def main():
    print("=" * 92)
    print("PROBE C27: Hasse-Davenport Dyadic-Lifting Telescope -- house vs norm test")
    print("=" * 92)
    print("M(H)=HOUSE(eta); product telescope -> NORM N -> geomMean ~ sqrt(n) (Johnson scale).")
    print("Test P1 geomMean~sqrt n; P2 house/geomMean grows ~ sqrt(log(p/n)); P3 house not")
    print("determined by N (spread at fixed n,|N|); P4 only LOWER bound from product.\n")

    print(f"{'mu':>3} {'n':>5} {'p':>10} {'p/n^3':>7} {'m=idx':>7} "
          f"{'HOUSE':>9} {'geoMean':>9} {'min|eta|':>9} "
          f"{'H/sqn':>7} {'gm/sqn':>7} {'H/gm':>7} {'sqLog':>7} {'H/sqnlogp':>9}", flush=True)

    # Sweep n=2^mu and, for each, several primes p >> n^3, all PROPER subgroups.
    rows = []
    for mu in [3, 4, 5, 6]:
        n = 1 << mu
        primes = []
        base_m = n * n + 1
        m = base_m
        while len(primes) < 5:
            p = m * n + 1
            if p > n ** 3 and isprime(p) and (p - 1) != n:
                primes.append(p)
            m += 1
        for p in primes:
            g, f, H = subgroup(p, n)
            etas = all_periods(p, n, g, f, H)
            mags = [abs(e) for e in etas]
            house = max(mags)
            mn = min(mags)
            logN = sum(math.log(mm) for mm in mags if mm > 1e-12)
            gm = math.exp(logN / f)  # |N|^{1/m}, geometric mean
            sqn = math.sqrt(n)
            sq_log = math.sqrt(math.log(p / n))
            target = math.sqrt(n * math.log(p))
            rows.append((mu, n, p, house, gm, mn))
            print(f"{mu:>3} {n:>5} {p:>10} {p/n**3:>7.2f} {f:>7} "
                  f"{house:>9.3f} {gm:>9.3f} {mn:>9.3f} "
                  f"{house/sqn:>7.3f} {gm/sqn:>7.3f} {house/gm:>7.3f} {sq_log:>7.3f} "
                  f"{house/target:>9.3f}", flush=True)

    print("\n" + "-" * 92)
    print("P3 -- HOUSE is NOT determined by the product (norm/Jacobi telescope):")
    print("at FIXED n, geomMean (=|N|^{1/m}, all a multiplicative product can give) clusters")
    print("near sqrt(n), but HOUSE varies. Show min/max HOUSE and geomMean per n:")
    from collections import defaultdict
    byn = defaultdict(list)
    for mu, n, p, house, gm, mn in rows:
        byn[n].append((house, gm))
    print(f"{'n':>5} {'#p':>4} {'HOUSE_min':>10} {'HOUSE_max':>10} {'gm_min':>8} {'gm_max':>8} "
          f"{'gm_spread':>10} {'house_spread':>13}", flush=True)
    for n in sorted(byn):
        hs = [h for h, _ in byn[n]]
        gms = [g for _, g in byn[n]]
        print(f"{n:>5} {len(hs):>4} {min(hs):>10.3f} {max(hs):>10.3f} "
              f"{min(gms):>8.3f} {max(gms):>8.3f} "
              f"{(max(gms)-min(gms)):>10.4f} {(max(hs)-min(hs)):>13.4f}", flush=True)

    print("\n" + "=" * 92)
    print("VERDICT LOGIC:")
    print("  * geomMean/sqrt(n) ~ 1     => P1: the product (norm) only sees the sqrt(n)")
    print("                                geometric-mean = the JOHNSON-radius L^2 scale.")
    print("  * house/geomMean = house/|N|^{1/m} > 1 and tracking sqrt(log(p/n)) => P2: the")
    print("                                prize factor sqrt(log p) is the CONJUGATE SPREAD,")
    print("                                which a product is structurally BLIND to.")
    print("  * gm_spread << house_spread => P3: |N| (all the telescope yields) does NOT")
    print("                                determine HOUSE = M(H).")
    print("  => Hasse-Davenport/Jacobi telescope computes a SYMMETRIC FUNCTION (norm) =>")
    print("     LOWER bound M(H) >= sqrt(n) (Johnson scale) only. The claimed UPPER bound")
    print("     sqrt(n log p) is NOT delivered: the sup = HOUSE needs the archimedean")
    print("     argument distribution {arg tau(chi_j)} = the BGK open core (secretly-open),")
    print("     and the best the multiplicative recursion reaches is the Johnson sqrt(n)")
    print("     geometric mean (reduces-to-johnson).")


if __name__ == "__main__":
    main()
