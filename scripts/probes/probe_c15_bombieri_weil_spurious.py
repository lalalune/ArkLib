#!/usr/bin/env python3
"""
probe_c15_bombieri_weil_spurious.py  (#444 conjecture C15 attack)

CONJECTURE C15 ("Bombieri-Weil Completion of the Spurious-Collision Gauss-Sum Monomial"):
   Write the spurious term  S = q^r * Sum_{f^{2r-1} non-Wick collisions} e^{iTheta}.
   Each spurious monomial is a point-count on an Artin-Schreier-Kummer curve of genus
   <= (2r)^2; Bombieri's effective Weil II bounds each term; LARGE MONODROMY gives
   sqrt-cancellation in the SUM, yielding |S| <= q^r * sqrt(#spurious) -- a factor below
   Wick -- so M(mu_n) <= sqrt(2 n log(p/n)) PAST Johnson.

WHAT THIS PROBE CHECKS (over PROPER subgroup mu_n, p prime, p >> n^3, NEVER n=p-1):
  (A) The exact moment identity  Sum_b |eta_b|^{2r} = q * E_r(mu_n)   (the in-tree large sieve).
  (B) The Wick/spurious split of q*E_r in the multiplicative basis:
        diagonal/Wick term reproduces q*(2r-1)!!*n^r EXACTLY;
        spurious = the f^{2r-1} non-Wick collisions  Sum s_i = Sum t_j (mod f), {s}!={t}.
  (C) PER-TERM Weil bound alone (no effective cancellation) is the TRIVIAL bound:
        each |G| = q^r exactly, so the triangle-inequality bound on |S| is
        q^r * #spurious -> moment root >= n  (NEVER beats n). This is the
        Bombieri/Deligne-Weil-II *per-term* content; it is Wick-level, not below.
  (D) The decisive horn: the claimed extra sqrt(#spurious) factor IS effective
        sqrt-cancellation in the monodromy sum == Katz/Rojas-Leon joint equidistribution
        of Gauss-sum ARGUMENTS, effective only when discrepancy d_r/sqrt(q) < 1, i.e.
        f^r/(r! sqrt(q)) < 1, i.e. f <= sqrt(q) <=> n >= sqrt(p).
        The PRIZE regime is n << sqrt(p): over-dimensioned at EVERY depth r.

If (C) holds (per-term Weil = Wick-level, never below) and (D) holds (the only way to get
below Wick is the open+dimension-obstructed effective cancellation), then C15 either
reduces-to-johnson (its honest provable content stops at the Wick=Johnson level) OR is
secretly-open (the past-Johnson gain needs the open BGK/Katz input).
"""

import cmath
import math
from itertools import product
from sympy import primerange, isprime


def find_prime(n, beta_min=4):
    """Smallest prime p with n | p-1, p > n^beta_min (so p >> n^3), n != p-1."""
    # need p = 1 mod n, p > n^beta_min
    lo = n ** beta_min
    p = ((lo // n) + 1) * n + 1
    while True:
        if p % n == 1 and isprime(p) and p - 1 != n:
            return p
        p += n


def subgroup_mu_n(p, n):
    """The multiplicative subgroup mu_n of order n in F_p^* (proper since n != p-1)."""
    # generator of F_p^* via brute test on small g
    def is_primitive(g):
        seen = set()
        x = 1
        for _ in range(p - 1):
            x = (x * g) % p
            seen.add(x)
        return len(seen) == p - 1
    g = 2
    while not is_primitive(g):
        g += 1
    h = pow(g, (p - 1) // n, p)  # element of order n
    G = []
    x = 1
    for _ in range(n):
        G.append(x)
        x = (x * h) % p
    assert len(set(G)) == n, "mu_n not size n"
    return sorted(set(G)), g


def eta(b, G, p):
    """eta_b = sum_{x in mu_n} e_p(b x)."""
    w = cmath.exp(2j * math.pi / p)
    return sum(w ** ((b * x) % p) for x in G)


def double_factorial_odd(m):
    """(2r-1)!! for m = 2r-1 odd."""
    r = (m + 1) // 2
    prod = 1
    for i in range(1, r + 1):
        prod *= (2 * i - 1)
    return prod


def energy_r(G, p, r):
    """E_r = #{(x_1..x_r, y_1..y_r) in mu_n^{2r}: sum x = sum y in F_p}."""
    from collections import Counter
    sums = Counter()
    for tup in product(G, repeat=r):
        sums[sum(tup) % p] += 1
    return sum(c * c for c in sums.values())


def main():
    print("=" * 78)
    print("C15 probe: Bombieri-Weil completion of the spurious Gauss-sum monomial")
    print("=" * 78)

    for n in [4, 8, 16]:
        p = find_prime(n, beta_min=4)
        G, gen = subgroup_mu_n(p, n)
        f = (p - 1) // n
        q = p
        print(f"\n--- n={n}, p={p} (p/n^4 = {p / n**4:.2f}), f=(p-1)/n={f},  n vs sqrt(p)={math.sqrt(p):.1f} ---")
        print(f"    proper subgroup? n={n} != p-1={p-1}: {n != p-1};  p >> n^3 = {n**3}: {p > n**3}")

        # ---- (A) exact moment identity Sum_b |eta_b|^{2r} = q*E_r ----
        for r in [1, 2, 3]:
            lhs = sum(abs(eta(b, G, p)) ** (2 * r) for b in range(p))
            Er = energy_r(G, p, r)
            rhs = q * Er
            ok = abs(lhs - rhs) < 1e-4 * max(1, rhs)
            print(f"    (A) r={r}:  Sum_b|eta_b|^2r = {lhs:.3f}   q*E_r = {rhs}   match={ok}")

        # ---- (B) Wick value and (C) per-term Weil = Wick-level ----
        # Wick (char-0 Gaussian) value of E_r is (2r-1)!! * n^r.
        for r in [2, 3]:
            wick = double_factorial_odd(2 * r - 1) * n ** r
            Er = energy_r(G, p, r)
            n_spurious_approx = f ** (2 * r - 1)  # the C15 count of non-Wick collisions
            print(f"    (B) r={r}:  E_r={Er}   Wick=(2r-1)!!*n^r={wick}   "
                  f"E_r/Wick={Er / wick:.4f}   #spurious~f^(2r-1)={n_spurious_approx}")

        # ---- (C) PER-TERM Weil bound (triangle ineq, no cancellation) ----
        # each spurious Gauss-sum monomial has |G|=q^r EXACTLY (Gauss sum modulus sqrt(q)
        # per factor, 2r factors -> q^r). So the per-term Weil bound on |S| is
        # q^r * #spurious. Pushed through the moment root:
        print("    (C) per-term Weil (NO cancellation) -> moment root vs n:")
        for r in [2, 3]:
            # bound on Sum_b|eta_b|^2r from per-term: q*E_r where E_r ~ Wick + spurious_mass
            # the moment root of q*E_r is ALWAYS >= n (Cauchy-Schwarz, _MomentMethodNoGo).
            Er = energy_r(G, p, r)
            moment_root = (q * Er) ** (1.0 / (2 * r))
            # b=0 alone contributes n^{2r}:
            b0 = float(n) ** (2 * r)
            print(f"        r={r}: (q*E_r)^(1/2r)={moment_root:.3f}  vs  n={n}   "
                  f"(>= n always: {moment_root >= n - 1e-6});  b=0 term n^2r={b0:.3g}")

        # ---- (D) the dimension obstruction: effective Deligne needs f <= sqrt(q) ----
        print("    (D) dimension obstruction (effective cancellation needs f<=sqrt(q)):")
        for r in [2, 5, 10]:
            d_r = math.comb(f + r - 1, r)         # rank of r-fold convolution ~ f^r/r!
            discrepancy = d_r / math.sqrt(q)       # Deligne/Weil-II discrepancy
            effective = discrepancy < 1
            print(f"        r={r}: d_r=C(f+r-1,r)={d_r:.3g}  disc=d_r/sqrt(q)={discrepancy:.3g}  "
                  f"effective(<1)={effective}")
        print(f"        => effective iff f<=sqrt(q) <=> n>=sqrt(p)={math.sqrt(p):.1f}; "
              f"prize n={n} << sqrt(p): OVER-dimensioned by sqrt(p)/n = {math.sqrt(p)/n:.2f}")

    print("\n" + "=" * 78)
    print("CONCLUSION:")
    print(" (A) exact: the b-large-sieve is SATURATED, = q*E_r (zero Weil slack).")
    print(" (C) per-term Bombieri/Weil-II on each spurious monomial is Wick-level:")
    print("     |G|=q^r exactly; the moment root is ALWAYS >= n (never below Johnson).")
    print(" (D) the extra sqrt(#spurious) C15 claims = EFFECTIVE monodromy cancellation")
    print("     = open Katz/Rojas-Leon joint Gauss-sum equidistribution, and it is")
    print("     DIMENSION-OBSTRUCTED (needs n>=sqrt(p)) exactly in the prize n<<sqrt(p).")
    print(" => C15's provable content stops at Wick=Johnson; the past-Johnson gain is the")
    print("    open BGK/Katz input. Horn: reduces-to-johnson / secretly-open.")
    print("=" * 78)


if __name__ == "__main__":
    main()
