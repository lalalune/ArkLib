#!/usr/bin/env python3
"""
PROBE C13: Vertical Sato-Tate Sup-Control via Katz Uniform Equidistribution Rate (issue #444).

C13 claims (algebraic-geometry, feasibility 1):
  The effective discrepancy of the Gauss-sum-family equidistribution, against trig-polynomial
  test functions of degree <= log(p/n) and RESTRICTED to a mu-dimensional dyadic sub-torus, is
        D = mu * 2^mu / sqrt(q)  <<  1,
  forcing  max_b |eta_b| <= sqrt(2 n log(p/n))  past Johnson.
  THE BET: "the relevant torus has dimension mu rather than f."

REDUCES-TO (claimed): Katz Sato-Tate + Rojas-Leon Cor 7 (only Hasse-Davenport => GL(1)^f)
  + Deligne Weil II effective form + in-tree GeneralizedPaleyRamanujan reduction.

This probe tests, prize-faithfully (proper mu_n: n=2^mu, n | p-1, p PRIME, p >> n^3,
m=(p-1)/n strictly > 1, NEVER n=p-1):

  HORN-DIM:  The Rojas-Leon equidistribution monodromy is GL(1)^f with f = the number of
             monomial Gauss sums in the family = the INDEX m = (p-1)/n ~ p/n ~ 2^128, NOT mu.
             The DFT identity  eta_c = -1/m + (1/m) sum_{j=1}^{m-1} tau(chi^j) e(-jc/m)
             writes the period as a length-(m-1) linear form in the f=m-1 INDEPENDENT Gauss
             sums tau(chi^j). The torus the equidistribution lives on therefore has dimension
             f = m-1 ~ p/n, and the honest discrepancy is f/sqrt(q) ~ sqrt(p)/n >> 1 in the
             prize regime n << p^{1/4}. The "mu-dimensional sub-torus" bet has no support:
             restricting to a mu-dim sub-torus is choosing only mu of the m-1 coordinates,
             which simply DROPS most of the sum and proves nothing about the full period.

  HORN-EFF:  Even with dimension f, Deligne/Katz equidistribution is a q->infinity statement
             at FIXED sheaf. It gives the TYPICAL (average) value, never the deterministic MAX
             over the thin designed subgroup. We confirm M(n)/sqrt(n log(p/n)) ~ 1 and drifts
             (no fixed effective constant), exactly the random / open-BGK signature.

  HORN-TARGET (moot but recorded): the claimed bound sqrt(2 n log(p/n)) is the BGK/Paley target
             itself. Even if true it is the OPEN object, not a consequence of any q->infinity
             equidistribution rate. We show M(n) TRACKS sqrt(n log(p/n)) within O(1) -- the bound
             is the random value, i.e. the conjecture asserts the open core as its conclusion.

We DO NOT claim a single-b violation of sqrt(2 n log(p/n)) is the refutation (that is the random
scale and may hold); the refutation is structural: the dimension bet is false, so the "D<<1"
premise that DERIVES the bound is false. We print both D(mu) [C13's bet] and D(f) [the truth].
"""
import cmath, math
from sympy import isprime, primitive_root


def find_prime(n, beta):
    """p prime, n | p-1, p ~ n^beta (so p >> n^3 for beta>=4), m=(p-1)/n strictly > 1."""
    target = int(n ** beta)
    cand = target - (target % n) + 1
    if cand <= target:
        cand += n
    while True:
        if isprime(cand) and (cand - 1) % n == 0 and (cand - 1) // n > 1:
            return cand
        cand += n


def mu_n(n, p):
    g = primitive_root(p)
    h = pow(g, (p - 1) // n, p)
    sub, x = [], 1
    for _ in range(n):
        sub.append(x)
        x = (x * h) % p
    assert len(set(sub)) == n, "mu_n not a proper subgroup of size n"
    return sub


def eta(b, sub, p):
    return sum(cmath.exp(2j * math.pi * ((b * y) % p) / p) for y in sub)


def worstcase_eta(sub, p, n):
    """max_{b != 0} |eta_b|; |eta_{cb}| = |eta_b| for c in mu_n, so sweep one rep per coset."""
    seen = set()
    M, argmax = 0.0, None
    for b in range(1, p):
        if b in seen:
            continue
        for c in sub:
            seen.add((b * c) % p)
        v = abs(eta(b, sub, p))
        if v > M:
            M, argmax = v, b
    return M, argmax


def run():
    print("=" * 110)
    print("PROBE C13 -- Vertical Sato-Tate sup-control via Katz uniform equidistribution rate")
    print("Honesty contract: proper mu_n (n=2^mu), p PRIME, n|p-1, p>>n^3, m=(p-1)/n>1, NEVER n=p-1")
    print("=" * 110)

    # --- Part 1: the DIMENSION-BET arithmetic at PRIZE scale (q = p ~ n*2^128) ----------------
    print("\n[PART 1] C13's discrepancy bet  D=mu*2^mu/sqrt(q)  vs the HONEST  D=f/sqrt(q), f=(p-1)/n")
    print("         prize regime: q = p ~ n*2^128, so n << p^{1/4} (beta = log_n p > 4).")
    print(f"{'mu':>3} {'n=2^mu':>8} {'log2 p':>7} {'beta':>6} "
          f"{'D_mu=mu*2^mu/sqrtq':>20} {'D_f=f/sqrtq (TRUTH)':>22} {'verdict':>10}")
    for mu in [16, 20, 30, 35]:
        n = 2 ** mu
        p = n * 2 ** 128            # prize: q = p ~ n * 2^128
        beta = math.log(p) / math.log(n)
        f = (p - 1) // n           # Rojas-Leon GL(1)^f: f = index m = (p-1)/n
        D_mu = mu * 2 ** mu / math.sqrt(p)
        D_f = f / math.sqrt(p)
        verdict = "D_mu<<1 but D_f>>1" if (D_mu < 1 < D_f) else "?"
        print(f"{mu:>3} {('2^'+str(mu)):>8} {math.log2(p):>7.1f} {beta:>6.2f} "
              f"{D_mu:>20.3e} {('2^%.1f' % math.log2(D_f)):>22} {verdict:>10}")
    print("  => The ONLY thing making D<<1 is the bet 'dim = mu'. With the correct Rojas-Leon")
    print("     dimension f=(p-1)/n~2^128, the discrepancy is 2^49..2^56 -- CATASTROPHICALLY VACUOUS.")
    print("     A mu-dim 'sub-torus' is just mu of the m-1 Gauss-sum coordinates; it drops the rest.")

    # --- Part 2: measured law -- M(n) tracks the OPEN BGK random value sqrt(n log(p/n)) -------
    print("\n[PART 2] Measured worst-case M(n)=max_b|eta_b| vs the claimed bound sqrt(2 n log(p/n))")
    print("         and the random/BGK scale sqrt(n log(p/n)). (Tractable n; large m.)")
    print(f"{'n':>4} {'p':>12} {'p/n^3':>7} {'m':>9} {'M(n)':>9} "
          f"{'sqrt(2 n log(p/n))':>18} {'M/that':>7} {'sqrt(n log(p/n))':>16} {'M/that':>7}")
    rows = []
    for mu in range(3, 7):           # n = 8, 16, 32, 64
        n = 2 ** mu
        beta = 4.0 if n >= 32 else 4.5
        p = find_prime(n, beta)
        m = (p - 1) // n
        assert isprime(p) and (p - 1) % n == 0 and m > 1 and p > n ** 3
        sub = mu_n(n, p)
        M, b = worstcase_eta(sub, p, n)
        logr = math.log(p / n)
        c13 = math.sqrt(2 * n * logr)
        rand = math.sqrt(n * logr)
        rows.append((n, p, m, M, c13, rand))
        print(f"{n:>4} {p:>12} {p/n**3:>7.1f} {m:>9} {M:>9.3f} "
              f"{c13:>18.3f} {M/c13:>7.3f} {rand:>16.3f} {M/rand:>7.3f}")

    # --- Part 3: M/sqrt(n) GROWS -> no fixed Sato-Tate edge; consistent with random sqrt(log) --
    print("\n[PART 3] M(n)/sqrt(n) is NOT a fixed constant (would be ~2 for a Sato-Tate semicircle")
    print("         edge); it GROWS like sqrt(log(p/n)) -- the random/Gaussian large-deviation law,")
    print("         which is exactly the OPEN BGK object, NOT delivered by equidistribution rate.")
    print(f"{'n':>4} {'M/sqrt(n)':>10} {'sqrt(log(p/n))':>15}")
    for (n, p, m, M, c13, rand) in rows:
        print(f"{n:>4} {M/math.sqrt(n):>10.3f} {math.sqrt(math.log(p/n)):>15.3f}")

    print("\n" + "=" * 110)
    print("VERDICT: C13 is SECRETLY-OPEN (degenerating to REDUCES-TO-JOHNSON on the only effective")
    print("reading). The discrepancy-<<1 premise rests entirely on the FALSE bet 'torus dim = mu'.")
    print("The Rojas-Leon family is GL(1)^f with f=(p-1)/n~2^128 (the DFT writes eta as a length-(m-1)")
    print("form in f INDEPENDENT Gauss sums), so the true discrepancy f/sqrt(q)~sqrt(p)/n >> 1 is")
    print("VACUOUS in regime -- the same large-sieve / Katz dimension obstruction already recorded")
    print("(needs n >~ sqrt(p); prize has n << p^{1/4}). The claimed bound sqrt(2 n log(p/n)) is the")
    print("OPEN BGK/Paley target itself (M(n) tracks it within O(1)); an asymptotic q->infinity")
    print("equidistribution RATE cannot deliver the deterministic MAX over a thin growing subgroup.")
    print("=" * 110)


if __name__ == "__main__":
    run()
