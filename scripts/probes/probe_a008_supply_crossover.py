#!/usr/bin/env python3
"""
A008 (probabilistic-method good-prime certificate) — the EXACT supply-vs-badcount
crossover, and WHY the binding rung lands on the wrong side of it.

KKH26 Lemma 2 (`kkh26_good_prime_paper_form`) gives a good prime p = Theta(n^beta),
p = 1 mod n, when the bad-prime budget is strictly below the TZ supply:

    hcount :  a^2 * logM / (beta * log n)  <  supply

with (thin 2-power tower, prize n = s = 2^mu):
    logM   = (s/2) * mu * log 2 = (s/2) * log s          [natAbs_resultant_cyclotomic_le]
    log n  = log s
    supply = n^{beta-1}                                  [Thorner-Zaman, unconditional, beta>12/5]

=> badcount = a^2 * (s/2) * log s / (beta * log s) = a^2 * s / (2 beta).

So the crossover is purely a CONDITION ON a (the count of signed sum-polynomials):

    badcount < supply
      <=>  a^2 * s / (2 beta) < s^{beta-1}
      <=>  a^2 < 2 beta * s^{beta-2}.                    [THE EXACT THRESHOLD]

The threshold a*^2 = 2 beta s^{beta-2} is POLYNOMIAL in s.

A008's hope: a random qualifying prime is good w.h.p. using ONLY the proven upper
bound. This probe shows the hope is realizable ONLY when a is sub-threshold, and
that the ACTUAL binding-rung a is EXPONENTIAL, blowing the threshold:

    a(r) = 2^r * C(s/2, r),   binding rung r = rho*s, rho = 1/4.

We verify (one sweep, exact, prize tower s = 2^mu, mu = 4..30, never n = q-1):
  (1) the exact crossover a^2 < 2 beta s^{beta-2} holds iff badcount < supply;
  (2) the binding-rung a is exponential => a^2 >> 2 beta s^{beta-2} (margin -> oo),
      so hcount FAILS at the binder for every fixed beta. The probabilistic method
      cannot avoid a finer supply LOWER bound: it is killed by the EXPONENTIAL
      collision-pair count at the binding rung, not by the supply being too thin.
"""
import math
from math import comb, log, sqrt

def run(beta):
    print(f"\n=== beta = {beta}  (threshold a*^2 = 2*beta*s^(beta-2)) ===")
    print(f"{'mu':>3} {'s=2^mu':>10} {'a*^2=thresh':>14} {'a_bind=2^r C(s/2,r)':>22} "
          f"{'a_bind^2 / thresh':>18} {'hcount@a_bind':>14}")
    for mu in range(4, 31):
        s = 2 ** mu
        thresh = 2.0 * beta * (s ** (beta - 2.0))     # a*^2
        r = s // 4                                     # binding rung rho=1/4
        # a_bind = 2^r * C(s/2, r); huge -> work in logs
        log_a = r * log(2.0) + math.lgamma(s/2 + 1) - math.lgamma(r + 1) - math.lgamma(s/2 - r + 1)
        log_a2 = 2.0 * log_a
        log_thresh = log(thresh)
        log_ratio = log_a2 - log_thresh                # log(a_bind^2 / thresh)
        hcount_holds = log_a2 < log_thresh             # would good-prime exist?
        # display a_bind compactly via its log10
        log10_abind = log_a / log(10.0)
        print(f"{mu:>3} {s:>10} {thresh:>14.4g} {('1e'+format(log10_abind,'.1f')):>22} "
              f"{('1e'+format(log_ratio/log(10),'.1f')):>18} {str(hcount_holds):>14}")

def verify_crossover_equivalence(beta):
    """Sanity: badcount < supply  <=>  a^2 < 2 beta s^{beta-2}, on sub-threshold a."""
    print(f"\n--- crossover equivalence check (beta={beta}) ---")
    ok = True
    for mu in range(4, 20):
        s = 2 ** mu
        log2 = log(2.0)
        logM = (s/2.0) * mu * log2
        supply = s ** (beta - 1.0)
        thresh = 2.0 * beta * (s ** (beta - 2.0))
        # test several a around the threshold
        a_star = sqrt(thresh)
        for a in (a_star * 0.5, a_star * 0.99, a_star * 1.01, a_star * 2.0):
            badcount = (a*a) * logM / (beta * log(s))
            lhs = badcount < supply
            rhs = (a*a) < thresh
            if lhs != rhs:
                ok = False
                print(f"  MISMATCH mu={mu} a={a:.3g}: badcount<supply={lhs} a^2<thresh={rhs}")
    print(f"  crossover equivalence: {'PASS' if ok else 'FAIL'}")

if __name__ == "__main__":
    verify_crossover_equivalence(4.0)
    verify_crossover_equivalence(5.27)
    for beta in (2.5, 4.0, 5.27):
        run(beta)
    print("\nVERDICT: the exact crossover is a^2 < 2*beta*s^(beta-2) (polynomial threshold).")
    print("The binding-rung a = 2^r*C(s/2,r) is EXPONENTIAL, so a^2/threshold -> oo:")
    print("hcount FAILS at the binder for every fixed beta. A008's probabilistic method")
    print("is killed by the EXPONENTIAL collision-pair count, NOT by thin supply.")
