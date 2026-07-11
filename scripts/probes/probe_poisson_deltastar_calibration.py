#!/usr/bin/env python3
"""
probe_poisson_deltastar_calibration.py  (#407)

CALIBRATION of the NEW factorial-moment / Poisson-concentration reframing of delta*.

CLAIM under test (the bridge that escapes the proven-dead energy sqrt(n) deficit):
  The far-line incidence  I(delta) = max over the n^2 MONOMIAL directions (X^a,X^b) of
  L = #{gamma : X^a + gamma X^b is delta-close to RS[k]}.  If L is sub-Poisson over that
  POLY-SIZE (n^2) family, then a Poisson tail union-bound gives
        I(delta*) = mu * (1 + o(1)),   mu = E[L] = q^{k+1} V_{delta n} / q^n,
  i.e. WORST-CASE = AVERAGE to leading order, because the family is poly-size (n^2), not q^n.

TWO things to verify numerically, in the TRUE prize regime (q = n^beta, beta = 1 + 128/log2 n,
so q ~ n*2^128 >> n^3; NEVER the full group):
  (A) The average-term threshold  delta_avg := { delta : mu(delta) = q*eps* = n }
      reproduces the issue's conjectured  delta*_conj = 1 - rho - H(rho)/(beta*log2 n).
      If these AGREE, the conjectured delta* IS the average-term value (first moment), and the
      whole prize = "does the incidence concentrate at delta_avg" = the sub-Poisson gate.
  (B) At delta_avg (where mu = n), the Poisson tail over M = n^2 monomial lines gives
      worst-case a* with  a*/mu -> 1  (concentration), i.e. M * P(Poisson(mu) >= a*) ~ 1 at
      a* = n + O(sqrt(n log n)) = n(1+o(1)).  So sub-Poisson => I(delta*) = n(1+o(1)) = exact pin.

This is a calibration of the MODEL, not a proof.  It checks the reframing is quantitatively
self-consistent with the in-tree conjectured delta* before we formalize the bridge & refute
sub-Poisson against the KKH26 heavy line.
"""
import math
from math import log2, log, lgamma, comb


def H2(x):
    if x <= 0 or x >= 1:
        return 0.0
    return -x * log2(x) - (1 - x) * log2(1 - x)


def log_q_ball_volume(n, w, beta, logq):
    """log_q V_w, V_w = sum_{i<=w} C(n,i)(q-1)^i ~ C(n,w)(q-1)^w (top term dominates for q huge)."""
    if w <= 0:
        return 0.0
    # log2 of top term C(n,w) + w*log2(q-1); divide by log2 q
    log2_top = log2_binom(n, w) + w * logq  # logq is log2 q here ~ log2(q-1)
    return log2_top / logq


def log2_binom(n, k):
    if k < 0 or k > n:
        return float('-inf')
    return (lgamma(n + 1) - lgamma(k + 1) - lgamma(n - k + 1)) / log(2)


def mu_log_q(n, rho, delta, beta, logq):
    """log_q mu(delta), mu = q^{k+1} V_{delta n}/q^n, k=rho n.  Returns log base q."""
    k = rho * n
    w = delta * n
    # log_q V_w = (log2 C(n,w) + w*log2(q-1)) / log2 q ; log2(q-1)~logq
    log_q_V = (log2_binom(n, round(w)) + w * logq) / logq
    return (k + 1) + log_q_V - n  # log_q of q^{k+1} V / q^n


def poisson_log_sf(mu, a):
    """log P(Poisson(mu) >= a) via upper tail; use Chernoff a>mu: a - mu - a*log(a/mu) (natural log)."""
    if a <= mu:
        return 0.0
    return a - mu - a * log(a / mu)


def main():
    print(f"{'n':>8} {'beta':>6} {'rho':>6} | {'dstar_conj':>11} {'delta_avg':>11} {'match?':>8} "
          f"| {'a*/mu @davg (Poisson tail, M=n^2)':>34}")
    print("-" * 100)
    for log2n in [20, 24, 28, 30, 32]:
        n = 2 ** log2n
        beta = 1 + 128 / log2n           # forces q*eps* = q*2^-128 = n  (q = n^beta = n*2^128)
        logq = beta * log2n              # log2 q
        for rho in [0.5, 0.25, 0.125, 0.0625]:
            # (A) conjectured delta*
            dstar_conj = 1 - rho - H2(rho) / (beta * log2n)
            # (A) average-term delta: solve mu_log_q(delta) = log_q(n) = log2 n / log2 q = 1/beta
            target = (log2n) / logq      # log_q n = 1/beta
            lo, hi = 0.0, 1 - rho
            for _ in range(200):
                mid = (lo + hi) / 2
                if mu_log_q(n, rho, mid, beta, logq) > target:
                    hi = mid       # mu too big -> decrease delta
                else:
                    lo = mid
            delta_avg = (lo + hi) / 2
            match = abs(delta_avg - dstar_conj) < 5e-4
            # (B) Poisson tail at delta_avg: mu = n (=q eps*); find a* with M=n^2: n^2 * P >= 1
            mu = n  # by construction mu(delta_avg) = q eps* = n
            # solve a* : 2 ln n + poisson_log_sf(mu,a) = 0
            target_ln = 2 * log(n)
            alo, ahi = mu, mu * 4
            for _ in range(200):
                am = (alo + ahi) / 2
                if poisson_log_sf(mu, am) + target_ln > 0:
                    alo = am
                else:
                    ahi = am
            a_star = (alo + ahi) / 2
            ratio = a_star / mu
            print(f"{log2n:>6}b {beta:>6.2f} {rho:>6.3f} | {dstar_conj:>11.6f} {delta_avg:>11.6f} "
                  f"{'YES' if match else 'no':>8} | a*/mu = {ratio:.5f}  (excess {a_star-mu:.3e} ~ sqrt(n log n)={math.sqrt(n*log(n)):.3e})")
    print("\nIf delta_avg == dstar_conj: conjectured delta* IS the average-term (first-moment) value,")
    print("and a*/mu -> 1 confirms Poisson concentration over the n^2-line family pins worst-case = avg.")


if __name__ == "__main__":
    main()
