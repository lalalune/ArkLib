#!/usr/bin/env python3
"""
probe_dsar_critpoint_bandwidth.py  (#444, DERIVATIVE / CRITICAL-POINT route)

OBJECT: M(n) = max_{b!=0} |eta_b|, eta_b = sum_{x in mu_n} e_p(bx), mu_n = 2-power subgroup, n=2^mu.
ROUTE: treat eta as a Laurent polynomial P(z)=sum_{x in mu_n} z^x; the maxima of |eta_b| sit at the
critical points eta'_b = 0, eta'_b = sum_{x in mu_n} x*e_p(bx) (the bandwidth-weighted derivative).
QUESTION: does the critical-point equation eta'=0 / its energy bound M, or count the large-value freqs?

VERDICT (this probe): the derivative/critical-point field is BANDWIDTH-governed, NOT sparsity-governed.
  (1) EXACT derivative-field energy:  sum_{b!=0} |eta'_b|^2 = p*sum_x x^2 - (sum_x x)^2   [matched 1e-15;
      formalized axiom-clean in Frontier/_AR_CriticalPointFieldEnergy.lean as weighted_secondMoment].
  (2) Its scale is set by sum_x x^2 ~ n * (p^2/3)  (the magnitudes x in [0,p)) = Theta(n*p^2), a p=q-SCALE
      object, decoupled from the sparsity n.  So any Markov/critical-point ceiling M^2 <= (.)*sum|eta'|^2
      lives at the bandwidth (p) scale and NEVER reaches the prize sqrt(n log q).
  (3) The continuous interpolant has Theta(p) critical points (bandwidth, not n); #near-max integer freqs
      = exactly n or 2n (the known mu_n-coset localization), invisible to the derivative energy.
=> the derivative route REDUCES TO THE BGK / Konyagin wall at log depth: the sub-sqrt(q) cancellation in
   M is a fact about WHICH n frequencies mu_n occupies (support arithmetic), NOT the critical-point count.
"""
import numpy as np
from sympy import isprime

def subgroup(n, p):
    def order(a):
        o = 1; x = a % p
        while x != 1:
            x = (x * a) % p; o += 1
        return o
    pr = next(a for a in range(2, p) if order(a) == p - 1)
    h = pow(pr, (p - 1) // n, p)
    S = set(); x = 1
    for _ in range(n):
        S.add(x); x = (x * h) % p
    return sorted(S)

def find_prime(n, beta):
    t = int(n ** beta); p = t - (t % n) + 1
    while not (p > n and isprime(p) and (p - 1) % n == 0):
        p += n
    return p

if __name__ == "__main__":
    print(f"{'n':>4} {'beta':>5} {'p':>9} {'M/sqrtn':>8} {'deriv_E_exact':>14} {'match':>8} "
          f"{'derivE/p^2 ~ n?':>16} {'#(>=.9M2)':>10}")
    for (n, beta) in [(8, 3.0), (8, 4.0), (16, 3.0), (16, 4.0), (32, 3.0)]:
        p = find_prime(n, beta)
        S = np.array(subgroup(n, p), dtype=object)
        sum_x = int(sum(S)); sum_x2 = int(sum(int(x) ** 2 for x in S))
        derivE_exact = p * sum_x2 - sum_x ** 2     # sum_{b!=0} |eta'_b|^2  (exact identity)
        Sf = np.array([int(x) for x in S])
        if p < 70000:
            E = np.exp(2j * np.pi * np.outer(np.arange(1, p), Sf) / p)
            eta = E.sum(axis=1); etap = (E * Sf).sum(axis=1)
            g = np.abs(eta) ** 2; M2 = g.max()
            derivE_num = float(np.sum(np.abs(etap) ** 2))
            match = abs(derivE_exact - derivE_num) / derivE_exact
            near9 = int(np.sum(g >= 0.9 * M2))
            print(f"{n:>4} {beta:>5} {p:>9} {np.sqrt(M2/n):>8.3f} {derivE_exact:>14.3e} {match:>8.1e} "
                  f"{derivE_exact/(n*p**2):>16.3f} {near9:>10}")
        else:
            print(f"{n:>4} {beta:>5} {p:>9} {'--':>8} {derivE_exact:>14.3e} {'(exact)':>8} "
                  f"{derivE_exact/(n*p**2):>16.3f} {'--':>10}")
    print("\nderivE/(n*p^2) ~ 1/3  => bandwidth-scaled (Theta(n*p^2)), decoupled from n; route -> BGK wall.")
