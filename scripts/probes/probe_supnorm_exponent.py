#!/usr/bin/env python3
"""
probe_supnorm_exponent.py

THE crux measurement for the prize: the worst-case THIN-regime sup norm exponent.

For a multiplicative subgroup R of order n in F_p with p ~ n^4 (THIN, n~p^{1/4}),
let  M(R) = max_{a!=0} |sum_{x in R} e_p(a x)|.

  - BGK / square-root-cancellation CONJECTURE: M(R) <= C * sqrt(n) * (log p)^O(1),
    i.e. M(R)/sqrt(n) grows only POLYLOG  =>  exponent kappa = 1/2.
  - If instead M(R) ~ n^kappa with kappa > 1/2, square-root cancellation FAILS in the
    thin regime, the prize "Gaussian" bound is FALSE, and delta* is pinned strictly
    below the optimistic (1-rho) edge.

We sweep n over many values with p ~ n^4 (capped for FFT feasibility), take the
WORST M(R) over several thin primes per n, and fit  log M  vs  log n  to estimate
kappa. We also report M/sqrt(n) and M/n (fraction of trivial).

One FFT per prime (rfft of the length-p indicator of R).
"""
import sys
import numpy as np
from sympy import isprime, primitive_root

def subgroup(p, n):
    g = pow(primitive_root(p), (p - 1) // n, p)
    R, cur = [], 1
    for _ in range(n):
        R.append(cur); cur = (cur * g) % p
    return R

def supnorm(p, R):
    ind = np.zeros(p, dtype=np.float64)
    for x in R:
        ind[x] = 1.0
    F = np.abs(np.fft.rfft(ind))
    return float(F[1:].max())     # exclude DC (index 0)

def worst_thin_supnorm(n, n_primes, pmax):
    """worst M(R) over up to n_primes thin primes p=1 mod n in [n^4, n^5], p<=pmax."""
    lo, hi = n**4, min(n**5, pmax)
    if lo > pmax:
        return None, None, 0
    best, bp, cnt = -1.0, None, 0
    cand = lo - (lo % n) + 1
    if cand < lo: cand += n
    while cand <= hi and cnt < n_primes:
        if isprime(cand):
            M = supnorm(cand, subgroup(cand, n))
            cnt += 1
            if M > best:
                best, bp = M, cand
        cand += n
    return best, bp, cnt

def main():
    PMAX = 120_000_000
    print("=== THIN-regime worst-case sup-norm exponent (p ~ n^4) ===")
    print(f"{'n':>5} {'p*':>11} {'#pr':>4} {'M(R)':>9} {'M/sqrt(n)':>10} {'M/n':>7} {'logM/logn':>10}")
    import math
    ns = [16, 24, 32, 40, 48, 56, 64, 80, 96, 112]
    pts = []
    for n in ns:
        npr = 12 if n <= 48 else (6 if n <= 80 else 3)
        M, bp, cnt = worst_thin_supnorm(n, npr, PMAX)
        if M is None:
            continue
        kappa_pt = math.log(M) / math.log(n)
        pts.append((n, M))
        print(f"{n:>5} {bp:>11} {cnt:>4} {M:>9.2f} {M/np.sqrt(n):>10.3f} "
              f"{M/n:>7.3f} {kappa_pt:>10.3f}", flush=True)

    # global least-squares fit  log M = kappa * log n + c   over n>=32 (drop tiny-n noise)
    big = [(n, M) for (n, M) in pts if n >= 32]
    if len(big) >= 2:
        X = np.array([math.log(n) for (n, M) in big])
        Y = np.array([math.log(M) for (n, M) in big])
        A = np.vstack([X, np.ones_like(X)]).T
        kappa, c = np.linalg.lstsq(A, Y, rcond=None)[0]
        print(f"\nLEAST-SQUARES fit (n>=32):  M(R) ~ n^kappa,  kappa = {kappa:.4f}")
        print(f"  kappa = 0.5  <=>  square-root cancellation (BGK conjecture, prize bound TRUE/provable-open)")
        print(f"  kappa > 0.5  <=>  cancellation FAILS in thin regime (prize 'Gaussian' bound FALSE)")
        # also a polylog fit: M = C sqrt(n) (log p)^beta, with p=n^4 => log p = 4 log n + const
        # test residual of M/sqrt(n) vs log n
        Z = np.array([math.log(M / math.sqrt(n)) for (n, M) in big])
        L = np.array([math.log(math.log(n**4)) for (n, M) in big])
        AA = np.vstack([L, np.ones_like(L)]).T
        beta, cc = np.linalg.lstsq(AA, Z, rcond=None)[0]
        print(f"  polylog alt: M/sqrt(n) ~ (log p)^beta,  beta = {beta:.3f} "
              f"(beta finite & kappa~0.5 => polylog/BGK; large kappa-0.5 => power excess)")

if __name__ == "__main__":
    main()
