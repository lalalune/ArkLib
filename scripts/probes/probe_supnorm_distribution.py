#!/usr/bin/env python3
"""
probe_supnorm_distribution.py

Decides: is the thin-regime square-root-cancellation bound TRUE-but-hard or FALSE?

Prior probe measured the WORST-CASE (max over primes) sup norm M(R)~n^{0.67-0.9}; that
cannot distinguish "bound holds for TYPICAL primes, sparse bad outliers" (=> conjecture
morally TRUE, difficulty purely worst-case/proof) from "TYPICAL M(R) itself exceeds sqrt(n)"
(=> bound genuinely FALSE).

Here we record the full DISTRIBUTION of the normalized sup norm
    rho(p) = M(R_p) / sqrt(n * ln p),    M(R_p) = max_{a!=0} |sum_{x in R} e_p(a x)|,
over MANY thin primes p ~ n^4 (n = order of the multiplicative subgroup R).

  - BGK / square-root-cancellation TRUE-typically: rho(p) is O(1), its median/quantiles do
    NOT drift up with n; only a sparse tail (special primes) is large.
  - bound FALSE: even the median rho(p) grows with n (a positive power), i.e. sqrt(n)
    cancellation fails for typical primes, not just worst case.

We report, per n: min, median, mean, p90, p99, max of rho, AND the SLOPE of log(median M)
vs log(n) (=0.5 => sqrt-cancellation typical) and the bad-prime tail fraction {rho>2*median}.
One FFT per prime.
"""
import sys, math
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
    return float(F[1:].max())   # exclude DC

def thin_primes(n, count, pmax):
    lo, hi = n**4, min(n**5, pmax)
    out = []
    cand = lo - (lo % n) + 1
    if cand < lo: cand += n
    while cand <= hi and len(out) < count:
        if isprime(cand):
            out.append(cand)
        cand += n
    return out

def main():
    PMAX = 30_000_000
    print("=== thin-regime sup-norm DISTRIBUTION: true-but-hard vs false ===")
    print("rho(p) = M(R_p) / sqrt(n*ln p)  [BGK-predicted scale; O(1) => sqrt-cancellation]\n")
    print(f"{'n':>4} {'#pr':>5} {'minRho':>7} {'medRho':>7} {'meanRho':>7} {'p90':>6} {'p99':>6} "
          f"{'maxRho':>7} {'medM':>9} {'tail>2med':>9}")
    medM_pts = []
    for n in [16, 24, 32, 48, 64, 80, 96]:
        npr = 400 if n <= 32 else (150 if n <= 64 else 40)
        ps = thin_primes(n, npr, PMAX)
        if not ps:
            continue
        rhos, Ms = [], []
        for p in ps:
            M = supnorm(p, subgroup(p, n))
            Ms.append(M)
            rhos.append(M / math.sqrt(n * math.log(p)))
        rhos = np.array(rhos); Ms = np.array(Ms)
        med = float(np.median(rhos))
        tail = float(np.mean(rhos > 2 * med))
        medM = float(np.median(Ms))
        medM_pts.append((n, medM))
        print(f"{n:>4} {len(ps):>5} {rhos.min():>7.3f} {med:>7.3f} {rhos.mean():>7.3f} "
              f"{np.percentile(rhos,90):>6.3f} {np.percentile(rhos,99):>6.3f} {rhos.max():>7.3f} "
              f"{medM:>9.2f} {tail:>9.3f}", flush=True)

    # slope of log(median M) vs log n  (0.5 => typical sqrt-cancellation)
    big = [(n, M) for (n, M) in medM_pts if n >= 24]
    if len(big) >= 2:
        X = np.array([math.log(n) for n, M in big])
        Y = np.array([math.log(M) for n, M in big])
        A = np.vstack([X, np.ones_like(X)]).T
        kappa_med, _ = np.linalg.lstsq(A, Y, rcond=None)[0]
        print(f"\nTYPICAL (median) exponent: median M(R) ~ n^{kappa_med:.4f}")
        print(f"  ~0.5 => sqrt-cancellation holds for TYPICAL primes (bound TRUE-but-hard; "
              f"only worst-case/proof open)")
        print(f"  >0.5 => typical cancellation FAILS (bound genuinely FALSE in thin regime)")

if __name__ == "__main__":
    main()
