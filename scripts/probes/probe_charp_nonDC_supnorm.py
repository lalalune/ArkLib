#!/usr/bin/env python3
"""
probe_charp_nonDC_supnorm.py

CORRECTED prize-regime probe. The prior probes measured E_r = (1/p) sum_{ALL a} |S(a)|^{2r}
(includes the a=0 DC term |S(0)|^{2r}=n^{2r}) in the r>n regime. But the PRIZE regime is
r ~ ln q ~ 55..89 with n=2^mu LARGE (n~1e6), i.e. r << n; there the DC term alone gives
E_r >= n^{2r}/p = n^{2r-4} >> (2r-1)!!*n^r, so the un-reduced bound is trivially FALSE.

The correct prize quantity (the "DC-escape" separation) is the NON-DC sup norm:
    M(R) := max_{a != 0} |S(a)|,   S(a) = sum_{x in R} e_p(a x).
BGK target: M(R) <= C * sqrt(n) * polylog  (square-root cancellation).
Trivial bound: M(R) <= n.  Via moments: M(R)^{2r} <= sum_{a!=0}|S(a)|^{2r} = p*E_r^{(!=0)},
and E_r^{(!=0)} = (1/p) sum_{a!=0}|S(a)|^{2r} = (sum_v c_r(v)^2) - n^{2r}/p.

We compute ALL S(a) by ONE FFT of the indicator of R (fast), then report, for thin
primes p in [n^4, n^5] at LARGE n with r << n:
  - normalized sup norm   M(R)/sqrt(n)   (BGK: should be ~ O(sqrt(log p)), bounded)
  - non-DC moment ratio   E_r^{(!=0)} / ((2r-1)!!*n^r)   for small r < n
  - DC dominance check: n^{2r}/p vs (2r-1)!!*n^r at prize-like (r,n) [analytic]
"""
import numpy as np
from sympy import isprime, primitive_root

def dfact(m):
    p, k = 1, m
    while k > 0:
        p *= k; k -= 2
    return p

def subgroup(p, n):
    g = pow(primitive_root(p), (p - 1) // n, p)
    R, cur = [], 1
    for _ in range(n):
        R.append(cur); cur = (cur * g) % p
    return R

def abs_S(p, R):
    """|S(a)| for all a in [0,p) via one FFT of the indicator of R."""
    ind = np.zeros(p, dtype=np.float64)
    for x in R:
        ind[x] = 1.0
    F = np.fft.rfft(ind)            # real FFT; |F[a]| = |S(a)| for a in [0, p//2]
    return np.abs(F)               # length p//2+1 ; index 0 is the DC term (=n)

def thin_primes(n, count, hi_mult):
    lo, hi = n**4, min(n**5, n**4 * hi_mult)
    out = []
    cand = lo - (lo % n) + 1
    if cand < lo: cand += n
    while cand <= hi and len(out) < count:
        if isprime(cand): out.append(cand)
        cand += n
    return out, lo, hi

def main():
    print("=== CORRECTED prize-regime probe: NON-DC sup norm of subgroup char sums ===")
    print("M(R)=max_{a!=0}|S(a)|; BGK target ~ C*sqrt(n)*polylog; trivial bound = n\n")

    PMAX = 20_000_000   # FFT size cap
    for n, hi_mult, npr in [(32, 6, 30), (64, 2, 4)]:
        primes, lo, hi = thin_primes(n, npr, hi_mult)
        primes = [p for p in primes if p <= PMAX]
        sqn = n ** 0.5
        sup_ratios = []
        worst = (-1.0, None)
        rs = [r for r in [2, 3, 4, 6, 8] if r < n]
        # accumulate worst non-DC moment ratios per r across sampled primes
        mom_worst = {r: -1.0 for r in rs}
        for p in primes:
            A = abs_S(p, n_R := subgroup(p, n))   # length p//2+1
            dc = A[0]                              # = n
            tail = A[1:]                           # a != 0 (and a != p/2 boundary; rfft covers half)
            M = float(tail.max())
            ratio = M / sqn
            sup_ratios.append(ratio)
            if ratio > worst[0]:
                worst = (ratio, p)
            # non-DC moments: sum over a!=0 of |S|^{2r}. rfft gives half the spectrum;
            # |S(a)|=|S(p-a)| so full sum_{a!=0} ~ 2*sum_{tail} (minus Nyquist if present).
            for r in rs:
                half = np.sum(tail.astype(np.float64) ** (2 * r))
                full = 2.0 * half                  # symmetry a <-> p-a (p odd => no exact Nyquist)
                Enz = full / p
                mr = Enz / (dfact(2 * r - 1) * n ** r)
                if mr > mom_worst[r]:
                    mom_worst[r] = mr
        print(f"--- n={n}: {len(primes)} thin primes in [{lo},{hi}], sqrt(n)={sqn:.2f}, trivial=n={n} ---")
        print(f"  sup_p [ M(R)/sqrt(n) ] = {worst[0]:.3f}  (at p={worst[1]})   "
              f"i.e. M(R) ~ {worst[0]*sqn:.1f} = {worst[0]*sqn/n*100:.1f}% of trivial n")
        print(f"  mean M(R)/sqrt(n) = {np.mean(sup_ratios):.3f}")
        print(f"  worst non-DC moment ratio E_r^(!=0)/((2r-1)!!*n^r):")
        for r in rs:
            print(f"      r={r}: {mom_worst[r]:.4f}" + ("  <-- EXCEEDS Gaussian" if mom_worst[r] > 1 else ""))
        print()

    # analytic: DC-term dominance at genuine prize scale
    print("=== analytic: DC term n^{2r}/p vs Gaussian (2r-1)!!*n^r at prize (r<<n) ===")
    import math
    for (mu, r) in [(20, 55), (20, 89), (16, 55), (24, 89)]:
        n = 2 ** mu
        p = n ** 4  # thin
        logDC = 2 * r * math.log(n) - math.log(p)
        logG = sum(math.log(2 * j - 1) for j in range(1, r + 1)) + r * math.log(n)
        print(f"  mu={mu} (n=2^{mu}), r={r}, p~n^4:  log(DCterm)-log(Gaussian) = {logDC-logG:.1f} "
              f"(>0 means un-reduced bound FALSE; DC dominates by e^{logDC-logG:.0f})")

if __name__ == "__main__":
    main()
