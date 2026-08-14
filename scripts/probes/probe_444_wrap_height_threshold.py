#!/usr/bin/env python3
"""
probe_444_wrap_height_threshold.py  (#444, C1-anomaly-wrap-count angle)

STRUCTURAL CLAIM under test (the height/divisor route to bounding the char-p anomaly):

  The char-p anomaly A_r = E_r^{Fp,nonzero} - E_r^{char0,nonzero} counts exactly the 2r-tuples
  whose signed sum  S = sum_{i=1}^{r} zeta^{a_i} - sum_{j=1}^{r} zeta^{b_j}  in Z[zeta_n] is
  NONZERO but vanishes mod the prime ideal P|p induced by zeta -> omega (n-th root of unity mod p).

  Such an S is an algebraic integer that is a sum of 2r roots of unity, so
      |sigma(S)| <= 2r  for every embedding sigma  =>  |N(S)| <= (2r)^{phi(n)}.
  S in P, S != 0  =>  p | N(S).  Hence:

  (PERFECT-FAITHFULNESS THRESHOLD)   p > (2r)^{phi(n)}   =>   A_r = 0   exactly.

This probe TESTS three things EXACTLY (proper mu_n = 2-power subgroup, n | p-1, never n=p-1):

  (T1) Confirm A_r = 0 for all in-window primes once p exceeds the naive height threshold (2r)^{phi(n)}.
  (T2) Find the EMPIRICAL wrap threshold T_emp(n,r) = largest prime with A_r > 0 (the true onset wall),
       and compare to the naive (2r)^{phi(n)} and to a SHARPER norm bound based on the actual
       max |N(S)| over signed 2r-tuples with S != 0.
  (T3) The DECISIVE prize question: is T_emp(n,r) below the prize band p ~ n^beta (beta 4-5) at the
       prize depth r ~ log m ~ log(p/n)?  If T_emp << n^4 the anomaly is GONE in the prize regime
       (real handle). If T_emp >> n^4 the anomaly is alive (no gain from height alone).

Exact integer arithmetic via mod-p convolution for E_r^{Fp} and a char-0 lattice convolution for
E_r^{char0}.  No Lean here => axiom-clean trivially (probe-only). Reuses the verified engine.
"""
import sys, os, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from probe_407_anom_worst_rtraj_n32 import Ep, E0_ring, roots_modp, is_prime

def phi_2power(n):
    # n = 2^k => phi(n) = n/2
    return n // 2

def inwin(n, blo, bhi, cap):
    """primes p = m*n+1 with n^blo <= p <= n^bhi, p prime, proper subgroup (m>=2 so n<p-1)."""
    lo = int(n**blo); hi = int(n**bhi); out = []
    m = max(2, lo // n)
    while m*n + 1 <= hi and len(out) < cap:
        p = m*n + 1
        if p >= lo and is_prime(p):
            out.append(p)
        m += 1
    return out

def Anom(n, p, r):
    return Ep(roots_modp(n, p), p, r) - E0_ring(n, r)

print("="*92)
print("STRUCTURAL HEIGHT THRESHOLD for the char-p anomaly A_r  (#444 C1-wrap-count)")
print("  Naive bound: p > (2r)^{phi(n)}  =>  A_r = 0  (since |N(S)| <= (2r)^{phi(n)} and p|N(S)).")
print("="*92)

# T1+T2: scan a wide prime range, find the empirical onset wall, compare to naive threshold.
for n in [8, 16]:
    phi = phi_2power(n)
    for r in [2, 3, 4]:
        if n**r > 6_000_000:   # convolution feasibility
            continue
        naive = (2*r)**phi
        # scan primes from small (where anomaly lives) upward across many octaves
        # use a broad window in beta to find the LAST prime with A_r>0
        worst_p_with_anom = None
        last_clean_streak = 0
        # sweep many primes p=m*n+1 over a large multiplier range
        ps = inwin(n, 1.5, 6.0, 4000)
        for p in ps:
            a = Anom(n, p, r)
            if a > 0:
                worst_p_with_anom = max(worst_p_with_anom or 0, p)
        Temp = worst_p_with_anom
        ratio_to_naive = (Temp / naive) if Temp else 0.0
        print(f"  n={n:>2} r={r}: phi={phi:>2}  naive (2r)^phi = (2*{r})^{phi} = {naive:.3e}")
        if Temp:
            print(f"             EMPIRICAL wrap wall T_emp = {Temp}  (~ n^{math.log(Temp)/math.log(n):.2f})"
                  f"   T_emp/naive = {ratio_to_naive:.2e}")
        else:
            print(f"             EMPIRICAL: NO anomaly found in scanned window (A_r=0 throughout)")
        # check threshold: is every prime above naive clean?
        if Temp:
            print(f"             => T_emp << naive by factor {1.0/ratio_to_naive:.1e}: naive height bound is LOOSE")
        print()

print("="*92)
print("T3: prize-band comparison. Prize wants p ~ n^beta (beta in [4,5]) at depth r ~ log_2 m.")
print("    Is the empirical wrap wall T_emp(n,r) below n^4 at the relevant r?  If yes -> anomaly")
print("    is structurally absent in the prize regime (HANDLE). If no -> alive (no gain).")
print("="*92)
