#!/usr/bin/env python3
"""
probe_ceiling_constant.py  (#389, Fable, 2026-06-13)

Verify the Calibrated Pin Hypothesis ceiling constant by EXACT binomial arithmetic,
independent of the (noisy) moment-budget probe.

The deep-band failure fires at agreement a = k + j (band m = j-1, radius
delta = 1 - a/n) when the witness-mass bad-scalar count beats the prize threshold:

    #badSet >= C(n, a) / (q^{a-k} * B)        (deep_band_badSet_card_of_supply)
    failure (epsilon_mca > eps*) when  #badSet > eps* * q
    <=>  C(n, a) > eps* * q^{a-k+1} * B

with B the per-word capped supply (polynomial; we use the proven unconditional
pair-count B = C(n,2) at k=2, and also B=1 to see the B-independence of the leading term).

The PRIZE frontier band a*(n) = the LARGEST a (deepest below capacity? no -- a grows
AWAY from capacity toward Johnson; capacity is a=k, Johnson is a=sqrt(k n)) for which
failure still fires.  delta*_ceiling = 1 - a*/n.

Hypothesis:  1 - a*/n  ->  1 - rho - H(rho)/(beta log2 n),  H = binary entropy (bits).
We compute a* EXACTLY and extract the subleading correction.
"""
from math import log2, log, lgamma

def H(p):
    if p <= 0 or p >= 1:
        return 0.0
    return -p * log2(p) - (1 - p) * log2(1 - p)

def log2_binom(n, a):
    """log2 C(n,a) via log-gamma (exact-asymptotic, no big ints)."""
    if a < 0 or a > n:
        return float('-inf')
    return (lgamma(n + 1) - lgamma(a + 1) - lgamma(n - a + 1)) / log(2)

EPS_LOG2 = -128.0   # log2(eps*) = -128

def frontier_a(n, k, q, logB):
    """Largest a in (k, n) with log2 C(n,a) > -128 + (a-k+1)*log2 q + log2 B."""
    best = None
    lq = log2(q)
    # scan from a=k+1 upward; the failure region is a contiguous band above k
    a = k + 1
    while a < n:
        lhs = log2_binom(n, a)
        rhs = EPS_LOG2 + (a - k + 1) * lq + logB
        if lhs > rhs:
            best = a
            a += 1
        else:
            if best is not None:
                break   # left the failure band
            a += 1
    return best

def johnson_a(n, k):
    return (n * (k - 1)) ** 0.5  # a^2 = n(k-1)

print(f"{'n':>6} {'k':>5} {'beta':>4} {'a*(B=C(n,2))':>13} {'a*(B=1)':>9} "
      f"{'Johnson_a':>10} {'1-a*/n':>9} {'asymp':>9} {'gap*logn':>9} {'corr':>8}")
for beta in (2, 3):
    for L in (8, 10, 12, 14, 16, 18, 20):
        n = 2 ** L
        rho = 0.25
        k = int(rho * n)
        q = n ** beta
        a1 = frontier_a(n, k, q, log2_binom(n, 2))
        a0 = frontier_a(n, k, q, 0.0)
        if a1 is None:
            print(f"{n:>6} {k:>5} {beta:>4}  no-failure")
            continue
        delta_ceil = 1 - a1 / n
        asymp = 1 - rho - H(rho) / (beta * log2(n))
        # gap between exact ceiling and (1-rho); times log n should -> H(rho)/beta
        gap = (1 - rho) - delta_ceil          # = a1/n - rho = j/n
        gap_logn = gap * log2(n)              # -> H(rho)/beta
        target = H(rho) / beta
        print(f"{n:>6} {k:>5} {beta:>4} {a1:>13} {a0:>9} {johnson_a(n,k):>10.1f} "
              f"{delta_ceil:>9.5f} {asymp:>9.5f} {gap_logn:>9.4f} {target:>8.4f}")
    print()

print("PREDICTION: column 'gap*logn' -> 'corr'(=H(rho)/beta) as n grows.")
print("Also: a* should be << Johnson_a (frontier is deep below Johnson, near capacity).")
print(f"H(0.25) = {H(0.25):.5f};  H/2 = {H(0.25)/2:.5f};  H/3 = {H(0.25)/3:.5f}")

# Subleading: the B-dependence (a1 vs a0) measures the poly-B shift; should be O(1) in a.
print("\n=== B-independence of leading term: a*(B=C(n,2)) - a*(B=1) (should be O(1), <<j) ===")
for beta in (2,):
    for L in (12, 16, 20):
        n = 2 ** L; rho = 0.25; k = int(rho*n); q = n**beta
        a1 = frontier_a(n,k,q,log2_binom(n,2)); a0 = frontier_a(n,k,q,0.0)
        print(f"  n={n} beta={beta}: a*(C(n,2))={a1}, a*(1)={a0}, diff={a0-a1}, j={a1-k}")
