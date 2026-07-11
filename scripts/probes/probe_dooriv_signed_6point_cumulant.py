#!/usr/bin/env python3
"""
Door-(iv) Lane 1 — the SIGNED 6-point connected cumulant of the period field: the board's OWN
terminal chain pointer (DISPROOF_LOG, 2026-06-18 connected-4 entry) localized the surviving door-(iv)
surface to "6TH ORDER OR HIGHER, or an object outside the moment hierarchy entirely." The chain is
closed through 4th order (marginal-EVT dead; white 2-pt; connected-4 cumulant = 0 => Gaussian to full
4th order; modulus-4th = E2 = refuted energy). 6th order is the FIRST UNPROBED surface.

WHY THIS OBJECT (not a re-probe): the modulus 6th moment K6 was already tabulated and, by the same
character-orthogonality identity that collapsed K4 -> E2, the modulus 6th moment collapses to the
6-fold additive count E3 = refuted-energy lane (DEAD by construction; do NOT re-measure it). The
NEVER-PROBED object is the PHASE-SENSITIVE, SIGNED, OFF-DIAGONAL connected 6-point cumulant -- the
piece of E[z z z zbar zbar zbar] that survives after subtracting the GAUSSIAN (Wick) prediction built
from the (white, ~0) 2-point covariance. For a complex-Gaussian field this connected 3-3 cumulant is
IDENTICALLY 0 at every lag configuration. A nonzero, N-non-shrinking, thinness-essential value =
the genuine higher-order phase coherence door-(iv) needs (and the one the white-noise autocorrelation
and the connected-4 sweep are BLIND to).

OBJECT: period field z_j = eta_{g^j} on the cyclic multiplicative quotient Z_N (N=(p-1)/n), proper
2-power mu_n, p >> n^3, m=(p-1)/n>1, NEVER n=q-1.

The lag-resolved connected 3-3 cumulant at lag pattern (0,k,l):
  M6(k,l) = E_j[ z_j z_{j+k} z_{j+l} * conj(z_j z_{j+k} z_{j+l}) ]   ... that is a MODULUS moment (=E3, dead)
So instead we use the PHASE-CARRYING translation-cumulant: the connected piece of
  G(k,l) = E_j[ z_j z_{j+k} z_{j+l} * conj(z_{j+a} z_{j+b} z_{j+c}) ]
with the (3,3) indices NOT a permutation of each other (so it is NOT a modulus moment). The cleanest
phase-sensitive scalar that is NOT a modulus moment and is Wick-zero for a Gaussian field is the
TRIPLE-PRODUCT connected cumulant
  C3(k,l) = E_j[ z_j z_{j+k} z_{j+l} ] * conj( E_j[ z_j z_{j+k} z_{j+l} ] )   (no, that's |3pt|^2 -- still a moment)

The correct connected 6th object: the 3-3 connected cumulant
  kappa6(k,l) = E[ z_j z_{j+k} z_{j+l} \bar z_j \bar z_{j+k} \bar z_{j+l} ]   (=E3 modulus, DEAD)
                                                              --> NOT this.
We take the genuinely-signed PHASE cumulant: the connected part of the TRIPLE CORRELATION
  T3(k,l) = E_j[ z_j z_{j+k} z_{j+l} ]   (the complex bispectrum-of-3 on the quotient)
For a stationary GAUSSIAN field with mean m, E[z_j z_{j+k} z_{j+l}] = m^3 + m(cov(0,k)+cov(0,l)+cov(k,l))
i.e. fully determined by the 1- and 2-point statistics (Gaussian has no connected 3rd cumulant of the
field itself). The CONNECTED triple correlation
  kappa3(k,l) = E[z_j z_{j+k} z_{j+l}] - [Gaussian/Wick prediction from mean + covariances]
is identically 0 for a Gaussian field. Since z is COMPLEX, E[zzz] need not be ~|.|, it is a SIGNED phase
object -- exactly the "phase information the modulus moment discards." A nonzero connected kappa3(k,l)
that is bounded away from 0 / thinness-essential = a 3rd-order PHASE coherence = a door-(iv) crack;
its SQUARE feeds a 6th-order (3x conj-3) bound that does NOT reduce to E3.

This is the FIRST member of the "6th order or higher" surface (|E[zzz]|^2 is a 6-point object) and it is
PHASE-sensitive (uses z, not |z|), so it is OUTSIDE the modulus-moment/additive-energy hierarchy that
killed K4=E2 and K6=E3. Probe it.

Wick (Gaussian) prediction for the connected triple correlation of a zero-corrected field:
  Gaussian field has kappa3 == 0 identically (odd connected cumulant of a Gaussian vanishes).
So the test is simply: is the connected triple correlation
  kappa3(k,l) = E_j[ (z_j-m)(z_{j+k}-m)(z_{j+l}-m) ]   (m = field mean)
bounded away from 0 (normalized by (E|z-m|^2)^{3/2}) as N grows, thinness-essentially?
EXACT complex arithmetic.
"""
import cmath, math, statistics

def is_prime(n):
    if n < 2: return False
    for q in (2,3,5,7,11,13,17,19,23,29,31,37):
        if n % q == 0: return n == q
    d = n-1; r = 0
    while d % 2 == 0: d //= 2; r += 1
    for a in (2,3,5,7,11,13,17,19,23,29,31,37):
        x = pow(a, d, n)
        if x in (1, n-1): continue
        for _ in range(r-1):
            x = x*x % n
            if x == n-1: break
        else: return False
    return True

def find_prime(n, beta):
    t = int(round(n**beta)); k0 = max(2, t//n)
    for dk in range(0, 600000):
        for k in (k0+dk, k0-dk):
            if k < 2: continue
            p = k*n + 1
            if p > n and is_prime(p): return p
    return None

def subgroup(p, n):
    pm1 = p-1; f = {}; m = pm1; d = 2
    while d*d <= m:
        while m % d == 0: f[d] = 1; m //= d
        d += 1
    if m > 1: f[m] = 1
    def isg(g): return all(pow(g, pm1//q, p) != 1 for q in f)
    g = 2
    while not isg(g): g += 1
    h = pow(g, pm1//n, p); mu = []; c = 1
    for _ in range(n): mu.append(c); c = c*h % p
    return mu, g

def eta_c(b, mu, p):
    return sum(cmath.exp(2j*math.pi*((b*y) % p)/p) for y in mu)

def main():
    print("=== door-(iv) signed 6-point object: connected TRIPLE correlation kappa3(k,l) of period field ===")
    print("  (PHASE-sensitive, NOT a modulus moment; =0 for a Gaussian field; |kappa3|^2 is a 6-pt object")
    print("   that does NOT reduce to E3 additive energy. N-non-shrinking + thinness-essential => door-iv.)")
    print()
    print(f"{'n':>4} {'beta':>5} {'p':>11} {'N':>7} {'thick?':>7} {'|kap3|max/sd3':>13} "
          f"{'|kap3|mean/sd3':>14} {'lag*':>10}")
    # thin (2-power) vs thick (non-2-power composite) control, matched-ish n, rule-3 test
    cells = [
        (16, 4.0, "THIN"), (16, 4.5, "THIN"),
        (32, 4.0, "THIN"), (32, 4.5, "THIN"),
        (64, 4.0, "THIN"),
        (24, 4.0, "thick"), (40, 4.0, "thick"), (48, 4.0, "thick"),
    ]
    results = {}
    for n, beta, tag in cells:
        p = find_prime(n, beta)
        if p is None:
            print(f"{n:>4} {beta:>5} {'--':>11}  (no prime)")
            continue
        mu, g = subgroup(p, n)
        N = (p-1)//n
        cap = min(N, 24000)
        z = []; cur = 1
        for j in range(cap):
            z.append(eta_c(cur, mu, p)); cur = cur*g % p
        m = sum(z)/cap
        zc = [v - m for v in z]
        var = sum((abs(v)**2) for v in zc)/cap   # E|z-m|^2
        sd3 = var**1.5                            # scale for a 3rd cumulant
        # connected triple correlation over a grid of lags (k,l), k<l small
        best = 0.0; bestlag = None; vals = []
        K = min(12, cap//3)
        for k in range(1, K):
            for l in range(k+1, K+1):
                acc = 0+0j
                for j in range(cap):
                    acc += zc[j]*zc[(j+k) % cap]*zc[(j+l) % cap]
                kap = acc/cap
                a = abs(kap)/sd3
                vals.append(a)
                if a > best:
                    best = a; bestlag = (k, l)
        meanv = statistics.fmean(vals) if vals else 0.0
        results[(n, beta, tag)] = (best, meanv, N)
        print(f"{n:>4} {beta:>5} {p:>11} {N:>7} {tag:>7} {best:>13.5f} {meanv:>14.5f} {str(bestlag):>10}")
    print()
    print("READING:")
    print(" - Gaussian/white-field baseline: |kappa3|/sd3 ~ 1/sqrt(cap) -> 0 as N grows (sampling noise only).")
    print("   For cap~24000 that floor is ~0.006. A SIGNAL must sit well above ~0.01 and NOT shrink with N.")
    print(" - rule-3 (thinness): compare THIN (2-power mu_n) vs thick (non-2-power) at matched n.")
    print("   A door-(iv) crack needs THIN > thick (thinness-essential). Thickness-invariant => dead (BGK).")

if __name__ == "__main__":
    main()
