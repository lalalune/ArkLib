#!/usr/bin/env python3
"""
#407 C1(c) — reverse-engineer the worst-case (s, r) from the EXACT Kambire delta* FORMULA, then
evaluate the count threshold T(s,r) at that point.  This avoids my earlier mis-statement of the
'bad count > eps* q' constraint by reading the regime off the closed-form delta* directly.

Kambire window-edge (KB line 13/76):
    delta* = 1 - rho - 2*rho*ln(1/(2*rho)) / log2(q*eps*).
The construction: monomial coset line on subgroup mu_s (s | n), radius delta = 1 - r/s, with the
bad-scalar count = |H^(+r)(mu_s)| ~ C(s, r) (distinct r-fold sums).  The window edge is where this
count crosses the threshold eps* * q:
    |H^(+r)(mu_s)| ~ eps* * q   <=>   log2 C(s, r) ~ log2(q eps*) = log2 q - 128.
And the radius is delta = 1 - r/s.  To get the SUP radius (delta*), optimize over (s, r) on the
curve log2 C(s,r) = log2(q eps*).   The KB closed form is the result of that optimization with
r = rho*s + 2 substituted (so the agreement degree matches deg < k = rho*n scaled to the coset).

We do the optimization NUMERICALLY: maximize delta = 1 - r/s over integers (s|n, 1<=r<s) subject
to log2 C(s, r) >= log2(q eps*) = L.   Report the optimizer (s*, r*), the resulting delta*, COMPARE
to the closed form, then compute log2 T(s*, r*) = c*r*log2 s* (c~1.6 measured) vs log2 q.

THE QUESTION: at the OPTIMIZER, is r* = O(1), O(log n), or Theta(s)?  And is log2 T < log2 q?
"""
import math


def log2C(N, r):
    if r < 0 or r > N:
        return -1e18
    return (math.lgamma(N + 1) - math.lgamma(r + 1) - math.lgamma(N - r + 1)) / math.log(2)


def closed_form_deltastar(rho, log2qeps):
    return 1 - rho - 2 * rho * math.log(1 / (2 * rho)) / log2qeps


def optimize(mu, rho):
    n = 2 ** mu
    log2q = mu + 128
    L = log2q - 128  # = mu  (log2(q eps*))
    # maximize delta = 1 - r/s over s = 2^j (j<=mu), r in [1, s-1], subject to log2C(s,r) >= L.
    # For each s, the LARGEST r with log2C(s,r)>=L on the LOWER branch gives the smallest r/s?  No:
    # we want to MAXIMIZE delta = 1 - r/s, i.e. MINIMIZE r/s, subject to count >= eps*q.
    # For fixed s, smaller r -> smaller count.  So we need the SMALLEST r with log2C(s,r) >= L
    # (count just reaches threshold) -- that minimizes r/s for that s.
    best = None
    for j in range(2, mu + 1):
        s = 2 ** j
        # smallest r with log2C(s,r) >= L
        rmin = None
        for r in range(1, s):
            if log2C(s, r) >= L:
                rmin = r
                break
        if rmin is None:
            continue
        delta = 1 - rmin / s
        if best is None or delta > best[0]:
            best = (delta, s, rmin)
    return best, closed_form_deltastar(rho, L)


def main():
    print("=" * 104)
    print("C1(c) reverse-Kambire — worst-case (s*,r*) maximizing delta=1-r/s s.t. C(s,r)>=eps*q,")
    print("                        compared to the closed-form delta*, then T(s*,r*) vs q.")
    print("=" * 104)
    print("eps* q = 2^{log2 q - 128} = 2^mu = n.  So threshold L = mu.  c (T~s^{cr} exponent) ~ 1.6.")

    for mu in [10, 20, 30, 40]:
        n = 2 ** mu
        log2q = mu + 128
        print(f"\n##### mu={mu}  n=2^{mu}  log2 q={log2q}  L=log2(eps*q)={mu} #####")
        print(f"  {'rho':>7} {'s*':>10} {'r*':>8} {'delta*(opt)':>12} {'delta*(closed)':>14} "
              f"{'r*/log2 n':>10} {'log2 T':>10} {'log2 q':>7} {'T<q?':>6}")
        for rho in [0.5, 0.25, 0.125, 0.0625]:
            (best, dcf) = optimize(mu, rho)
            if best is None:
                print(f"  {rho:>7}  none")
                continue
            delta, s, r = best
            c = 1.6
            log2T = c * r * math.log2(s)
            clean = log2T < log2q
            print(f"  {rho:>7} {s:>10} {r:>8} {delta:>12.5f} {dcf:>14.5f} "
                  f"{r/mu:>10.3f} {log2T:>10.1f} {log2q:>7} {str(clean):>6}")

    print("\n" + "=" * 104)
    print("READOUT: r* (worst-case fold-count) and whether the single-r count threshold T < q.")
    print("  If r* = O(1) -> T = s*^{O(1)} = poly(n) << q: count genuinely BYPASSES BGK.")
    print("  If r* = Theta(log n) or more -> T = quasi-poly/exp: count re-hits the deep regime.")
    print("  Also: r* vs the deep-moment crossover r_cross ~ beta+1 (= log2 q / log2 n ~ 5-13);")
    print("  the BGK wall 'turns on' at r > r_cross.  Compare r* to r_cross to settle C1.")
    for mu in [20, 30, 40]:
        log2q = mu + 128
        beta = log2q / mu
        print(f"  mu={mu}: r_cross ~ beta+1 = {beta+1:.2f}  (BGK deep-moment wall turns on above this r)")


if __name__ == "__main__":
    main()
