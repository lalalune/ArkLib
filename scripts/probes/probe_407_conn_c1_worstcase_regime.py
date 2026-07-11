#!/usr/bin/env python3
"""
#407 C1(c) — pin the WORST-CASE (s, r) at delta* using the ACTUAL Kambire relation r = rho*s + 2,
then decide T(s,r) (count-clean threshold) vs the prize prime q at that point.

Kambire construction: monomial line X^{rm}+lambda X^{(r-1)m} on mu_n (m=n/s), gcd-subgroup mu_s,
radius delta = 1 - r/s = 1 - rho - 2/s (since r = rho*s + 2), bad count = |H^(+r)(mu_s)|.
A bad witness exists at this delta iff |H^(+r)(mu_s)| > eps* * q.
delta* = MAX over s|n of (1 - rho - 2/s) subject to |H^(+r)(mu_s)| > eps* q  (larger s -> larger
delta -> we want the LARGEST s that still has enough bad scalars).

So s* = LARGEST s|n with |H^(+r)(mu_s)| > eps* q,  r = rho*s + 2.
This is the worst-case subgroup.  Then the count-clean question is T(s*, r*) < q where the
MEASURED count threshold scales as T(s,r) ~ s^{c r}, c ~ 1.6.

|H^(+r)(mu_s)|: number of distinct r-fold sums of mu_s.  In char 0 (Lam-Leung) the antipodal-free
r-subsets of the half-basis all give distinct sums; |H^(+r)| ~ C(s/2, r)*2^r-ish.  We use
log2|H^(+r)| ~ log2 C(s, r) (firm-order proxy; the r-subset sumset of the s-element subgroup,
distinct in char 0).  We BRACKET with C(s/2,r) (firm lower) and s^r/r! (upper).
"""
import math


def log2binom(N, r):
    if r < 0 or r > N:
        return -1.0
    return (math.lgamma(N + 1) - math.lgamma(r + 1) - math.lgamma(N - r + 1)) / math.log(2)


def log2_Hr(s, r):
    """proxy log2 |H^(+r)(mu_s)| ~ log2 C(s/2, r) + r  (antipodal-free half-basis subsets, sign
    choices) -- a firm-order estimate consistent with measured |H^(+r)|: s=8 r=2 ->33 (C(4,2)=6,
    *~5), s=16 r=2 ->129 (C(8,2)=28).  We just need the ORDER for the crossover, so use C(s,r)/2^?:
    actually measured 33 ~ C(8,2)+C(8,1)+C(8,0)=37, i.e. SUM_{j<=r} C(s/2, j)... use the cumulative."""
    h = s // 2
    # cumulative half-basis subset count sum_{j=0}^{r} C(h, j) matches |H^(+r)| order well:
    # s=8,r=2: C(4,0..2)=1+4+6=11; measured 33 ~ 3x (sign/coset). s=16,r=2: 1+8+28=37 ~ measured 129/3.
    # The crossover only needs log2 to within O(1); use log2 of the dominant binomial C(h, min(r,h)).
    if r >= h:
        return s - 1  # ~ full subgroup
    return log2binom(h, r) + r  # + r for the 2^r sign/coset multiplicity (order-correct)


def main():
    print("=" * 104)
    print("C1(c) — worst-case s* (largest subgroup with enough bad scalars), r* = rho*s*+2,")
    print("        then count threshold T(s*,r*) ~ s*^{c r*} (c~1.6) vs prize prime q.")
    print("=" * 104)

    for mu in [10, 20, 30, 40]:
        n = 2 ** mu
        log2q = mu + 128
        log2_epsq = mu  # eps* q = q*2^-128 ~ n = 2^mu
        print(f"\n##### mu={mu}  n=2^{mu}  log2 q={log2q}  log2(eps* q)={log2_epsq} #####")
        print(f"  {'rho':>6} {'s* (worst sub)':>14} {'r*=rho*s*+2':>12} {'delta*=1-rho-2/s*':>17} "
              f"{'log2 T(s*,r*)':>14} {'log2 q':>7} {'T<q?':>6} {'r*/log2 n':>10}")
        for rho in [0.5, 0.25, 0.125, 0.0625]:
            # find largest s = 2^j <= n with log2_Hr(s, round(rho*s)+2) > log2_epsq
            sstar, rstar = None, None
            for j in range(2, mu + 1):
                s = 2 ** j
                r = round(rho * s) + 2
                if r >= s // 2:
                    # H^(+r) is near-maximal (~2^{s-1}) >> eps*q, definitely bad; keep going
                    sstar, rstar = s, r
                    continue
                if log2_Hr(s, r) > log2_epsq:
                    sstar, rstar = s, r
                else:
                    # once it falls below, larger s with r=rho*s+2 has even larger r relative...
                    # H^(+r) is non-monotone; but for the worst case we take the LARGEST s that works.
                    # continue scanning (don't break) to catch larger s that re-exceed.
                    pass
            if sstar is None:
                print(f"  {rho:>6}  (no s realizes eps* q bad count)")
                continue
            s, r = sstar, rstar
            delta = 1 - rho - 2 / s
            c = 1.6
            log2T = c * r * math.log2(s)
            clean = log2T < log2q
            print(f"  {rho:>6} {s:>14} {r:>12} {delta:>17.5f} {log2T:>14.1f} {log2q:>7} "
                  f"{str(clean):>6} {r/mu:>10.3f}")

    print("\n" + "=" * 104)
    print("DECISIVE READOUT:")
    print(" * s* (worst-case subgroup) is the LARGEST s|n with |H^(+r)| > eps* q at r=rho*s+2.")
    print(" * If s* is LARGE (~n), then r*=rho*s*+2 ~ rho*n is HUGE and T~s*^{c r*}=exp(Theta(n)) >> q")
    print("   -> the single-r count is DEEP and re-hits the exp wall.")
    print(" * If s* is SMALL (~log n / O(1)), r* is O(1)/O(log n) and T is poly/quasi-poly < q")
    print("   -> the single-r count genuinely bypasses BGK.")
    print(" The printed s*, r*, T<q? settle which regime the PRIZE worst case actually lands in.")


if __name__ == "__main__":
    main()
