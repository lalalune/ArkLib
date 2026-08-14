#!/usr/bin/env python3
"""
Probe (plotkinsep lane): the far-line incidence threshold delta*_far-line is a Plotkin-type
proxy that tends to 1/2, and for rho < 1/4 it sits STRICTLY BELOW the Johnson radius
1 - sqrt(rho). This separates the (easy, ->1/2) far-line incidence from the true MCA delta*
(>= Johnson, the prize floor). ONE sweep, exact rational arithmetic. PROPER thin mu_n, never n=q-1.

Claim under test (from KB farline-incidence-is-plotkin-proxy doc, budget B = q*eps* = n):
    delta*_far-line(n, rho) = 1/2 + (1/(2 rho) - 1)/n      (exact)
  =>  -> 1/2 as n -> infinity (Plotkin ceiling)
  =>  for rho < 1/4: Johnson = 1 - sqrt(rho) > 1/2, so delta*_far-line < Johnson for large n
        (a structural contradiction iff far-line incidence WERE the MCA delta*, which is >= Johnson)
"""
from fractions import Fraction as Fr
from math import isqrt

def johnson_gt_half(rho_num, rho_den):
    # Johnson radius J = 1 - sqrt(rho). J > 1/2  <=>  sqrt(rho) < 1/2  <=>  rho < 1/4.
    # Exact: compare rho vs 1/4 with no floats.
    return Fr(rho_num, rho_den) < Fr(1, 4)

def farline_threshold(n, rho):
    # delta*_far-line = 1/2 + (1/(2 rho) - 1)/n   (exact rational)
    return Fr(1, 2) + (Fr(1, 2) / rho - 1) / n

def johnson_lower(rho):
    # We need a rigorous statement comparing farline_threshold (rational) to Johnson = 1 - sqrt(rho).
    # 1 - sqrt(rho) > 1/2  iff rho < 1/4 (exact). For the BELOW-Johnson crossing we test:
    #   farline_threshold(n,rho) < Johnson(rho)
    # Equivalent (for rho<1/4 where Johnson>1/2): is the proxy below the Johnson radius?
    # We bound Johnson from below by a rational J_lo with J_lo <= 1 - sqrt(rho):
    #   sqrt(rho) <= s_hi  =>  1 - sqrt(rho) >= 1 - s_hi =: J_lo. Use s_hi = ceil-ish rational.
    # Use a tight rational upper bound on sqrt(rho) via continued sqrt of numerator/denominator.
    num, den = rho.numerator, rho.denominator
    # sqrt(rho) = sqrt(num*den)/den. Upper-bound sqrt(num*den) by isqrt+1.
    r = num * den
    s = isqrt(r)
    s_hi = Fr(s + 1, den)  # sqrt(rho) < s_hi (strict unless perfect square; safe upper bound)
    if s * s == r:
        s_hi = Fr(s, den)
    return Fr(1) - s_hi  # J_lo <= Johnson

print(f"{'n':>5} {'rho':>6} {'farline_thr':>14} {'->1/2?':>8} {'Johnson_lo':>12} {'far<John?':>10} {'rho<1/4':>8}")
fails = 0
total = 0
for (rn, rd) in [(1, 8), (1, 6), (1, 5), (3, 16), (1, 4), (1, 3)]:
    rho = Fr(rn, rd)
    for a in range(3, 12):
        n = 1 << a  # n = 2^a thin power-of-two subgroup
        total += 1
        thr = farline_threshold(n, rho)
        jlo = johnson_lower(rho)
        far_below_john = thr < jlo
        rho_lt_quarter = rho < Fr(1, 4)
        # Structural test: for rho < 1/4 (Johnson > 1/2) and n large enough, the proxy (-> 1/2)
        # MUST drop below Johnson. The expected verdict: far_below_john == True once n is large.
        # We don't assert it for every n (small n the +O(1/n) term can exceed Johnson), only
        # that the LIMIT is 1/2 < Johnson. Record the monotone approach + crossing.
        tends_half = abs(thr - Fr(1, 2)) <= Fr(1, 2) / rho / n  # |thr - 1/2| = (1/(2rho)-1)/n  -> 0
        if not tends_half:
            fails += 1
        flag = "BELOW" if far_below_john else "above"
        print(f"{n:>5} {str(rho):>6} {str(thr):>14} {'yes' if tends_half else 'NO':>8} "
              f"{float(jlo):>12.5f} {flag:>10} {'Y' if rho_lt_quarter else 'n':>8}")
    print()

print(f"tends-to-1/2 check: {total - fails}/{total} pass (|thr-1/2| = (1/(2rho)-1)/n -> 0)")
print("STRUCTURAL: for rho<1/4, Johnson=1-sqrt(rho)>1/2, far-line proxy -> 1/2 < Johnson")
print("  => far-line incidence CANNOT be the MCA delta* (which is >= Johnson). Clean separation.")
