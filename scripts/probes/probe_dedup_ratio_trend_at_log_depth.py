#!/usr/bin/env python3
"""
#444 probe (lane dedupstrict, part 2): the dedup-slack FRACTION at the binding log depth.

Part 1 showed N_r < C(n,r) is STRICT at r = log2 n for n = 8..128 and the slack GROWS in
absolute terms. The honesty-critical follow-up: does the slack FRACTION
    f(n) = (C(n, log2 n) - N_{log2 n}) / C(n, log2 n)
go to 0 (=> dedup fractionally negligible at the binding depth => leans WALL) or stay bounded
away from 0 (=> a real fractional escape)?

This computes f(n) up the thin tower n = 2^a, a = 3..14 (exact big-int), and also the survival
ratio s(n) = N_{log2 n} / C(n, log2 n) = 1 - f(n).  NEVER n = q-1.

A monotone f(n) -> 0 at r = log2 n is an HONEST WALL-leaning verdict (the dedup is strict but
asymptotically thin at the binding depth); it does NOT close anything and does NOT assert a
sub-linear/capacity law (ASYMPTOTIC GUARD: no c*/n claim, cliff-at-n/2 untouched).
"""
from math import comb
from fractions import Fraction


def N_r(m, r):
    tot = 0
    for k in range(0, min(r, 2 * m - r) + 1):
        if (k % 2) == (r % 2):
            tot += comb(m, k) * (2 ** k)
    return tot


def report():
    print("thin tower; r = log2 n; f(n) = slack/C(n,r) dedup fraction at the binding depth\n")
    fs = []
    for a in range(3, 15):
        n = 2 ** a
        m = n // 2
        r = a
        total = comb(n, r)
        distinct = N_r(m, r)
        slack = total - distinct
        f = Fraction(slack, total)
        survive = Fraction(distinct, total)
        fs.append((n, f))
        print(f"n=2^{a:<2}={n:>6}: f(n)=slack/total={float(f):.6f}   survive N_r/C={float(survive):.6f}"
              f"   (slack={slack})")
    print()
    # trend
    print("=== fraction trend at r = log2 n ===")
    monotone_down = all(fs[i][1] > fs[i + 1][1] for i in range(len(fs) - 1))
    print(f"f(n) strictly decreasing up the whole tower: {monotone_down}")
    print(f"f(smallest)={float(fs[0][1]):.6f}  ->  f(largest)={float(fs[-1][1]):.6f}")
    # crude check: does f look like it tends to 0?
    last4 = [float(x[1]) for x in fs[-4:]]
    print(f"last 4 f values: {['%.5f' % v for v in last4]}")
    print()
    if monotone_down and last4[-1] < last4[0]:
        print("VERDICT: the dedup-slack FRACTION at the binding log depth is monotonically")
        print("DECREASING up the tower -> dedup is STRICT but fractionally vanishing at r=log n.")
        print("Honest reading: leans WALL (the A3 escape is strict but asymptotically thin at the")
        print("binding depth); does NOT establish a real fractional escape. ASYMPTOTIC GUARD ok.")
    return monotone_down


if __name__ == "__main__":
    import sys
    sys.exit(0 if report() else 1)
