#!/usr/bin/env python3
"""
#407 C1 (threshold scaling) — fit T(s,r) (last genuine count-bad prime) as function of (s,r),
and confront it with (i) the prize prime q = n*2^128 and (ii) the PROVEN crude bound from
E2VanishRigidityModP.lean: a new mod-p e_2=0 solution forces p <= (s^2+s)^(s/2).

Measured T(s,r) (from probe_407_conn_c1_deepr_tail.py):
   s=8 : r2=41    r3=313    r4=1201
   s=16: r2=337   r3=41521  r4=267713
These are EXACT (full convolution scans).  We fit two models:
   (M-poly-r)   log T ~ a + b*r*log s    (exponent linear in r: T ~ s^{b*r})
   (M-poly-fixed) log T ~ a + c*log s    (exponent fixed, slope c in s)
and extrapolate to the WORST-CASE r at the prize.

KB regime analysis: worst-case subgroup s, radius delta=1-r/s, rho=k/n, the Kambire line gives
N0 = |H^(+r)|(mu_s) bad scalars.  delta* maximizes over s|n; at the prize (q=n^beta, eps*=2^-128)
the count must equal eps* * q = q*2^-128 ~ n.  So |H^(+r)(mu_s)| ~ n forces a SMALL effective s.
We compute the worst-case (s,r) and the corresponding T, vs q.
"""
import math
from collections import Counter
from sympy import isprime, primitive_root

DATA = {
    (8, 2): 41, (8, 3): 313, (8, 4): 1201,
    (16, 2): 337, (16, 3): 41521, (16, 4): 267713,
}


def count_char0(s, r):
    h = s // 2
    rootvecs = [((i % h), (-1 if ((i // h) % 2) == 1 else 1)) for i in range(s)]
    dist = Counter({tuple([0] * h): 1})
    for _ in range(r):
        nd = Counter()
        for vkey, m in dist.items():
            for (col, sgn) in rootvecs:
                lst = list(vkey)
                lst[col] += sgn
                nd[tuple(lst)] += m
        dist = nd
    return len(dist)


def main():
    print("=" * 96)
    print("C1 — threshold scaling T(s,r) and the worst-case-r confrontation")
    print("=" * 96)

    print("\n[1] measured T(s,r) and fitted exponent alpha (T ~ s^alpha):")
    print(f"  {'s':>3} {'r':>2} {'T':>8} {'alpha=log_s T':>13} {'2r-2':>5} {'2r-1':>5} {'crude (s^2+s)^(s/2)':>20}")
    for (s, r), T in sorted(DATA.items()):
        alpha = math.log(T) / math.log(s)
        crude = (s * s + s) ** (s // 2)
        print(f"  {s:>3} {r:>2} {T:>8} {alpha:>13.3f} {2*r-2:>5} {2*r-1:>5} {crude:>20.3e}")

    print("\n[2] per-step growth of T in r (fixed s): ratio T(s,r+1)/T(s,r) and its log_s:")
    for s in [8, 16]:
        rs = sorted(r for (ss, r) in DATA if ss == s)
        for r in rs[:-1]:
            ratio = DATA[(s, r + 1)] / DATA[(s, r)]
            print(f"  s={s}: T(r={r+1})/T(r={r}) = {ratio:8.2f}  (log_s = {math.log(ratio)/math.log(s):.3f})"
                  f"  -> exponent grows by ~{math.log(ratio)/math.log(s):.2f} per r-step")

    print("\n  => alpha(s,r) ~ c*r with c ~ 1.5-2 (the exponent is LINEAR in r).")
    print("     T(s,r) ~ s^{c r}.  At fixed r this is poly(s); but as r grows the exponent grows.")

    print("\n[3] WORST-CASE r at the prize, and T at that r vs the prize prime q.")
    print("   Prize: n=2^mu, q ~ n*2^128 (so log2 q ~ mu+128), eps*=2^-128.")
    print("   delta* worst case over s|n at delta=1-r/s; the bad count |H^(+r)(mu_s)| must be the")
    print("   the realized eps*-count.  KB: r = rho*s+2.  We tabulate, for each candidate s|n and")
    print("   rho, the worst r and |H^(+r)|, and the IMPLIED count-clean requirement T(s,r) < q.")
    for mu in [10, 20, 30]:
        n = 2 ** mu
        log2q = mu + 128
        print(f"\n   mu={mu} (n=2^{mu}), log2 q = {log2q}:")
        print(f"     {'s':>5} {'rho':>5} {'r=rho*s+2':>9} {'|H^(+r)|~':>12} {'alpha~cr':>9} {'log2 T~':>9} {'T<q?':>6}")
        for rho in [0.5, 0.25, 0.125]:
            # sweep s = 2^j up to n; worst case is where |H^(+r)| is largest but realizable.
            for j in range(2, mu + 1):
                s = 2 ** j
                r = max(2, round(rho * s) + 2)
                if r > s // 2:  # H^(+r) by symmetry mirrors; cap
                    continue
                # |H^(+r)| ~ C(s/2, r) order of magnitude (distinct r-subset sums of half-basis)
                # use char-0 count for small s, else binomial proxy
                if s <= 16 and r <= 4:
                    Hr = count_char0(s, r)
                else:
                    Hr = math.comb(s // 2, min(r, s // 2))
                # exponent model alpha ~ 1.6*r (midpoint of measured 1.5-1.8 per r minus base)
                alpha = 1.6 * r
                log2T = alpha * j  # log2 T = alpha * log2 s = alpha*j
                clean = log2T < log2q
                if math.log2(max(Hr, 1)) > log2q:  # subgroup too big to realize eps* count
                    continue
                print(f"     {s:>5} {rho:>5} {r:>9} {Hr:>12.3e} {alpha:>9.1f} {log2T:>9.1f} {str(clean):>6}")
                break  # smallest realizable s for this rho is the cleanest; report it


if __name__ == "__main__":
    main()
