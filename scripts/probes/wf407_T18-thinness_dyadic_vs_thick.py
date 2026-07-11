#!/usr/bin/env python3
"""wf407_T18-thinness_dyadic_vs_thick.py  (#407 T18 — IS the violation 'thick window' or 'dyadic m'?)

The thick-window measurement shows B > sqrt(2 n log p) at Fermat p=65537, n=64,128.
But the DIAGONAL (non-dyadic m, odd_part(m)>1) never violates S_p. So we must decide:

  IS the necessary condition about THICKNESS (beta small) or about the 2-ADIC STRUCTURE
  of m = (p-1)/n (m a power of 2)?  This MATTERS for the prize: the prize has
  m = (p-1)/n = 2^128 EXACTLY -- m is FULLY DYADIC. So if the violation tracks dyadic m
  (not thickness), the prize regime is on the SAME side as the Fermat witnesses, and the
  necessary condition is sharper and prize-relevant.

EXPERIMENT: at FIXED n and FIXED thickness beta (so log p, log m nearly equal across the
group), compare primes with
   (A) m fully dyadic  (odd_part(m) = 1, m = 2^j),     vs
   (B) m fully odd-rich (odd_part(m) large),
and measure B/sqrt(2 n log p), B/sqrt(2 n log m), logMeff/log m. If (A) systematically
inflates and (B) does not, the necessary-condition object is the 2-ADIC m, not thickness.

We hold beta ~ const by picking primes in a narrow band p in [P, 1.3 P] for several P,
classifying each by v2(m) = 2-adic valuation of m.
"""
import sys, math
sys.path.insert(0, 'scripts/probes')
from probe_constant_additive_vs_mult import is_prime, primitive_root
import numpy as np


def v2(x):
    k = 0
    while x % 2 == 0 and x > 0:
        x //= 2; k += 1
    return k, x   # (valuation, odd part)


def all_periods_abs(p, n):
    g = primitive_root(p)
    gm = pow(g, (p - 1) // n, p)
    sub = np.empty(n, dtype=np.int64); cur = 1
    for i in range(n):
        sub[i] = cur; cur = cur * gm % p
    m = (p - 1) // n
    twp = 2.0 * math.pi / p
    Bsq = 0.0
    b = 1
    for j in range(m):
        prods = (b * sub) % p; ang = twp * prods
        s = math.hypot(np.cos(ang).sum(), np.sin(ang).sum())
        if s > Bsq: Bsq = s
        b = b * g % p
    return Bsq


def main():
    flush = lambda *a: print(*a, flush=True)
    flush("#" * 100)
    flush("# T18: does the S_p / S_m violation track THICKNESS or the 2-ADIC structure of m?")
    flush("# Fixed n, narrow p-band (~fixed beta); classify primes by v2(m). m fully dyadic = prize shape.")
    flush("#" * 100)

    for n in (32, 64):
        flush(f"\n=== n = {n} ===")
        # several beta targets; at each, scan a window of primes and bucket by v2(m).
        for beta in (2.5, 3.0):
            P = int(round(n ** beta))
            flush(f"\n  beta~{beta} (P~{P}), n={n}.  Comparing m-dyadic vs m-odd-rich at ~same thickness:")
            flush(f"    {'p':>9} {'m':>7} {'v2(m)':>5} {'oddpart':>7} {'beta':>5} "
                  f"{'B':>8} {'B/Sp':>7} {'B/Sm2':>7} {'logMeff/logm':>12}")
            cnt = 0
            p = P - (P % n) + 1
            best_dyadic = None; best_odd = None
            while p < 3 * P and p < 4_000_000 and cnt < 60:
                if p > 3 and is_prime(p) and (p - 1) % n == 0:
                    m = (p - 1) // n
                    if m < 2:
                        p += n; continue
                    val, odd = v2(m)
                    Bsq = all_periods_abs(p, n)
                    B = Bsq
                    lnp = math.log(p); lnm = math.log(m)
                    rp = B / math.sqrt(2 * n * lnp)
                    rm = B / math.sqrt(2 * n * lnm)
                    logMeff = B * B / (2.0 * n)
                    bb = lnp / math.log(n)
                    tag = ""
                    # track the most-dyadic and most-odd in band
                    if best_dyadic is None or val > best_dyadic[0]:
                        best_dyadic = (val, p, m, odd, B, rp, rm, logMeff/lnm, bb)
                    if best_odd is None or odd > best_odd[0]:
                        best_odd = (odd, p, m, val, B, rp, rm, logMeff/lnm, bb)
                    cnt += 1
                p += n
            if best_dyadic:
                val, p, m, odd, B, rp, rm, rr, bb = best_dyadic
                flush(f"  MOST-DYADIC  {p:>9} {m:>7} {val:>5} {odd:>7} {bb:>5.2f} "
                      f"{B:>8.2f} {rp:>7.3f} {rm:>7.3f} {rr:>12.3f}")
            if best_odd:
                odd, p, m, val, B, rp, rm, rr, bb = best_odd
                flush(f"  MOST-ODD     {p:>9} {m:>7} {val:>5} {odd:>7} {bb:>5.2f} "
                      f"{B:>8.2f} {rp:>7.3f} {rm:>7.3f} {rr:>12.3f}")

    # Direct dyadic ladder: m = 2^j exactly (the prize shape m=2^128). p = n*2^j + 1 prime.
    flush(f"\n{'='*100}")
    flush("# DYADIC LADDER  m = 2^j  (the PRIZE shape, m=2^128):  p = n*2^j + 1 prime.")
    flush("#  This is exactly the prize coset count structure. Does S_p stay violated as j grows?")
    flush(f"{'='*100}")
    for n in (8, 16, 32, 64):
        flush(f"\n  n={n}:  {'j':>3} {'p':>10} {'m=2^j':>9} {'beta':>5} {'B':>9} "
              f"{'B/Sp':>7} {'B/Sm2':>7} {'logMeff/logm':>12}")
        for j in range(3, 22):
            m = 1 << j
            p = n * m + 1
            if p > 5_000_000:
                break
            if not is_prime(p):
                continue
            Bsq = all_periods_abs(p, n)
            B = Bsq
            lnp = math.log(p); lnm = math.log(m)
            rp = B / math.sqrt(2 * n * lnp)
            rm = B / math.sqrt(2 * n * lnm)
            logMeff = B * B / (2.0 * n)
            bb = lnp / math.log(n)
            mark = "  <-Sp FALSE" if rp > 1 else ""
            flush(f"     {j:>3} {p:>10} {m:>9} {bb:>5.2f} {B:>9.2f} "
                  f"{rp:>7.3f} {rm:>7.3f} {logMeff/lnm:>12.3f}{mark}")
    flush(f"\n{'='*100}")
    flush("# If MOST-DYADIC rows inflate vs MOST-ODD at the same beta, AND the dyadic ladder keeps")
    flush("# S_p violated as j->infty, the necessary-condition object is the 2-ADIC m, and the prize")
    flush("# (m=2^128, fully dyadic) is ON the violating side -- so thinness/thickness is NOT the")
    flush("# right axis; the 2-adic worst-index phenomenon is. That sharpens (or corrects) T18.")
    flush(f"{'='*100}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
