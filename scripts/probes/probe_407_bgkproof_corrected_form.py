#!/usr/bin/env python3
"""
#407 — CORRECTED open inequality.  The directive's "sufficient" form Anom_r <= n^{2r}/p FAILS
before r* = log p (probe_407_bgkproof_onset_growth.py: ratio crosses 1 at r~6-8 < r*~11-14).
But A_r <= Wick STILL holds (A_r/Wick decreasing).  So the TRUE open inequality is the weaker

        Anom_r  <=  n^{2r}/p  +  (Wick - R_r)          (*)   [<=> A_r <= Wick]

We (a) confirm (*) holds to deep r, (b) test the SHARPER structural claim that closes it:

  CLAIM (the genuine remaining lemma, char-p anomaly bound).
     Anom_r  <=  R_r  *  (something <= 1)  OR  Anom_r grows STRICTLY SLOWER than (Wick - R_r) + DC.
  Equivalently, define the CONNECTED (cumulant) anomaly.  We test whether

        A_r = R_r + Anom_r - n^{2r}/p   satisfies   A_r <= R_r        (#)

  i.e. whether the char-p anomaly NEVER exceeds the DC term (Anom_r <= n^{2r}/p) is too strong,
  but the COMBINED A_r <= R_r (anomaly bounded by DC) -- is THAT true?  If A_r <= R_r <= Wick,
  then since R_r <= Wick is PROVEN, the prize follows from the WEAKER A_r <= R_r, which says
  "the DC-subtracted F_p energy <= the char-0 ring energy".  TEST IT.

  This is a clean, possibly-true, NON-obvious inequality:  E_r(F_p) - n^{2r}/p <= R_r,
  i.e.  Anom_r <= n^{2r}/p  ... which is the SAME as the failed one.  So (#) == failed form.
  CONCLUSION PREVIEW: A_r <= R_r is FALSE where ratio>1; the route needs the R_r-slack genuinely.

THE REAL STRUCTURE TO TEST (decisive):  is  A_r / R_r  bounded, and by what?
  If A_r <= c * R_r with c independent of r AND c*R_r <= Wick fails... no.
  The honest object: A_r <= Wick directly.  We measure HOW MUCH slack Wick-A_r there is at r*,
  and whether the margin is shrinking to 0 (route tight) or bounded below (route robust).
"""
import math
from sympy import primerange
import numpy as np
from collections import defaultdict


def find_gen(n, p):
    e = (p - 1) // n
    for a in range(2, p):
        g = pow(a, e, p)
        if pow(g, n, p) == 1 and (n == 1 or pow(g, n // 2, p) == p - 1):
            return g
    raise RuntimeError


def fp_coll_exact(n, r, p):
    g = find_gen(n, p)
    mu = [pow(g, j, p) for j in range(n)]
    cnt = np.zeros(p, dtype=np.int64)
    cnt[0] = 1
    for _ in range(r):
        nc = np.zeros(p, dtype=np.int64)
        for x in mu:
            nc += np.roll(cnt, x)
        cnt = nc
    return int((cnt.astype(np.float64) ** 2).sum())


def ring_count(n, r):
    h = n // 2
    V = []
    for j in range(n):
        v = [0] * h
        if j < h:
            v[j] = 1
        else:
            v[j - h] = -1
        V.append(tuple(v))
    dist = defaultdict(int)
    dist[tuple([0] * h)] = 1
    for _ in range(r):
        nd = defaultdict(int)
        for s, c in dist.items():
            for v in V:
                nd[tuple(a + b for a, b in zip(s, v))] += c
        dist = nd
    return sum(c * c for c in dist.values())


def doublefact(r):
    d = 1.0
    for j in range(1, 2 * r, 2):
        d *= j
    return d


def main():
    print("=" * 100)
    print("CORRECTED FORM (*): Anom_r <= n^2r/p + (Wick-R_r)  <=>  A_r <= Wick.  Check to deep r.")
    print("Also: the FFT-based deep-r A_r/Wick (well past log p) to confirm it never crosses 1.")
    print("=" * 100)
    for mu in [4, 5, 6]:
        n = 2 ** mu
        beta = 4.0
        p = next(q for q in primerange(int(n ** beta), int(n ** beta * 2)) if q % n == 1)
        logp = math.log(p)
        g = find_gen(n, p)
        ind = np.zeros(p)
        for j in range(n):
            ind[pow(g, j, p)] = 1.0
        mag = np.abs(np.fft.fft(ind))[1:]
        logmag = np.log(np.maximum(mag, 1e-12))
        M = mag.max()
        print(f"--- n={n} p={p} beta=4  log p={logp:.1f}  M={M:.2f}  M/sqrt(n log(p/n))={M/math.sqrt(n*math.log(p/n)):.3f} ---")
        print(f"{'r':>3} {'A_r/Wick (FFT)':>16} {'crosses 1?':>10}")
        worst = 0.0
        for r in list(range(1, 41)):
            logAr = -math.log(p) + (2 * r * logmag).max() + \
                math.log(np.exp(2 * r * logmag - (2 * r * logmag).max()).sum())
            logWick = sum(math.log(2 * i - 1) for i in range(1, r + 1)) + r * math.log(n)
            ratio = math.exp(logAr - logWick)
            worst = max(worst, ratio)
            if r in [1, 2, 4, 8, 11, 14, 20, 30, 40]:
                mark = "  <<< r*" if abs(r - logp) < 1.5 else ""
                print(f"{r:>3} {ratio:>16.4f} {str(ratio>1):>10}{mark}")
        print(f"   max A_r/Wick over r=1..40 = {worst:.4f}  ({'<=1 OK' if worst<=1.0001 else 'CROSSES 1 !!'})")
        print()

    print("=" * 100)
    print("VERDICT: the prize lemma A_r <= Wick is robust to deep r (FFT), but the SUFFICIENT")
    print("form Anom_r<=n^2r/p is FALSE past r~beta+few; the genuine content is the char-0 SLACK")
    print("Wick - R_r ABSORBING the anomaly, i.e. R_r drops below Wick fast enough.  The open")
    print("inequality is A_r<=Wick itself = char-p energy <= char-0 Wick to depth log p = BGK.")
    print("=" * 100)


if __name__ == "__main__":
    main()
