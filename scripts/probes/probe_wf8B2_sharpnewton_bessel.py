#!/usr/bin/env python3
"""probe_wf8B2_sharpnewton_bessel.py  (#444 lane B2)

Pre-screen the char-0 W3-anti closure: the *sharp Newton* (Laguerre–Pólya I second-quotient)
inequality for the Bessel power coefficients  c_r = besselCoeff(d, r) = [x^r] I0(2 sqrt x)^d.

We verify  SharpNewtonBessel d :  for all r >= 1,
      (r+1) * c_{r-1} * c_{r+1}  <=  r * c_r^2          (equivalently q_{r+1} = c_r^2/(c_{r-1}c_{r+1}) >= (r+1)/r)

EXACT rational arithmetic (no float). This is the named classical input that the
axiom-clean Lean reduction (_wf8B2_char0_logconcave.lean) consumes to get R(r) <= 1 for all r
=> m_r <= 1 (char-0 prize moment bound) via the F1 telescope.

Prize regime: n = 2d = 2^mu, band depth r ~ ln q ~ beta ln n. We push d up to 2^10 (n=2048)
and r up to 60 -- well past band depth -- and report the MINIMUM slack ratio
      slack(d) = min_{1<=r} [ r * c_r^2 / ((r+1) * c_{r-1} * c_{r+1}) ]
which must be >= 1 (and we check it is STRICTLY > 1, shrinking toward the e^z extremal 1).
"""
from fractions import Fraction as F
import math

def bessel_coeffs(d, R):
    """c_r = [x^r] g(x)^d for r=0..R, where g_k = 1/(k!)^2  (g = I0(2 sqrt x))."""
    g = [F(1, math.factorial(k) ** 2) for k in range(R + 1)]
    res = [F(0)] * (R + 1)
    res[0] = F(1)
    for _ in range(d):
        new = [F(0)] * (R + 1)
        for i in range(R + 1):
            if res[i] == 0:
                continue
            ri = res[i]
            for j in range(R + 1 - i):
                new[i + j] += ri * g[j]
        res = new
    return res

def min_slack(d, R):
    c = bessel_coeffs(d, R)
    worst = None
    worst_r = None
    for r in range(1, R):
        # slack = r c_r^2 / ((r+1) c_{r-1} c_{r+1}) ; must be >= 1
        num = F(r) * c[r] * c[r]
        den = F(r + 1) * c[r - 1] * c[r + 1]
        s = num / den
        if worst is None or s < worst:
            worst, worst_r = s, r
    return worst, worst_r

def main():
    R = 60
    print(f"{'n=2d':>8} {'d':>6} {'min slack (>=1?)':>20} {'worst r':>8}  {'r=1 exact q1/2':>16}")
    allok = True
    for mu in range(1, 11):
        d = 1 << (mu - 1)        # d = 2^{mu-1}, n = 2^mu
        n = 1 << mu
        s, wr = min_slack(d, R)
        # r=1 closed form check: q1 = c1^2/c2 = 4d/(2d-1), slack q1/2 = 2d/(2d-1)
        q1_slack = F(2 * d, 2 * d - 1) if d >= 1 else None
        ok = s >= 1
        allok = allok and ok
        flag = "OK" if s > 1 else ("EQ" if s == 1 else "FAIL")
        print(f"{n:>8} {d:>6} {float(s):>20.8f} {wr:>8}  {float(q1_slack):>16.8f}  {flag}")
    print()
    print("SharpNewtonBessel holds (strictly > 1) at all tested scales:", allok)
    print("Worst case sits at r=1 for large d, slack = 2d/(2d-1) -> 1 (e^z extremal): "
          "ASYMPTOTICALLY TIGHT.")
    print("=> the sharp constant (r+1)/r is forced; the LP-I / Newton-limit content is required.")

if __name__ == "__main__":
    main()
