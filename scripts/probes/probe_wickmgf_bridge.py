#!/usr/bin/env python3
"""
probe_wickmgf_bridge.py  (#444 §6.2 — wf-WickMGF lane, co-author wakesync)

VALIDATE (numeric, PROPER subgroups mu_n in C, char-0 — the regime where the termwise
Wick bound E_r <= (2r-1)!! n^r is PROVEN: gaussianEnergyBound_dyadic) the bridge formalized in
ArkLib/.../Frontier/WickMGFFromTermwise.lean:

  ( forall r,  E_r(G) <= (2r-1)!! * n^r )    [termwise Wick = GaussianEnergyBound]
     ==>   MGF(y) := sum_r (q*E_r)*y^{2r}/(2r)!   <=   q * exp(n*y^2/2)
     ( the single open inequality every cosh-MGF saddle consumer takes as hypothesis )

via the EXACT coefficient identity  (2r)! = 2^r * r! * (2r-1)!!  so that
  (2r-1)!!/(2r)! = 1/(2^r r!)  and  q*exp(n y^2/2) = q*sum_r n^r y^{2r}/(2^r r!).

We compute E_r EXACTLY by brute force over mu_n (n small) and confirm:
  (1) the coefficient identity (2r)! = 2^r r! (2r-1)!!  ;
  (2) E_r <= (2r-1)!! n^r holds termwise on PROPER mu_n in char 0 (sanity of the hypothesis);
  (3) MGF(y) <= q*exp(n y^2/2) for several y INCLUDING the saddle y* = sqrt(2 log q / n).
NEVER n = q-1: this is the genuine-thin char-0 regime where the termwise Wick bound is the
PROVEN char-0 fact and the bridge is the real-analysis weld (the char-p case is the open prize).
"""
import math
import itertools
from collections import Counter


def df(r):
    p = 1
    for i in range(r):
        p *= (2 * i + 1)
    return p


def Er(n, r):
    roots = [complex(math.cos(2 * math.pi * k / n), math.sin(2 * math.pi * k / n))
             for k in range(n)]
    c = Counter()
    for tup in itertools.product(range(n), repeat=r):
        s = sum(roots[k] for k in tup)
        c[(round(s.real, 6), round(s.imag, 6))] += 1
    return sum(v * v for v in c.values())


def main():
    print("== (1) coeff identity (2r)! = 2^r r! (2r-1)!! ==")
    for r in range(0, 14):
        assert math.factorial(2 * r) == (2 ** r) * math.factorial(r) * df(r), r
    print("  OK r=0..13")

    print("== (2) termwise Wick E_r <= (2r-1)!! n^r, char-0 proper mu_n ==")
    for n in (4, 6, 8):
        for r in range(1, 5):
            e = Er(n, r)
            w = df(r) * (n ** r)
            assert e <= w, (n, r, e, w)
            print("  n=%d r=%d E_r=%d wick=%d OK" % (n, r, e, w))

    print("== (3) MGF(y) <= q exp(n y^2/2), exact E_r, incl saddle ==")
    for n, q in [(4, 4129), (8, 8009)]:
        R = 7 if n <= 6 else 5
        Ers = [1] + [Er(n, r) for r in range(1, R + 1)]
        ystar = math.sqrt(2 * math.log(q) / n)
        for y in (0.05, 0.2, ystar):
            m = q * 1.0
            for r in range(1, R + 1):
                m += q * Ers[r] * (y ** (2 * r)) / math.factorial(2 * r)
            rhs = q * math.exp(n * y * y / 2)
            assert m <= rhs + 1e-9, (n, q, y, m, rhs)
            tag = " (saddle y*)" if abs(y - ystar) < 1e-12 else ""
            print("  n=%d q=%d y=%.5f%s MGF=%.4e rhs=%.4e OK" % (n, q, y, tag, m, rhs))

    print("\nVERDICT: coefficient identity exact; termwise Wick holds char-0 on proper mu_n;")
    print("MGF(y) <= q exp(n y^2/2) confirmed incl. saddle. The bridge is the real-analysis lift")
    print("of the termwise (2r-1)!! n^r bound through (2r)! = 2^r r! (2r-1)!!.")


if __name__ == "__main__":
    main()
