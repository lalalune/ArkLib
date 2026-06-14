#!/usr/bin/env python3
"""
probe_dualcode_krawtchouk.py  (#389 — proximity prize: the Shaw operator's classical face)

VALIDATED three-way unification of the prize's multiplicity incidence (exact, q=7,n=6,k=2):

  Let C = RS[mu_n, k], S = delta-neighborhood of C (= C + B, B = Hamming ball radius r=n-t).
  The MULTIPLICITY incidence  M = sum_gamma #{c in C : wt(s0 + gamma*s1 - c) <= r}  is an UPPER
  BOUND on the true far-line incidence I(delta) = #{gamma : s0+gamma*s1 is delta-close to C}
  (equal when lists are <= 1; in the window M = I * (avg list)).  Three identities, all
  VALIDATED EXACTLY here:

  (1) FOURIER / dual-code Krawtchouk (convolution theorem, Chat(a)=|C|*1_{a in Cperp}, Bhat=Krawtchouk):
        M = (|F||C|/|V|) * ( |B|  +  sum_{a in Cperp cap s1perp, a != 0} K(wt a) * e(a . s0) )
      => the Shaw fluctuation is a KRAWTCHOUK-WEIGHTED TWISTED CHARACTER SUM over the dual RS code's
         hyperplane section Cperp cap s1perp (dim n-k-1).  Dual of RS is MDS => weight distn KNOWN.

  (2) MacWilliams collapse (sum_{a in L} fhat(a) e(a.s0) = |L| sum_{x in Lperp} f(s0+x), Lperp=C+<s1>):
        M = #{ x in C+<s1> : wt(s0 + x) <= r }
      => M = the LIST SIZE of the EXTENDED code C+<s1> (dim k+1) within radius r of s0.

  So the Shaw operator (additive-Fourier), the dual-code Krawtchouk-twisted sum, and extended-code
  list-decoding are ONE object with three faces, unified by MacWilliams.

HONEST SCOPE: this is validated machinery that makes the prize's equivalences crisp and computable,
but it LANDS BACK ON THE LIST-DECODING WALL (the multiplicity-relaxed MCA incidence = list size of
a dim-(k+1) code).  It does NOT escape the wall; it shows the Shaw fluctuation IS the extended-code
list deviation.  The open prize = bound that deviation (= the dual-RS Krawtchouk sum cancellation),
the W4 sub-sqrt(q) character-sum problem.  See issue389-shaw-operator-assessment,
issue389-schur-roots-of-unity-lever.

USAGE: python3 probe_dualcode_krawtchouk.py
"""
import itertools
import cmath
import math


def run(q=7, n=6, k=2, r=3, seed=1):
    D = list(range(1, n + 1))  # mu_n = F_q^* for q=7,n=6 (or first n nonzero); eval points
    w = cmath.exp(2j * math.pi / q)

    def ch(a, x):
        return w ** (sum(ai * xi for ai, xi in zip(a, x)) % q)

    def evalpoly(coef, x):
        rr = 0
        for c in reversed(coef):
            rr = (rr * x + c) % q
        return rr

    def wt(v):
        return sum(1 for x in v if x % q != 0)

    def vadd(u, v):
        return tuple((a + b) % q for a, b in zip(u, v))

    def vsub(u, v):
        return tuple((a - b) % q for a, b in zip(u, v))

    def smul(g, v):
        return tuple((g * a) % q for a in v)

    C = [tuple(evalpoly(coef, x) % q for x in D) for coef in itertools.product(range(q), repeat=k)]
    Cset = set(C)
    allv = list(itertools.product(range(q), repeat=n))
    Cperp = [a for a in allv if all(sum(ai * ci for ai, ci in zip(a, c)) % q == 0 for c in C)]
    Ball = [v for v in allv if wt(v) <= r]

    import random
    random.seed(seed)
    s1 = tuple(random.randrange(q) for _ in range(n))
    while s1 in Cset:
        s1 = tuple(random.randrange(q) for _ in range(n))
    s0 = tuple(random.randrange(q) for _ in range(n))

    def dot(a, b):
        return sum(ai * bi for ai, bi in zip(a, b)) % q

    def Bhat(a):
        return sum(ch(a, v) for v in Ball)

    # (0) DIRECT multiplicity incidence
    M = sum(sum(1 for c in C if wt(vsub(vadd(s0, smul(g, s1)), c)) <= r) for g in range(q))
    # (1) Fourier / dual-code Krawtchouk
    inter = [a for a in Cperp if dot(a, s1) == 0]
    shaw = sum(Bhat(a) * ch(a, s0) for a in inter if any(x for x in a))
    rhs = (q * len(C) / q ** n) * (len(Ball) + shaw)
    # (2) MacWilliams -> extended-code list size
    Cext = set(vadd(c, smul(g, s1)) for c in C for g in range(q))
    listext = sum(1 for x in Cext if wt(vadd(s0, x)) <= r)

    print(f"q={q} n={n} k={k} r={r}:  |C|={len(C)} |Cperp|={len(Cperp)} |B|={len(Ball)} |C+<s1>|={len(Cext)}")
    print(f"  (0) DIRECT multiplicity M        = {M}")
    print(f"  (1) Fourier/dual-Krawtchouk      = {rhs.real:.4f}   match={abs(M - rhs) < 1e-6}")
    print(f"  (2) extended-code list size      = {listext}   match={M == listext}")
    print(f"  average=(|F||C||B|/|V|)={q * len(C) * len(Ball) / q ** n:.3f}  shaw-fluct(normalized)="
          f"{(q * len(C) / q ** n) * abs(shaw):.3f}")


if __name__ == "__main__":
    run()
