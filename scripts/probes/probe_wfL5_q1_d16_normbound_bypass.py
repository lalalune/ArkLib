"""
wf-L5 (#444): the char-p NORM-BOUND BYPASS for Chai-Fan Q1 at d=16.

Companion to probe_wfL5_q1_d16_minpoly_obstruction.py. That probe pinned WHY there is no uniform
resultant R_16 (the exponent of (Z/16)* is 4 < 8 = phi(16), so deg(minpoly_{F_p} w) <= 4 always).

This probe shows the bypass that nonetheless delivers Q1 char-p at PRIZE SCALE unconditionally:

  For a {-1,0,1}-combo P(w) = sum_{j<8} c_j w^j, the resultant/norm
      R(c) = Res(Phi_16, P) = Norm_{Q(zeta_16)/Q}(P(zeta_16))
  is a RATIONAL INTEGER. char-0 Q1 (chaiFan_Q1_charZero) says R(c) != 0 for every nonzero c.
  And |R(c)| <= 2401 = 7^4 over all nonzero c in {-1,0,1}^8 (exact, below).

  P(w) = 0 in a field of char p  <=>  p | R(c).  But 0 < |R(c)| <= 2401, so for every prime
  p > 2401 we have p does NOT divide R(c): Q1 holds char-p for EVERY prime p > 2401.

  Prize regime: p ~ n^4 with n = d = 16 => p >= 16^4 = 65536 > 2401. (And the actual prize prime
  p ~ 2^120 >> 2401.) So Q1 holds char-p at prize scale at d=16 -- by the norm bound, a genuine
  theorem, not just the 3^8/p < 1 pigeonhole heuristic.

This is computed with an INDEPENDENT engine (direct complex-conjugate product, no sympy) and
cross-checked against sympy's resultant.
"""
import cmath, itertools
from math import gcd

half = 8  # phi(16)
prim = [cmath.exp(2j * cmath.pi * k / 16) for k in range(16) if gcd(k, 16) == 1]

# (A) Independent engine: |Norm(P(zeta))| = |prod over primitive 16th roots P(w)|.
maxnorm = 0
argmax = None
nonint = 0
for c in itertools.product((-1, 0, 1), repeat=half):
    if not any(c):
        continue
    norm = 1.0 + 0j
    for w in prim:
        norm *= sum(c[j] * w ** j for j in range(half))
    nr = round(norm.real)
    if abs(norm.real - nr) > 1e-6 or abs(norm.imag) > 1e-6:
        nonint += 1
        continue
    if nr == 0:
        # char-0 Q1: this must never happen for nonzero c.
        raise AssertionError(f"char-0 Q1 VIOLATED: Norm=0 for nonzero c={c}")
    if abs(nr) > maxnorm:
        maxnorm = abs(nr); argmax = c

assert nonint == 0, f"unexpected non-integer norms: {nonint}"
print("=== (A) independent norm engine ===")
print(f"max |Norm_(Q(z16)/Q)(P(z))| over nonzero c in {{-1,0,1}}^8 = {maxnorm} = 7^4 = {7**4}")
print(f"achieved at c = {argmax}")
print(f"char-0 Q1 holds: Norm != 0 for all {3**half - 1} nonzero c (no AssertionError).")

# (B) Cross-check with sympy resultant Res(Phi_16, P) for a sample of c.
import sympy as sp
x = sp.symbols('x')
Phi16 = sp.cyclotomic_poly(16, x)
import random
random.seed(0)
sample = [tuple(random.choice((-1, 0, 1)) for _ in range(half)) for _ in range(200)]
maxres = 0
for c in sample:
    if not any(c):
        continue
    P = sum(c[j] * x ** j for j in range(half))
    R = abs(int(sp.resultant(Phi16, P, x)))
    maxres = max(maxres, R)
    assert R <= maxnorm, f"resultant {R} exceeds norm bound {maxnorm} for c={c}"
print("\n=== (B) sympy resultant cross-check (200 samples) ===")
print(f"all |Res(Phi_16, P)| <= {maxnorm}; sample max = {maxres}.")

# (C) The bypass verdict.
print("\n=== (C) verdict ===")
print(f"For every prime p > {maxnorm}: p does NOT divide Res, so P(w) != 0 in char p")
print(f"=> Chai-Fan Q1 holds char-p at d=16 for every prime p > {maxnorm}.")
print(f"prize regime p ~ n^4 = 16^4 = {16**4} > {maxnorm}: {16**4 > maxnorm}  (prize prime ~2^120 >> bound)")
print("NORM-BOUND BYPASS: Q1 char-p at d=16 is a THEOREM at prize scale, via |Res| <= 2401 < p.")
