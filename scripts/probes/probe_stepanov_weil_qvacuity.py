#!/usr/bin/env python3
"""
PROBE [bivstep] — the Stepanov-Weil sqrt(q) field-bound is VACUOUS on mu_n in the prize regime,
and Johnson sqrt(kn) sits strictly below BOTH Stepanov outputs (trivial deg=n-1 AND sqrt(q)).

THE OBJECT (issue #444/#407, intrinsic):
  mu_n = 2-power multiplicative subgroup of F_q*, n = 2^a, n | q-1, q PRIME power, prize regime
  q ~ n^beta, beta in [4,5] (the brief: p >> n^3). s* = max far-line zero count on mu_n.

TWO Stepanov outputs on mu_n (both in-tree as prose in StepanovStructuredVacuous docstring,
NOT formalized as the q-regime arithmetic theorem):
  (A) classical Stepanov on the SEPARABLE X^n-1: multiplicity pinned to M=1 => trivial deg bound
      s* <= deg P <= n-1.  (mu_n_roots_simple, stepanov_collapses_to_degree -- LANDED.)
  (B) Stepanov-Weil / Kelley-Owen over F_q: a t-nomial has ~ sqrt(q) field roots; bound is in
      sqrt(q), NOT in subgroup size.

CLAIM TO CHECK (one sweep, exact integer arithmetic, multiple prize-regime (n, q=n^beta)):
  In the prize regime q >= n^3 (so beta >= 3; prize beta in [4,5]):
    1.  sqrt(q) >= n           => the Weil FIELD bound (B) EXCEEDS the trivial degree bound (A)=n-1
                                  => (B) is VACUOUS (worse than the trivial bound) on mu_n.
    2.  sqrt(k*n) < n          for every k < n  => Johnson is strictly below the trivial bound (A).
    3.  sqrt(k*n) < sqrt(q)    => Johnson strictly below the Weil bound (B) too.
  => NEITHER Stepanov form reaches Johnson sqrt(kn); the Weil form is additionally vacuous.

This is the SECOND Stepanov stall mechanism (the first = separability/M=1 collapse, already in
tree). Refutation-with-mechanism, NON-moment, field-arithmetic, thinness enters only via the
prize regime q >> n (mu_n THIN). cliff-at-n/2 untouched (no capacity claim).
"""
import math

def isqrt(x):
    return math.isqrt(x)

print("n     beta  q=n^beta            isqrt(q)  n-1   sqrt(q)>=n?  Johnson sqrt(kn)(k=n/4) < n?  < sqrt(q)?")
fails = 0
for a in range(3, 9):              # n = 2^a, a=3..8 (n=8..256)
    n = 1 << a
    for beta in (3, 4, 5):         # prize regime beta>=3 (prize 4..5); beta=3 = boundary
        q = n ** beta
        sq = isqrt(q)
        # 1. sqrt(q) >= n  (q >= n^2 suffices; beta>=3 => certainly)
        c1 = (q >= n * n)          # exact: sqrt(q) >= n  iff  q >= n^2
        # 2. Johnson < trivial(n): sqrt(kn) < n iff kn < n^2 iff k < n. take worst interior k=n/4
        k = n // 4 if n >= 4 else 1
        c2 = (k * n < n * n)       # sqrt(kn) < n  iff  kn < n^2  iff  k<n
        # 3. Johnson < sqrt(q): kn < q
        c3 = (k * n < q)
        ok = c1 and c2 and c3
        if not ok:
            fails += 1
        print(f"{n:<5} {beta:<5} {q:<19} {sq:<9} {n-1:<5} {str(c1):<12} k={k:<4} {str(c2):<28} {str(c3)}")

print()
print(f"TOTAL FAILS: {fails}")
print("VERDICT:" , "ALL HOLD -- Weil sqrt(q) bound VACUOUS on mu_n; Johnson strictly below BOTH Stepanov outputs."
      if fails == 0 else "SOME FAILED -- claim is wrong, do NOT formalize.")
