"""Probe: di Benedetto Thm 3.1 raw-exponent beta-validity window (#444).

di Benedetto-Garaev-Garcia-Gonzalez-Sanchez-Shparlinski-Trujillo, JNT 2020
(arXiv:2003.06165), Thm 3.1 (verbatim): for a multiplicative subgroup H of F_p*
with p^{1/2} > |H| > p^{1/4},
    max_{(a,p)=1} |S_a(H)| <~ |H|^{2689/2880} * p^{1/72}.

With |H| = n and p = n^beta the TOTAL exponent in n is
    E(beta) = 2689/2880 + beta/72,
and the cancellation saving is delta(beta) = 1 - E(beta). The bound is a
NONTRIVIAL power saving (sub-n^1) iff E(beta) < 1 iff delta(beta) > 0.

This probe confirms the exact arithmetic the brief's near-Sidon lane LEANS on:
  - upper nontriviality edge beta* = 191/40 = 4.775 (saving vanishes there),
  - prize point beta=4 recovers the headline 1 - 31/2880 EXACTLY,
  - saving is monotone DECREASING in beta (thinner subgroup => smaller saving),
  - beyond the edge (beta > 191/40) the raw bound is TRIVIAL (E >= 1).
NON-MOMENT, field-universal exponent arithmetic (exact Fraction, no float trust).
"""

from fractions import Fraction as F

a = F(2689, 2880)   # leading exponent of |H| in Thm 3.1
s = F(1, 72)        # coefficient of beta (from the p^{1/72} factor, p = n^beta)


def E(beta: F) -> F:
    return a + s * beta


def delta(beta: F) -> F:
    return 1 - E(beta)


# Upper nontriviality edge: E(beta) = 1  <=>  beta = (1 - 2689/2880)/(1/72).
edge = (1 - a) / s
print("upper nontriviality edge beta* =", edge, "=", float(edge))
assert edge == F(191, 40), edge

# Prize point beta = 4 (n = p^{1/4}) recovers the headline saving 31/2880.
print("E(4) =", E(F(4)), "  delta(4) =", delta(F(4)),
      "  == 1 - 31/2880 ?", delta(F(4)) == F(31, 2880))
assert delta(F(4)) == F(31, 2880)
assert E(F(4)) == F(2849, 2880) == 1 - F(31, 2880)

print("beta sweep (exact):")
for b in [F(2), F(3), F(4), F(9, 2), F(191, 40), F(5)]:
    d = delta(b)
    print(f"  beta={float(b):.4f}  E={float(E(b)):.6f}  "
          f"delta={float(d):.6f}  nontrivial={d > 0}")

# Verdict checks (exact).
assert delta(F(191, 40)) == 0          # saving vanishes EXACTLY at the edge
assert delta(F(5)) < 0                  # trivial beyond the edge (E > 1)
assert delta(F(2)) > delta(F(4)) > 0    # monotone decreasing, both nontrivial
assert 0 < delta(F(9, 2)) < delta(F(4))  # 4.5 still nontrivial but smaller saving
print("ALL CHECKS PASS")
