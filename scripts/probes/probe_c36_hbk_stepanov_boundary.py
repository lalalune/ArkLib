#!/usr/bin/env python3
"""
Probe for CONJECTURE [C36] — "Heath-Brown-Konyagin Single-Curve Stepanov at the
Prize Boundary."

C36 claims: the proven single-curve HBK Stepanov bound
    M(mu_n) <= min(n^{5/8} p^{1/8}, n^{3/8} p^{1/4})
"becomes nontrivial (below n) exactly at the prize boundary" and thereby gives a
PAST-Johnson sup-norm.

This probe checks the elementary arithmetic of that bound against the prize regime
(n = 2^mu, p prime ~ n^beta, beta in {4,5}; NEVER n = p-1).

VERDICT (computed below): the HBK bound is ABOVE the trivial bound n across the
ENTIRE prize band (beta >= 3). It only dips below n for beta < 3, i.e. p < n^3 ---
which the honesty contract explicitly forbids (probes require p >> n^3). And it
NEVER reaches the Johnson/sqrt scale (~ n^{1/2}) for any beta > 0 except the
forbidden full-group limit beta -> 0 (p ~ n). So C36 is REFUTED-FALSE: the bound is
vacuous in the prize regime, far from Johnson, let alone past it.

HBK exponents (writing p = n^beta, both bounds as powers of n):
    e1 = 5/8 + beta/8     (from n^{5/8} p^{1/8})
    e2 = 3/8 + beta/4     (from n^{3/8} p^{1/4})
    e_min = min(e1, e2)   (HBK bound ~ n^{e_min})
Nontrivial (below n) iff e_min < 1.
Johnson-relevant iff e_min <= ~1/2.
"""

def e1(beta): return 5/8 + beta/8
def e2(beta): return 3/8 + beta/4
def emin(beta): return min(e1(beta), e2(beta))

print("=" * 78)
print("C36 PROBE: HBK min(n^{5/8}p^{1/8}, n^{3/8}p^{1/4}) vs n in prize regime")
print("=" * 78)

# Thresholds (solve e_i(beta) = target).
print("\n[A] Where does HBK become NONTRIVIAL (e_min < 1)?")
print(f"    e1<1  <=>  beta < {(1-5/8)*8:.3f}   (= 3.0)")
print(f"    e2<1  <=>  beta < {(1-3/8)*4:.3f}   (= 2.5)")
print("    => HBK is sub-trivial only for beta < 3, i.e. p < n^3.")
print("    HONESTY CONTRACT requires p >> n^3 (NEVER p < n^3): HBK is OUTSIDE the")
print("    legal regime entirely. At beta=3 exactly, e_min = 1.0 (equals trivial).")

print("\n[B] Where does HBK reach the JOHNSON scale (e_min <= 1/2)?")
print(f"    e1<=1/2 <=> beta <= {(0.5-5/8)*8:.3f}  (impossible, beta>0)")
print(f"    e2<=1/2 <=> beta <= {(0.5-3/8)*4:.3f}  (= 0.5)")
print("    => Johnson scale only reachable for beta <= 1/2 (p <= sqrt(n)), which is")
print("    DEEP in the forbidden full-group regime. Past-Johnson: NEVER.")

print("\n[C] Concrete prize points (n = 2^30, p ~ n^beta):")
mu = 30
n = 2.0 ** mu
print(f"    n = 2^{mu} = {n:.3e}")
print(f"    {'beta':>5} | {'HBK exp e_min':>14} | {'HBK ~ 2^?':>12} | {'n = 2^':>7} | sub-trivial?")
for beta in [3, 4, 5, 6]:
    em = emin(beta)
    log2_bound = mu * em            # since bound = n^{em} = 2^{mu*em}
    print(f"    {beta:>5} | {em:>14.3f} | {('2^%.1f' % log2_bound):>12} | "
          f"{('2^%.0f' % mu):>7} | {'YES' if em < 1 else 'NO'}")

print("\n[D] The prize beta band {4,5}: HBK bound exponent vs trivial and Johnson")
for beta in [4, 5]:
    em = emin(beta)
    print(f"    beta={beta}: HBK ~ n^{em:.3f}  >  n^1.0 (trivial)  >>  n^0.5 (Johnson)")
    print(f"             EXCESS over trivial: factor n^{em-1:.3f} = "
          f"2^{(em-1)*mu:.1f} at n=2^30  => bound exceeds n by a factor ~2^{(em-1)*mu:.0f}")

print("\n" + "=" * 78)
print("CONCLUSION: REFUTED-FALSE. min(n^{5/8}p^{1/8}, n^{3/8}p^{1/4}) >= n^{9/8}")
print("for all beta in the prize band {4,5} -- it is WORSE THAN TRIVIAL, not")
print("'nontrivial below n', and exponentially far from the Johnson sqrt(n) scale,")
print("let alone past-Johnson. The only beta making it sub-trivial is beta<3")
print("(p<n^3), which the honesty contract forbids and which is NOT the prize.")
print("No 'sharpened auxiliary-degree budget' can move the EXPONENT: it is fixed")
print("by the Stepanov degree/multiplicity accounting (deg ~ p^{1/2}-strength via")
print("Frobenius x^q=x), and the in-tree StepanovStructuredVacuous.lean proves the")
print("subgroup relation X^n-1 is SEPARABLE so manufactures NO multiplicity -- the")
print("Frobenius sqrt-saving the HBK exponents encode does not even apply to mu_n.")
print("=" * 78)
