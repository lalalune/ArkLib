import math

# ===================================================================
# LEVER 3 VERDICT — is the Ring-LWE/ideal-SVP machinery a real handle?
# ===================================================================
#
# The cross-surplus count we need to UPPER-BOUND is
#   crossCell(r) ~ #{ nonzero alpha in p0 : l1-weight(alpha) <= 2r }
# (each such alpha = one vanishing-subset / Q4 witness). The prize needs this
# count CONTROLLED (specifically -> the b!=0 char sum <= sqrt(2n ln q)).
#
# WHAT THE SVP MACHINERY GIVES (CDPR / Biasse-Song / 2601.07511):
#   * lambda_1^{l2}(p0) <= (2 d^2 p)^{1/4}      [UPPER bound; 2601 Thm]
#   * recover ONE short generator via log-unit decode  [ALGORITHM, promise-based]
#   * approx-SVP factor exp(Otilde(sqrt(deg)))         [ALGORITHM]
# All three are: (a) UPPER bounds on lambda_1 (a short vector EXISTS),
#               (b) about ONE vector, not a COUNT,
#               (c) in l2/canonical norm, not the l1 wrap budget.
#
# DIRECTION MISMATCH (fatal): To get Q4 = 0 you need lambda_1 LARGE (a LOWER
# bound: no short vector). SVP gives lambda_1 SMALL (upper). So the machinery
# proves the OPPOSITE of what helps -- it certifies witnesses EXIST.
#
# Let us quantify how badly. The 2601 upper bound vs the needed l1 budget:
print("Does SVP's lambda_1 UPPER bound even keep witnesses OUT of the budget ball?")
print("(If lambda_1^{l1} <= budget, a witness provably EXISTS => Q4 != 0.)\n")
print(f"{'n':>10} {'d':>9} {'lam1_l2<=':>12} {'->l1<=sqrt(d)*':>14} {'2r budget':>10} {'witness?':>9}")
for mu in [7,8,10,20,30]:
    n=2**mu; d=n//2
    p = n*(2.0**128)
    lnq = math.log(p)
    budget = 2*lnq
    lam2 = (2*d*d*p)**0.25
    lam1_upper = math.sqrt(d)*lam2     # l1 <= sqrt(dim)*l2
    # The girth (true min l1) ~ log_n p (counting); SVP's l1 upper is ENORMOUS.
    girth = lnq/math.log(n)
    verdict = "EXISTS" if girth <= budget else "none"
    print(f"{n:>10} {d:>9} {lam2:>12.3e} {lam1_upper:>14.3e} {budget:>10.1f} {verdict:>9}")

print()
print("KEY POINT: the SVP l1-upper-bound (sqrt(d)*lam2 ~ 1e12+) is USELESS as a")
print("witness-existence certificate -- it is WAY above the 2r~187 budget. The")
print("REAL min-l1 girth is the COUNTING value log_n(p)~19, far BELOW budget,")
print("so witnesses exist by counting, NOT by any SVP geometry. SVP norm (l2)")
print("and SVP direction (upper) are both wrong for the prize.\n")

print("="*68)
print("Why the SVP factor exp(sqrt(deg)) cannot be the prize cancellation:")
print("="*68)
# The prize wants B = max|eta_b| <= sqrt(2 n ln q). The SVP 'gain' is the
# ratio Minkowski/2601 = (d p^{1/4}) / (2d^2 p)^{1/4} = (d / (2d^2)^{1/4})
#  ... it's an O(sqrt(d)) geometric improvement, a polynomial-in-d factor,
# NOT a sqrt-cancellation of an exponential character sum. Compare scales:
for mu in [7,10,20,30]:
    n=2**mu; d=n//2
    gain = (d*1.0)/((2*d*d)**0.25)            # Minkowski l2 / 2601 l2, p-indep part
    print(f" n={n:>10}: 2601-over-Minkowski l2 gain factor = {gain:8.2f} "
          f"(= poly(d)~d^{math.log(gain)/math.log(d):.2f}); "
          f"prize needs exp-sum collapse n->sqrt(n)= {n}->{math.sqrt(n):.1f}")
