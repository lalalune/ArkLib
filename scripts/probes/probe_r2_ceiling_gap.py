import math
# r=2 per-frequency ceiling (PROVEN, eta_quartic_le_muN_two): ||eta_b||^4 <= q*3*n^2
#   => ||eta_b|| <= (3q)^{1/4} * sqrt(n)
# prize target: M(mu_n) <= C * sqrt(n * log(p/n)), q=p field size, n=2^a, q=n^beta (beta~4-5)
# Q1: restate the proven 4th-power bound in sup-norm units (4th root). EXACT, no new content.
# Q2: how far is the r=2 ceiling (3q)^{1/4}*sqrt(n) ABOVE the prize sqrt(n*ln(q/n))?
#     If ceiling > prize for all prize-regime (n,beta), the r=2 ceiling does NOT reach the prize
#     (honest gap: it is a POLYNOMIAL-in-n factor too weak). ratio>1 expected, growing.
print("n, beta, q=n^beta, r2_ceiling=(3q)^.25*sqrt(n), prize=sqrt(n*ln(q/n)), ratio")
fails = 0
tot = 0
for a in [4, 5, 6, 8, 10, 16, 20, 30]:
    n = 2 ** a
    for beta in [4.0, 4.5, 5.0]:
        q = n ** beta
        ceiling = (3 * q) ** 0.25 * math.sqrt(n)
        prize = math.sqrt(n * math.log(q / n))
        ratio = ceiling / prize
        tot += 1
        if ratio <= 1:
            fails += 1
        exp_ceiling = (beta + 2) / 4.0
        print("n=2^%-2d beta=%s q=n^%s: ceil~n^%.3f=%.3e  prize=%.3e  ratio=%.3f"
              % (a, beta, beta, exp_ceiling, ceiling, prize, ratio))
print("")
print("fails (ratio<=1, ceiling NOT above prize): %d/%d" % (fails, tot))
print("ceiling exponent (beta+2)/4: beta=4 -> %.3f ; beta=5 -> %.3f ; prize exponent ~0.5"
      % ((4 + 2) / 4.0, (5 + 2) / 4.0))
# Cross-check the EXACT integer envelope used in Lean: ||eta||^4 <= q*3*n^2 with q=p>2^n.
# Vacuity guard: at the smallest prize instance n=16 (a=4), p just above 2^16, the bound is
# a real finite number (not vacuous), and the 4th root is well-defined (RHS>=0).
n = 16
p = 2 ** n + 1
rhs4 = p * 3 * n ** 2
print("vacuity check n=16,p=2^16+1: ||eta||^4 <= %d (finite, positive) -> ||eta|| <= %.4e"
      % (rhs4, rhs4 ** 0.25))
