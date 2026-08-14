# Probe: confirm the geometric-minor budget discharge is NON-VACUOUS at prize regime.
# Object: minorPoly(g_a,g_{a-1},g_b,g_{b-1}) = X^a * g_{b-a-1}, deg = b-1.
# Budget: |forcedGammaImage| <= deg = b-1.  Discharge MinorImageLeBudget(n) needs b-1 <= n.
# Prize regime: thin 2-power mu_n, span D = b <= n = 2^a. Confirm b-1 < n strictly (halving vs 2D),
# and verify the EXACT minor identity g_a g_{b-1} - g_{a-1} g_b = X^a g_{b-a-1} as polynomials.
import sympy as sp
X = sp.symbols('X')

def g(c):  # geometric readout row 1+X+...+X^c
    return sum(X**i for i in range(c + 1))

print("identity + degree sweep (a<b, prize-scale spans b=2^k):")
ok_id = True
for k in range(3, 9):                 # n = 2^k
    n = 2 ** k
    b = n                             # worst row degree = span = n
    for a in (1, n // 4, n // 2 - 1): # several binding offsets a<b
        if not (1 <= a < b):
            continue
        lhs = sp.expand(g(a) * g(b - 1) - g(a - 1) * g(b))
        rhs = sp.expand(X ** a * g(b - a - 1))
        idok = sp.simplify(lhs - rhs) == 0
        deg = sp.Poly(lhs, X).degree() if lhs != 0 else -1
        budget_ok = (deg == b - 1) and (deg < b) and (deg <= n)  # <= prize budget n
        halving = deg < 2 * b                                    # strictly below generic 2D
        ok_id = ok_id and idok and budget_ok and halving
        if a in (1, n // 2 - 1):
            print(f"  n={n} b={b} a={a}: id={idok} deg={deg} (=b-1? {deg==b-1})"
                  f" <n:{deg<b} <=n:{deg<=n} <2D:{halving}")
print("VERDICT:",
      "PASS (identity exact + deg=b-1 < n <= 2D-halving, budget non-vacuous)"
      if ok_id else "FAIL")
