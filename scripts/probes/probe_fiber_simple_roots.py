# PROBE: in the prize regime (p >> n^3, p == 1 mod n, char p does not divide n),
# are the fibre roots SIMPLE roots of shiftedPowPoly = (X+1)^n - c^n?
# Equivalently: is X^n - 1 separable (squarefree) so r(c) = deg gcd EXACTLY?
# Thin 2-power mu_n, NEVER n=q-1. Exact GF(p) via sympy.
import sympy
from sympy import GF, Poly, symbols, gcd

X = symbols('X')
results = []
for p in [257, 193, 641, 769, 12289]:
    for n in [8, 16, 32]:
        if (p - 1) % n != 0:
            continue
        if p % n == 0:
            continue  # char | n -- excluded by prize regime
        gen = None
        for a in range(2, p):
            if pow(a, n, p) == 1 and all(pow(a, d, p) != 1 for d in range(1, n)):
                gen = a
                break
        if gen is None:
            continue
        mu = [pow(gen, k, p) for k in range(n)]
        Xn1 = Poly(X**n - 1, X, modulus=p)
        dXn1 = Xn1.diff(X)
        g = gcd(Xn1, dXn1)
        sep = (g.degree() == 0)
        max_mult = 0
        bad = False
        for c in [2, 3, 5, mu[1], mu[2]]:
            cn = pow(int(c), n, p)
            Pc = Poly((X + 1) ** n - cn, X, modulus=p)
            dPc = Pc.diff(X)
            fib = [w for w in mu if pow((1 + w) % p, n, p) == cn]
            for w in fib:
                if Pc.eval(w) % p != 0:
                    bad = True
                if dPc.eval(w) % p == 0:
                    max_mult = max(max_mult, 2)
        results.append((p, n, sep, max_mult, bad))
        print("p=%6d n=%3d  Xn-1 separable=%s  fiber_max_mult=%d  bad_root=%s"
              % (p, n, sep, max_mult, bad))

allsep = all(r[2] for r in results)
allsimple = all(r[3] <= 1 for r in results)
nobad = all(not r[4] for r in results)
print()
print("VERDICT: Xn-1 separable everywhere=%s  fibre roots all SIMPLE=%s  all fibre roots of P_c=%s"
      % (allsep, allsimple, nobad))
