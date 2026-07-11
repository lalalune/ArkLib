#!/usr/bin/env python3
"""
wf407_T01-norm_parseval_route.py  (#407 T01-norm, proof-structure pin)

Goal: identify the EXACT elementary chain proving the Landau ceiling
   |N(alpha)| = |Res(Phi_n, g_S)| = prod_{omega prim} |g_S(omega)|  <=  (#S)^{phi(n)/2}.

Candidate chain (geometric-mean <= quadratic-mean over the phi conjugates):
   (prod_omega |g(omega)|^2)^{1/phi}  <=  (1/phi) sum_omega |g(omega)|^2        [AM-GM]
   sum_{omega: Phi_n(omega)=0} |g(omega)|^2  =  ??? vs  phi * ||g||_2^2 = phi * #S
If  sum_omega |g(omega)|^2  <=  phi * #S, then
   |N|^2 = prod |g(omega)|^2 <= ((1/phi) sum |g|^2)^phi <= (#S)^phi,  i.e. |N| <= (#S)^{phi/2}.  QED-shape.

So the SINGLE arithmetic fact to verify is:
   sum_{omega primitive n-th root} |g_S(omega)|^2  <=  phi(n) * #S,
with EQUALITY exactly when ... ?  (For 0/1 g_S with exponents in [0,n), the full-root
sum sum_{all n-th roots} |g(omega)|^2 = n*#S by Parseval/orthogonality; the primitive
subset is <= that, and we compare to phi*#S.)

This probe verifies sum_{prim} |g(omega)|^2 vs phi*#S EXACTLY (exhaustive small n),
and also the FULL-root Parseval sum_{all roots} |g(omega)|^2 = n*#S (clean identity).
"""
import math, cmath, itertools
from sympy import cyclotomic_poly, Poly, symbols, totient, Integer, resultant

X = symbols('X')

def g_eval_sq_sum_primitive(n, S):
    """sum over primitive n-th roots omega of |g_S(omega)|^2 (numeric)."""
    tot = 0.0
    for c in range(1, n, 2):  # primitive = odd c for n a 2-power
        z = sum(cmath.exp(2j*math.pi*c*i/n) for i in S)
        tot += abs(z)**2
    return tot

def g_eval_sq_sum_all(n, S):
    """sum over ALL n-th roots of |g_S|^2 (Parseval => n*#S for distinct exps in [0,n))."""
    tot = 0.0
    for c in range(n):
        z = sum(cmath.exp(2j*math.pi*c*i/n) for i in S)
        tot += abs(z)**2
    return tot

print("="*80)
print("wf407 T01-norm  PARSEVAL ROUTE for the Landau ceiling")
print("="*80)

print("\n[1] FULL-root Parseval:  sum_{all n-th roots} |g_S(omega)|^2  =  n*#S  ?")
for n in (8, 16, 32):
    ok = True
    for _ in range(50):
        import random; random.seed(_)
        s = random.randint(1, n)
        S = sorted(random.sample(range(n), s))
        val = g_eval_sq_sum_all(n, S)
        ok = ok and abs(val - n*len(S)) < 1e-6
    print(f"  n={n:3d}: sum_all |g|^2 = n*#S on 50 random S?  {ok}")

print("\n[2] PRIMITIVE-root sum:  sum_{prim} |g_S(omega)|^2  <=  phi(n)*#S  ?  (the AM-GM input)")
print(f"  {'n':>4} {'max ratio (sum_prim)/(phi*#S)':>30} {'<=1 always?':>12}")
for n in (8, 16):
    phi = int(totient(n)); worst = 0.0; ok = True
    for mask in range(1, 1 << n):
        S = [i for i in range(n) if (mask>>i)&1]
        sp = g_eval_sq_sum_primitive(n, S)
        ratio = sp / (phi*len(S))
        worst = max(worst, ratio)
        if ratio > 1 + 1e-9: ok = False
    print(f"  {n:>4} {worst:>30.6f} {str(ok):>12}")
print("  --> if sum_prim |g|^2 <= phi*#S EXHAUSTIVELY, the Landau ceiling")
print("      |N| <= (#S)^{phi/2} follows by AM-GM (geo-mean <= arith-mean of |g(omega)|^2).")

print("\n[3] verify the assembled bound exactly: |N|^2 <= (sum_prim|g|^2 / phi)^phi <= (#S)^phi")
for (n, S) in [(16, [0,1,2,3,4]), (32, list(range(7))), (16,[0,1,3,7,11,15])]:
    phi = int(totient(n))
    Nx = cyclotomic_norm = Integer(resultant(Poly(cyclotomic_poly(n,X),X,domain='ZZ'),
                                              Poly(sum(X**i for i in S),X,domain='ZZ')))
    sp = g_eval_sq_sum_primitive(n, S)
    amgm_ceiling = (sp/phi)**(phi)          # >= |N|^2
    landau_ceiling = (len(S))**(phi)        # >= amgm_ceiling >= |N|^2
    N2 = float(int(Nx))**2
    print(f"  n={n} S={S}: |N|^2=2^{math.log2(max(N2,1)):.2f} "
          f"<= AMGM=2^{math.log2(amgm_ceiling):.2f} <= Landau (#S)^phi=2^{math.log2(landau_ceiling):.2f}  "
          f"chain_ok={N2 <= amgm_ceiling+1 <= landau_ceiling+1}")
print("\nDONE.")
