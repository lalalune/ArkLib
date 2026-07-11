"""
[N3] The moment/energy method is NOT provably dead — the DC escape.  (#407)

Question (candidate impossibility): is there a theorem that NO moment/energy proof can
establish the prize floor M <= C*sqrt(n log q), because the required deep moments inflate?

Answer: NO. The inflation is ENTIRELY the DC (b=0) term.  This probe quantifies, at the prize
parameters, the two facts the Lean brick _N3MomentNotDeadDCEscape.lean proves axiom-clean:

  (A) FULL energy E_r <= (2r-1)!! n^r is FALSE at deep r: the b=0 term forces E_r >= n^{2r}/q,
      which exceeds Wick (2r-1)!! n^r once n^r > q*(2r-1)!!.  Crossover ~ r=5..6 at n=2^30.

  (B) REDUCED (DC-subtracted) energy at r ~ ln q gives, IF DCEnergyBound (= A_r<=Wick, the open
      BGK input, measured-true) holds:   M^2 <= 2e*n*r << n^2.   So a moment/energy proof on the
      reduced energy reaches BELOW the trivial bound n.  The route is ALIVE; residual = BGK only.

Prize regime: n = 2^30 (smooth mu_n, proper 2-power subgroup), q ~ n * 2^128 (beta~4-5), eps*=2^-128.
"""
import math

n = 2**30
q = n * 2**128          # q >= n*2^128 so that eps*|F| >= ~n (prize existence gate)
ln_q = math.log(q)

def logwick(r):
    s = 0.0; k = 1
    while k <= 2*r - 1:
        s += math.log(k); k += 2
    return s + r*math.log(n)

def logDC(r):
    return 2*r*math.log(n) - math.log(q)      # log(n^{2r}/q)

print(f"n = 2^30 = {n}, q ~ n*2^128, ln q = {ln_q:.2f}\n")
print("(A) FULL-energy bound E_r<=Wick: DC floor n^{2r}/q vs Wick (2r-1)!! n^r")
print(f"{'r':>4} {'log(n^2r/q)':>14} {'log Wick':>12}  full-energy bound")
for r in [1, 2, 4, 5, 6, 8, 30, 89, 110]:
    a, b = logDC(r), logwick(r)
    print(f"{r:>4} {a:>14.2f} {b:>12.2f}  {'FALSE (DC>Wick)' if a > b else 'ok'}")

# locate exact crossover r* where DC first beats Wick
r = 1
while logDC(r) <= logwick(r):
    r += 1
print(f"\n  full-energy bound first FALSE at r* = {r}  (= where deep moments 'inflate').")

print("\n(B) REDUCED energy depth-optimized (Lean: eta_sq_le_dcOptimized), conditional on A_r<=Wick:")
r_opt = math.ceil(ln_q)
Msq = 2*math.e*n*r_opt
gap = 2*math.e*r_opt
print(f"  r = ceil(ln q) = {r_opt};  M^2 <= 2e*n*r = {Msq:.3e}")
print(f"  trivial bound n^2 = {n**2:.3e};  M^2/n^2 = {Msq/n**2:.3e}  (<< 1)")
print(f"  gap test 2e*r = {gap:.1f} < n = {n}  =>  M^2 < n^2 strictly (Lean: reduced_moment_bound_below_card)")
print(f"  M <= sqrt(2e*n*r) = {math.sqrt(Msq):.3e} = {math.sqrt(Msq)/math.sqrt(n):.1f}*sqrt(n)  (the prize floor shape)")

print("\nVERDICT [N3]: the candidate 'no moment/energy proof can work' is REFUTED.")
print("  Full-energy / single-depth methods ARE dead (DC inflation / spike).")
print("  Reduced-energy depth-optimized method is ALIVE: reaches M << n conditional on BGK.")
print("  => residual is genuinely BGK (A_r<=Wick), NOT a moment-method impossibility.")
