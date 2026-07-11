"""
Pin the units in the delta* formula. Kambire: eta = 2/s, and at threshold the count a = (1/2rho)^{rho s}
hits q*eps*. Solve consistently.

a = q*eps*:  (1/2rho)^{rho s} = q*eps*
Take log base 2:  rho*s*log2(1/2rho) = log2(q*eps*)
=> s = log2(q*eps*) / (rho * log2(1/2rho))
=> eta = 2/s = 2*rho*log2(1/2rho)/log2(q*eps*).

So the CORRECT formula (purely log2) is:
   delta* = 1 - rho - 2*rho*log2(1/2rho)/log2(q*eps*).
The directive wrote 2*rho*LN(1/2rho)/log2(q*eps*) -- using ln in num.
ln(x) = log2(x)*ln2, so directive_eta = log2-formula_eta * ln2 = log2-formula_eta * 0.6931.
=> the directive formula UNDERSTATES eta by factor ln2 => OVERSTATES delta* by (1-ln2)*2rho*log2(..)/log2(qeps).
Check which one matches Kambire's actual eta=2/s exactly.
"""
import math
for rho in [0.25,0.125]:
    for L in [128,256]:  # log2(q eps)
        s = L/(rho*math.log2(1/(2*rho)))   # log2-consistent threshold
        eta_kambire = 2/s
        eta_log2formula = 2*rho*math.log2(1/(2*rho))/L
        eta_directive_ln = 2*rho*math.log(1/(2*rho))/L
        print(f"rho={rho} L={L}: s={s:.2f}  eta(2/s)={eta_kambire:.6f}  "
              f"eta(log2 form)={eta_log2formula:.6f} [match={abs(eta_kambire-eta_log2formula)<1e-12}]  "
              f"eta(directive ln)={eta_directive_ln:.6f}  ratio ln/log2={eta_directive_ln/eta_log2formula:.4f}")
print()
print("VERDICT: the SELF-CONSISTENT delta* uses log2 in BOTH places:")
print("  delta* = 1 - rho - 2*rho*log2(1/2rho)/log2(q*eps*)   [= Kambire's 1-rho-2/s exactly]")
print("The directive's 'ln' in the numerator is a units slip (off by ln2=0.693 in eta);")
print("it makes delta* slightly LARGER than Kambire's true edge. Magnitude: ~(1-ln2)*eta ~ 0.0012 at L=128,rho=1/4.")
