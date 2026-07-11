import sympy
import math

# C35: di Benedetto n^{0.989} bound (proven for p^{1/4}<H<p^{1/2}) extends below p^{1/4}
# via "antipodal-only structure plug", giving a power-saving past Johnson.
#
# Two decisive facts to verify:
#  (1) The prize regime n in {2^30..2^43}, q ~ n*2^128, FORCES n < p^{1/4} strictly
#      => di Benedetto's stated domain (p^{1/4}<H<p^{1/2}) is genuinely MISSED.
#  (2) Even GRANTING di Benedetto exponent 1-31/2880 = 0.98924 below p^{1/4},
#      the resulting bound M <= n^{0.98924} is FAR above the floor target.
#      To pin delta* PAST Johnson the per-frequency sup-norm must reach the
#      Paley/Ramanujan floor ~ sqrt(n log(p/n)) = n^{1/2+o(1)}.
#      n^{0.989} vs n^{0.5}: an ENTIRE half-power short.
#
# (3) Crucially: does the "antipodal plug" change anything about the EXPONENT?
#     The antipodal structure (z+(-z)=0, the ONLY primitive vanishing relation among
#     2^mu-th roots, Mann/Conway-Jones) is a CHAR-0 closed combinatorial fact. The
#     route-elimination meta-theorem: every closed/p-independent/antipodal object caps
#     at Johnson. So an "antipodal plug" cannot supply the p-DEPENDENT cancellation
#     that di Benedetto's Stepanov machinery uses; it gives no exponent improvement.

dB_exp = 1 - sympy.Rational(31,2880)   # di Benedetto explicit power-saving exponent
print("di Benedetto exponent 1-31/2880 =", float(dB_exp), "  (31/2880 =", float(sympy.Rational(31,2880)),")")
print()

# (1) regime check: prize point grid n=2^mu, q ~ n * 2^128 (eps*=2^-128)
print("=== FACT 1: prize regime forces n < p^{1/4} (di Benedetto domain MISSED) ===")
for mu in [30, 32, 36, 40, 43]:
    n = 2**mu
    # q ~ n * 2^128 (the spec: budget q*eps* ~ n with eps*=2^-128)
    log2_q = mu + 128
    # beta = log_n q = log2 q / log2 n
    beta = log2_q / mu
    # n < p^{1/4} iff beta > 4 iff log2 n < log2 q /4
    log2_p_quarter = log2_q / 4.0
    inside_dB = (mu > log2_p_quarter)  # n > p^{1/4} would mean di Benedetto applies
    print(f"  mu={mu}: n=2^{mu}, q~2^{log2_q}, beta=log_n q={beta:.3f}, "
          f"p^(1/4)=2^{log2_p_quarter:.2f}, n>p^(1/4)? {inside_dB} "
          f"(di Benedetto {'APPLIES' if inside_dB else 'VACUOUS — n<p^(1/4)'})")
print()

# (2) granting the exponent, distance to the floor
print("=== FACT 2: even GRANTING dB exponent below p^{1/4}, it misses the floor by ~half a power ===")
for mu in [30, 40]:
    n = 2**mu
    log2_q = mu + 128
    M_dB = float(dB_exp) * mu                # log2 of n^{0.989}
    M_floor = 0.5*mu + 0.5*math.log2(log2_q - mu)   # log2 of sqrt(n log(p/n))
    M_trivial = mu                            # log2 of trivial n
    print(f"  mu={mu}: log2 M(dB)={M_dB:.2f}  vs  log2 M(floor ~sqrt(n log(p/n)))={M_floor:.2f}  "
          f"vs trivial log2 n={M_trivial}")
    print(f"          gap dB-above-floor = {M_dB - M_floor:.2f} bits "
          f"(= factor 2^{M_dB-M_floor:.1f}); savings below trivial = {M_trivial-M_dB:.3f} bits only")
print()

# (3) Johnson vs capacity in delta* language.
# Johnson radius 1-sqrt(rho). To pin delta* PAST Johnson, the worst-far-line incidence
# I(delta) must stay <= budget for delta in (1-sqrt(rho), 1-rho-Theta(1/log n)).
# Via the governing law I_pencil = N * S, the per-frequency sup-norm M controls this.
# The KEY arithmetic: a sup-norm bound M <= n^c translates to a delta* that beats
# Johnson ONLY IF c < 1/2 + o(1) (square-root cancellation). For c=0.989, the implied
# crossing is at/below Johnson (no past-Johnson gain). Demonstrate the exponent threshold:
print("=== FACT 3: past-Johnson requires sup-norm exponent c -> 1/2; dB c=0.989 yields NO past-Johnson gain ===")
print("  To reach the window interior (past Johnson) the cancellation must be n^{1/2+o(1)}.")
print("  di Benedetto c=0.989 is a 0.489-power short => stays in the n^{1-o(1)} BGK class (Johnson side).")
print(f"  Required: c<=0.5. Have: c={float(dB_exp):.4f}. Deficit = {float(dB_exp)-0.5:.4f} in exponent.")
