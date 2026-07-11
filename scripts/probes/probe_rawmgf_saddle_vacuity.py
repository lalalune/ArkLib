#!/usr/bin/env python3
"""
Probe: is the RAW even-moment MGF saddle hypothesis vacuous at the prize?

The in-tree cosh-MGF saddle consumer (period_le_saddle_closedForm / period_le_of_mgfBound, and my
prizeFloor_of_saddle built on them) takes the hypothesis

    RawMGF(y*) := sum_r  q * E_r(G) / (2r)!  *  y*^{2r}   <=   q * exp(n y*^2 / 2)

with y*^2 = 2 log q / n (so the RHS = q*exp(log q) = q^2).

But by the cosh-MGF identity, RawMGF(y) = sum_{b in F} cosh(eta_b * y) (q terms), which INCLUDES the
b=0 / DC term eta_0 = |G| = n. So RawMGF(y*) >= cosh(n * y*). With n*y* = sqrt(2 n log q), the DC term
alone is exp(sqrt(2 n log q))/2 -- which EXCEEDS q^2 = exp(2 log q) exactly when sqrt(2 n log q) > 2 log q,
i.e. n > 2 log q. In the prize regime n >> log q, so the RAW hypothesis is FALSE (the conditional is
vacuous). Only the DC-SUBTRACTED form A_r = E_r - n^{2r}/q is the non-vacuous open target (issue #444 §8,
DCEnergyEssential.lean). This probe makes that quantitative across the prize regime.

NOTE: this is a structural/vacuity check on the HYPOTHESIS shape (log-scale exact for the DC term), not a
numeric evaluation of M -- so it is NOT the thinness-invariant moment face being re-probed; it characterizes
which saddle-hypothesis form is live.
"""
import math

print(f"{'a':>3} {'beta':>4} {'n':>11} {'q':>6} {'n*y* = sqrt(2n log q)':>22} "
      f"{'log DC = n y* - log2':>20} {'log(q^2) = 2 log q':>18} {'RAW hyp FALSE?':>14}")
any_false = False
for a in [4, 6, 8, 10, 16, 24, 30]:
    n = 2 ** a
    for beta in [4, 5]:
        q = n ** beta
        lq = math.log(q)
        ystar = math.sqrt(2 * lq / n)
        nystar = n * ystar                # = sqrt(2 n log q)
        log_dc = nystar - math.log(2)     # log cosh(n y*) ~ n y* - log 2 for large argument
        log_q2 = 2 * lq
        raw_false = log_dc > log_q2       # DC term alone exceeds the saddle RHS q^2 => hypothesis false
        any_false = any_false or raw_false
        print(f"{a:>3} {beta:>4} {n:>11} {'n^'+str(beta):>6} {nystar:>22.3f} "
              f"{log_dc:>20.3f} {log_q2:>18.3f} {str(raw_false):>14}")

print()
print("VERDICT: the RAW even-moment MGF saddle hypothesis (b=0 DC term included) is FALSE for all")
print(f"         prize-regime n (n > 2 log q):  any_false = {any_false}")
print("CONSEQUENCE: prizeFloor_of_saddle / period_le_saddle_closedForm are true conditionals on a")
print("VACUOUS premise at the prize; the LIVE non-vacuous open target is the DC-SUBTRACTED A_r = E_r")
print("- n^{2r}/q (issue #444 §8 / DCEnergyEssential). The bridge welds the encodings correctly, but")
print("the open hypothesis must be the DC-subtracted MGF, not the raw E_r MGF.")
