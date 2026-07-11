#!/usr/bin/env python3
"""
P5 — BGK / short-character-sum SOTA literature lever sweep (issue #407 / #444 prize).

QUESTION (the assigned mandate): does ANY result or combination of the newest BGK /
short-character-sum literature (Bourgain-Glibichuk-Konyagin, Bourgain-Garaev,
di Benedetto, Heath-Brown-Konyagin, Shkredov higher-energy, Murphy-Petridis, and the
2023-2026 follow-ups) cross the exponent wall  n^{0.989} -> n^{1/2}  at  beta = 4-5
for the THIN 2-power subgroup mu_n (n = 2^mu) that the prize requires?

VERDICT (verified by direct computation + literature WebFetch, 2026-06-17): NO.
This is a RIGOROUS NEGATIVE CLOSURE of the literature-lever angle: the entire known
pointwise-bound family stops at exponent ~1-31/2880 ~ 0.989, valid only for |H| > p^{1/4}-ish,
and goes VACUOUS at the upper prize end. The prize needs exponent 1/2 (sqrt cancellation).
The gap (>= 0.49 in the exponent) is the open Paley-Graph / Ramanujan content -- SPECTRAL,
not sum-product -- and NO 2023-2026 paper closes it for thin subgroups.

LITERATURE GROUND-TRUTH (fetched 2026-06-17):
 * di Benedetto et al, "New estimates for exponential sums over multiplicative subgroups
   and intervals in prime fields", J. Number Theory (2020), arXiv:2003.06165, Thm 3.1:
       max_{(a,p)=1} |sum_{x in H} e_p(ax)|  <~  H^{2689/2880} * p^{1/72}.
   With p = H^beta the H-exponent is  E(beta) = 2689/2880 + beta/72.  This is the SOTA
   pointwise power-saving for a general multiplicative subgroup (improves Bourgain-Garaev).
 * arXiv:2401.04756 (2024) "Exponential sums over small subgroups, revisited" is EXPOSITORY
   (re-proves BGK n^{1-o(1)}); it gives NO new exponent.
 * Harper, "Better than squareroot cancellation in number theory" (arXiv:2512.23681, 2025)
   is about AVERAGED/MOMENT cancellation in FAMILIES (Mobius in short intervals/APs), NOT a
   pointwise max-bound for a fixed thin subgroup -> does NOT apply to M(n) = max_b ||eta_b||.
 * Shkredov higher-energy / trinomial-energy (Cambridge CJM 2024-25): improve collinear-triple
   / additive-energy exponents for GENERIC subgroups, still energy/incidence based, subject to
   the SAME diagonal floors t2>=2, t3>=3 -> raise delta toward ~0.05-0.1 for generic sets,
   NEVER to 1/2; the 2-power subgroup ALREADY saturates the energy floor (E2=3n^2-3n, E3=15n^3),
   so there is no further room on the energy side (see probe_c3_dibenedetto_formula_audit.py).

This probe pins the EXACT beta-window of the di Benedetto SOTA -- sharper than the in-tree
_BGKSOTAInsufficiency.lean blanket "0.011 < 1/2" -- and confirms the Burgess-amplification
exponent is >= trivial at beta=4.
"""
from fractions import Fraction as F


def diB_H_exponent(beta):
    """di Benedetto Thm 3.1 H-exponent with p = H^beta:  2689/2880 + beta/72."""
    return F(2689, 2880) + F(beta) / 72


def burgess_exponent(beta, r):
    """Amplified Burgess: M <= C n^{1-1/r} p^{(r+1)/(4r^2)}; exponent on n with p=n^beta."""
    return (1 - F(1, r)) + F(beta) * F(r + 1, 4 * r * r)


print("=" * 78)
print("P5 BGK-SOTA literature lever sweep — does anything cross n^0.989 -> n^0.5 ?")
print("=" * 78)

print("\n[1] di Benedetto Thm 3.1 H-exponent E(beta) = 2689/2880 + beta/72")
print("    (the SOTA pointwise power-saving for a multiplicative subgroup)")
print(f"    {'beta':>6} | {'H-exponent':>12} | {'saving 1-E':>11} | status")
print("    " + "-" * 56)
prize_betas = [F(2), F(3), F(7, 2), F(15, 4), F(4), F(17, 4), F(9, 2), F(19, 4), F(5)]
for beta in prize_betas:
    E = diB_H_exponent(beta)
    s = 1 - E
    status = "NONTRIVIAL" if s > 0 else "VACUOUS (>= trivial H^1)"
    tag = "  <-- PRIZE" if beta in (F(4), F(5)) else ""
    print(f"    {float(beta):>6.3f} | {float(E):>12.6f} | {float(s):>+11.6f} | {status}{tag}")

# exact vacuity cutoff: 2689/2880 + beta/72 = 1  =>  beta = 72*(191/2880) = 191/40
beta_cut = F(72) * (1 - F(2689, 2880))
print(f"\n    => di Benedetto SOTA goes VACUOUS (saving<=0) at beta >= {beta_cut} = {float(beta_cut):.4f}")
print(f"       Prize regime beta in [4,5] STRADDLES this cutoff:")
print(f"         beta=4   : saving = {float(1-diB_H_exponent(4)):+.6f}  (tiny but nontrivial)")
print(f"         beta=4.775: saving = 0          (the cliff)")
print(f"         beta=5   : saving = {float(1-diB_H_exponent(5)):+.6f}  (VACUOUS: worse than trivial)")

print("\n[2] Burgess amplification min-exponent at beta=4 (optimize over depth r):")
for beta in [F(2), F(3), F(4), F(5)]:
    best = min((burgess_exponent(beta, r), r) for r in range(1, 2000))
    e, r = best
    status = "below trivial" if e < 1 else ">= TRIVIAL (no saving)"
    print(f"    beta={float(beta):.1f}: min n-exponent = {float(e):.6f} at r={r}  ({status})")
print("    => At beta=4 Burgess is >= trivial: pure Weil/Burgess is VACUOUS for the prize.")

print("\n[3] The prize requirement vs the best SOTA (the wall, exact):")
prize_exp = F(1, 2)
print(f"    prize needs H-exponent = 1/2 = {float(prize_exp)} (sqrt cancellation up to sqrt-log)")
print(f"    best SOTA at beta=4     = {float(diB_H_exponent(4)):.6f}")
gap = diB_H_exponent(4) - prize_exp
print(f"    EXPONENT GAP at beta=4  = {float(gap):.6f}  (~0.49 — vastly short)")
print(f"    saving needed  = 1/2 = {float(prize_exp):.4f}")
print(f"    saving SOTA    = {float(1-diB_H_exponent(4)):.4f}")
print(f"    ratio (needed/SOTA) = {float(prize_exp/(1-diB_H_exponent(4))):.1f}x short at beta=4")

print("\n[4] VERDICT: reduces-to-bgk. NO literature lever crosses the wall for thin mu_n.")
print("    The 0.989 -> 0.5 gap is the open Paley-Graph-Conjecture / Ramanujan content,")
print("    a SPECTRAL (eigenvalue) statement, not reachable by any fixed-fold sum-product /")
print("    energy / Burgess amplification. The 2-power subgroup saturates the energy floor")
print("    (no Shkredov-type room left), the 2024 'revisited' paper is expository, and the")
print("    2025 'better-than-sqrt' result is averaged/moment (does NOT give a pointwise M-bound).")
print("    Negative closure of the P5 literature-lever angle. Open core = unchanged BGK wall.")
