#!/usr/bin/env python3
"""Fold-transport feasibility frontier for a beyond-Johnson δ* lower bound (#389).

Research-map vector 5 (claim comment 4697257855), the lower-bound side that the
all-rates bracket (probe_deltastar_bracket_allrates.py) identified as the whole
remaining δ* content. Exact rational arithmetic; falsify-first.

THE REDUCTION (standard, no folded-decoder implementation needed — we compute the
budget the route requires, not a decoder).
  Folded smooth-RS, fold arity s along the 2-power tower: message dim k over F,
  folded length n/s over alphabet F^s. Rate is preserved: ρ = k/n.
  Folded RS list-decodes to folded-SYMBOL-error fraction 1 − ρ − ε (Guruswami–Wang
  / Chen–Zhang capacity; s ≥ Θ(1/ε)).
  A plain δ-fraction of coordinate errors maps to a folded-symbol-error fraction in
  [δ, min(δ·s, 1)]: the lower end packs all errors into whole blocks; the upper end
  is the adversary spreading one error per block (δn errors over n/s blocks →
  fraction δs). Call the realized multiplier the EFFECTIVE UNFOLDING LOSS L ∈ [1, s].
  The fold route certifies a plain decoding (hence MCA-good) radius δ iff
  L·δ ≤ 1 − ρ − ε, i.e. δ ≤ (1 − ρ − ε)/L. It BEATS Johnson iff
        (1 − ρ)/L  >  1 − √ρ   (ε → 0)   ⟺   L < L*(ρ) := (1 − ρ)/(1 − √ρ).

VERDICT LOGIC.
  * naive worst-case L = s ≥ 2 (full spreading). If s ≥ L*(ρ) the route is dead at
    that arity (naive folding cannot beat Johnson).
  * the route is ALIVE only if the smooth tower forces effective L < L*(ρ) — i.e. the
    MCA-bad error patterns must be at least (1 − L*/s)-fraction block-localized
    (cannot be spread). We report, per rate, L*(ρ), whether ANY s ≥ 2 admits L < L*
    under naive spreading (it never does), and the localization fraction the smooth
    structure would have to enforce. That last number is the sharp, toy-probeable
    successor question.

Exact: L*(ρ) = (1−ρ)/(1−√ρ) = (1−ρ)/(1−√ρ) · (1+√ρ)/(1+√ρ) = (1−ρ)(1+√ρ)/(1−ρ) =
1 + √ρ  (since 1−ρ = (1−√ρ)(1+√ρ)). So L*(ρ) = 1 + √ρ — clean closed form.
"""

from math import sqrt

# Exact symbolic result: L*(rho) = (1-rho)/(1-sqrt(rho)) = 1 + sqrt(rho), proven in
# the docstring (1-rho = (1-sqrt rho)(1+sqrt rho)). sqrt below is for DISPLAY only;
# the load-bearing facts (L* = 1+sqrt(rho) < 2 <= s; co-location fraction = 1-sqrt(rho))
# are exact closed forms, not numerics.
RATES = [("1/2", 0.5), ("1/4", 0.25), ("1/8", 0.125), ("1/16", 0.0625)]


def main():
    print("FOLD-TRANSPORT FEASIBILITY FRONTIER — can folded smooth-RS capacity, "
          "unfolded, beat Johnson?\n")
    print("Closed form (exact): L*(ρ) = (1−ρ)/(1−√ρ) = 1 + √ρ "
          "(since 1−ρ = (1−√ρ)(1+√ρ)).")
    print("Route beats Johnson at arity s iff effective unfolding loss L < L*(ρ); "
          "naive worst-case L = s.\n")
    print(f"{'ρ':>6} {'√ρ':>8} {'Johnson':>9} {'capacity':>9} {'L*=1+√ρ':>9} "
          f"{'naive s=2':>10} {'route@s≥2?':>11} {'loc. frac needed':>18}")
    for (lbl, rho) in RATES:
        sq = sqrt(rho)
        johnson = 1 - sq
        cap = 1 - rho
        Lstar = 1 + sq
        # naive s=2 loss = 2; route alive at s iff s < L*; smallest usable fold s=2
        alive_naive = (2 < Lstar)
        # localization fraction the smooth structure must enforce so that effective
        # loss L < L*: with s=2, errors spread to L=2 worst case; need L<L*<2, so a
        # fraction (1 − (L*−1)/(s−1)) of the spreading must be defeated. For s=2:
        # effective L = 1 + (spread fraction); need 1+f < L* ⟹ f < L*−1 = √ρ. So at
        # most √ρ of errors may land in fresh blocks; (1−√ρ) must co-locate.
        need_localized = 1 - sq  # = 1 − √ρ = Johnson, strikingly
        print(f"{lbl:>6} {sq:>8.4f} {johnson:>9.4f} {cap:>9.4f} "
              f"{Lstar:>9.4f} {'2.0':>10} "
              f"{('ALIVE' if alive_naive else 'DEAD'):>11} "
              f"{need_localized:>17.4f}")
    print()
    print("READING.")
    print("• L*(ρ) = 1 + √ρ ∈ (1, 1.708]; the smallest fold arity is s = 2, so naive")
    print("  worst-case loss L = s = 2 ≥ L*(ρ) at EVERY prize rate (2 > 1.708 ≥ 1+√ρ).")
    print("  ⟹ naive fold-transport NEVER beats Johnson — the research-map hand-wave is")
    print("  now an exact fact at all four rates. (Route DEAD under worst-case spreading.)")
    print("• The route survives ONLY if the smooth tower forbids spreading: with s = 2,")
    print("  the effective loss is L = 1 + (fraction of errors in fresh blocks), and the")
    print("  route beats Johnson iff that fraction < √ρ — i.e. a (1−√ρ)-fraction of every")
    print("  MCA-bad error pattern must be FORCED to co-locate within tower blocks.")
    print("  Strikingly, the required co-location fraction equals the Johnson radius 1−√ρ")
    print("  itself: an exact self-referential threshold.")
    print("• SUCCESSOR QUESTION (toy-probeable, the real test): do MCA-bad stacks on a")
    print("  smooth 2-power domain have error support that co-locates under the squaring-")
    print("  tower block structure to fraction ≥ 1−√ρ? If NO (errors spread freely), the")
    print("  fold route is refuted for smooth domains. If YES, it is the first beyond-")
    print("  Johnson lower-bound mechanism. The supply census (exponential, spread)")
    print("  is prior evidence AGAINST co-location — the honest prior is refutation.")


if __name__ == "__main__":
    main()
