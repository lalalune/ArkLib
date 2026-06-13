# Independent audit: the δ* pin chain (submission-safety pass) — 2026-06-13

Author: NubsCarson (census/verifier seat). Method: 10-agent adversarial pass (Opus 4.8) —
map the chain, audit each headline claim independently (axiom-clean / non-vacuous /
params-match / honest-conditional), then synthesize with a live kernel re-check against the
Jun-13 sibling-tree oleans and a submission red-team.

# Audit: delta* pin chain submission-safety (ArkLib ProximityGap, issue #389)

**Date:** 2026-06-13  **Auditor:** independent adversarial pass (live kernel + independent recomputation)  **Worktree:** /home/nubs/Git/ArkLib-232 (sources byte-identical to /home/nubs/Git/ArkLib, diff -q clean)

## Verdict

The delta* pin chain is SOUND and submission-safe **as a reduction**, NOT as a prize solution. Unconditional pins are genuinely proven, axiom-clean, and non-vacuous; the production-value pin is genuinely conditional on the never-discharged `CensusDomination` Prop and is honestly marked as such in-tree.

## Verification method (gap closed)

Every per-claim auditor disclosed they could not run `#print axioms` live ("no oleans in either tree"). This was false for the chain: `/home/nubs/Git/ArkLib/.lake` has 677 ProximityGap oleans (built Jun 13) + 8840 Mathlib oleans, and chain sources are byte-identical between trees. I therefore ran LIVE `lake env lean` axiom checks (taskset -c 5 nice -n 19 ionice -c3, one at a time, no full build).

### Live axiom-check results (all = `[propext, Classical.choice, Quot.sound]`, zero sorryAx/native_decide/ofReduceBool)

| Theorem | File:loc |
|---|---|
| kkh26_epsMCA_lower_bound, kkh26_mcaDeltaStar_le | KKH26WitnessSpread.lean:126 |
| mcaDeltaStar_eq_of_good_below_of_bad_above | MCAExactPin.lean |
| kkh26_deltaStar_pin_of_interior_ceiling | KKH26DeltaStarReduction.lean |
| rs_mcaDeltaStar_bracket | MCADeltaStarBracket.lean:47 |
| mcaDeltaStar_rs_F5_eq_quarter | MCADeltaStarExactPoint.lean |
| interiorCeiling_of_censusDomination, kkh26_deltaStar_pin_of_censusDomination, evalCode_eq_rsCode | CensusDominationWeld.lean:80,143,45 (built from source vs oleans) |
| badScalars_card_le_alignable, alignableSets_card_le_choose | UniversalAlignmentLaw.lean:284,351 |
| all 7 incl. kkh26_dimOne_deltaStar_pin, deltaStar_pin_F12289 | KKH26DimOnePin.lean:363,425 |

The KKH26DimOnePin run was scanned in full: 7/7 declarations report the exact triple, no `sorryAx`/`native_decide`/`ofReduceBool` (the `decide` calls are pure kernel decide).

## Foundation (faithful, not degenerate)

- `mcaEvent` (Errors.lean:216-219): genuine ∃ over witness sets with line=codeword AND non-joint-agreement clauses — faithful ABF26 Def 4.3.
- `epsMCA` (Errors.lean:231-233): genuine iSup over word-stacks of Pr over gamma.
- `mcaDeltaStar` (MCAThresholdLedger.lean:86): sSup of good radii — the genuine threshold.

## Independent recomputation (not trusting decide / per-claim reports)

- **F12289 (dim-1):** 12289 prime; ord(4043)=8=2^3 exactly (4043^4=12288=-1, 4043^8=1, 4043^2=1479≠1); pin=3/4; window Johnson 0.6464 < 3/4 < capacity 0.875; beyond-Johnson (2/8)^2=0.0625 < rate 0.125; dim-1 band [14,24) nonempty. `interiorCeiling_dimOne` (KKH26DimOnePin.lean:261) has NO Prop hypothesis — genuinely unconditional, discharged by the real incidence theorem `dimOne_badScalars_card_mul_four_le` (line 100).
- **F5 (toy threshold):** exhaustive 5^8 search reproduces epsMCA = 1/5 for delta<1/4 and 4/5 at delta=1/4; with eps*=2/5 strictly between, delta*=1/4, sup not attained. Genuine `mcaDeltaStar` threshold pin (not list size).
- **CensusDomination non-vacuity:** appears ONLY in CensusDominationWeld.lean (grep -rln over all .lean) — never discharged. Satisfiable for large K via `alignableSets_card_le_choose` (≤ n.choose a) — not vacuously false.
- **Supply probe (PINBAND-SUPPLY-PROBE.md) reproduced exactly:** at m≥2 the EsymmFiber coset supply refutes CensusDomination (n=2048,m=2: band a=1032=8·129, d=8, C(256,129)=2^251.7); at m=1 (FFT/FRI domains) it is blocked by the divisor-floor off-by-one (log2 reach ≤ 2 across μ=10..12). EsymmFiber.lean has 0 references to Aligned/CensusDomination/deltaStar — pure supply combinatorics, consistent.

## Two-tier safety map

**SAFE to claim as PROVEN (unconditional, axiom-clean, non-vacuous):**
- dim-1 pin delta*=1-2/2^mu (3/4 at p=12289) — only unconditional result strictly inside the prize window; honest caveat: dimension-one constants only.
- F5 threshold pin delta*=1/4 at eps*=2/5 — TOY (n=4, not 2^-128).
- rs two-sided bracket delta ≤ delta* ≤ 1-(k+1)/n at eps*=1/2^128.
- F17/KKH26 epsMCA upper brackets.

**SAFE only as "reduced to one open Prop" (NEVER as "pinned"):**
- delta*=1-r/2^mu via kkh26_deltaStar_pin_of_censusDomination — conditional on the open CensusDomination; production regime (m=1, eps*=2^-128) needs a non-coset supply bound that does not exist.

## Issues

1. **OVERSELL (isolated, fix before any external cite):** DeltaStarConcretePinF17.lean:13-19,245,255 names a list-size bracket `delta_star_two_sided_pin` and says it "pins the threshold delta* two-sidedly," but proves `5 ≤ |Lambda| ≤ 120` at one radius. True + axiom-clean + isolated (Mathlib-only imports, nothing in chain imports it), and F5 already flags it as a different quantity. Fix: rename to `list_size_two_sided_bracket_at_interior_radius`; soften docstring.
2. **DISCLOSURE (resolved):** the "no oleans, cannot run axiom check" disclaimer in the per-claim reports is false for the chain; live runs are now on record.
3. **LINT (cosmetic):** CensusDominationWeld.lean:81 unused variable `hmu`.

## Red-team (submission)

Most embarrassing finding if sent as "prize fixed": the only unconditional exact pins are an n=4 toy (eps*=2/5) and a dimension-one (k=1) pin — the prize is k≥2 at eps*=2^-128. The production-value pin is conditional on CensusDomination, which the project's own only landed supply construction REFUTES at m≥2 and cannot reach at m=1. Honest framing in-tree neutralizes this; a careless cover letter saying "we pinned delta*" would not.

## Conclusion

Chain sound, conditional claim honestly marked, foundation faithful, residual non-vacuous and not refuted at m=1. No sorry/admit/native_decide/fabricated axiom anywhere in the chain (live-verified). Ship as a reduction with honest scope; tidy the F17 wording.