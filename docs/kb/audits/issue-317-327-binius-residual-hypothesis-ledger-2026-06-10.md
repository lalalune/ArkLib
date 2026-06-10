# Issues #317/#327 — Binius BinaryBasefold residual discharge: audit + hypothesis ledger (2026-06-10)

Goal-session ledger for the two open Binius issues: #327 (BinaryBasefold convention repair +
final-sumcheck completeness) and #317 (discharge the residual `Prop` typeclasses). This page
records (a) the full residual census with classification, (b) the literature anchoring, (c) the
hypothesis exercise over the genuinely open/uncertain mathematics, with explicit
constraint/novelty/prior-art reasoning per hypothesis, and (d) unification/DRY observations.

Baseline commit: `a075a1b66` (main). `lake build
ArkLib.ProofSystem.Binius.BinaryBasefold.ReductionLogic` green at baseline.

## A. Residual census and classification

Audit method: one reader-agent per residual (statement + every referenced definition chased +
consumer map + degeneracy check), cross-checked in the orchestrator loop. Classifications:

| # | Residual | Site | Classification | Core gap |
|---|---|---|---|---|
| 1 | `FinalSumcheckStepLogicCompleteResidual` | ReductionLogic.lean:1694 | provable as stated (#327) | one weld: `iterated_fold (getLastOracle) (final ϑ block) = const (t(challenges))` via FinalOracleBridge → `iterated_fold_transitivity` → `getFoldingChallenges_append_finalBlock` → `getMidCodewords_last_apply_eq_eval`; then `IsStronglyComplete` assembly along the retained skeleton |
| 2 | `Prop4212Case1Residual` | Soundness/Incremental.lean:230 | provable as stated (post per-fiber migration) | one new brick (`qMap_total_fiber_succ_peel_first`, bottom/LSB fiber peel) + per-y affine SZ + union bound; probability layer (`Pr_le_Pr_of_implies`, `prob_uniform_eq_card_filter_div_card`) exists |
| 3 | `Prop4212Case2Residual` | Soundness/Incremental.lean:1852 | weld-distance | all 5 chain deps proven incl. the full DG25 layer; remaining: residual #4 + the `s = 0` boundary of the close→affine-line bridge |
| 4 | `PreTensorCombineJointProximityResidual` | Soundness/Incremental.lean:1659 | provable (medium) | Lemma 4.22 fiber-projection distance counting: `Δ₀(⋈\|preTensor f, ⋈\|preTensor g) ≤ Δ₀(f,g)`-shaped bound through the fiber re-indexing |
| 5 | `Prop421Case1FiberwiseCloseResidual` | Soundness/Proposition4_21.lean:68 | provable as stated (medium) | ONE new lemma: tensor bit-order bridge `(challengeTensorProduct n r).get = challengeTensorExpansion n (r ∘ Fin.rev)`; then `single_point_localized_fold_matrix_form_eq_iterated_fold` + `foldMatrix_det_ne_zero` + `prob_schwartz_zippel_mv_polynomial` (all proven) |
| 6 | `Prop421Case2FiberwiseFarResidual` | Soundness/Proposition4_21.lean:440 | weld-distance | same DG25 chain as #3, telescoped over steps |
| 7 | `FoldPreservesBBFCodeMembershipResidual` | Code.lean:1039 | provable (medium, ~300–450 lines) | general-level-`i` novel-basis reconstruction: degree + triangularity of `intermediateNovelBasisX` (CompPoly has defs, no degree lemmas); level-0 template exists verbatim in CompPoly NovelPolynomialBasis.lean:1382–1545 |
| 8 | `PreviousSuffixFiberAlignmentResidual` | Soundness/QueryPhasePrelims.lean:571 | provable (easy) | complete old proof exists (QueryPhase.lean:317–395) against the outdated CompPoly `iteratedQuotientMap` signature; re-state + port |
| 9 | `ExtractMLPCorrectnessResidual` | Relations.lean:239 | provable (medium plumbing) | Berlekamp–Welch decoder soundness/completeness transported across the `sDomain` enumeration |

**Headline: none of the 9 is open mathematics.** Every statement is either DP24/Basefold
textbook content or pure mechanization debt. The two soundness-theory walls that COULD have been
open — fold-matrix nonsingularity and the affine proximity gap — are already discharged in-tree
(`FoldDetDischarge.lean`; `ArkLib/Data/CodingTheory/ProximityGap/DG25/` is sorry-free,
axiom-free, residual-free).

## B. Literature anchors

- **Basefold** (Zeilberger–Chen–Fisch, eprint 2023/1705): sumcheck/IOPP lockstep; final-round
  binding `enc₀(h_d(r)/eq̃_z(r)) = π_final` is exactly the shape of
  `finalSumcheckStepLogic.verifierCheck` (`target = eqTilde(eval_point, challenges) * c`). #327's
  residual is the completeness direction of this check — settled math.
- **DP24 / FRI-Binius** (Diamond–Posen, eprint 2024/504): §4 query-phase analysis. The
  formalized `foldingBadEvent` = Def 4.20; the incremental events = Def 4.20.2; the case split =
  Prop 4.21 (close/far); butterfly invertibility = Lemma 4.9/4.13 family. Case 1 = per-fiber
  Schwartz–Zippel + union bound; Case 2 = proximity-gap route.
- **DG25** (affine-line proximity gaps at unique decoding, formalized in
  `Data/CodingTheory/ProximityGap/DG25/`): Thm 2.2 (RS affine-line gap, ε = |S|) + Thm 3.1
  (lift to interleaved codes). This is the UDR-regime replacement for BCIKS20 correlated
  agreement, and it is fully proven in ArkLib — the heavyweight input to Case 2 is NOT open here.
- Known divergence (deliberate): the formalized `fiberwiseClose` is plain Hamming/UDR closeness
  at the source level; DP24's case split uses the *fiberwise* distance `d^{(i)}(f, C) <
  d_{i+ϑ}/2`. See hypotheses H-K1/H-A4.

## C. Hypothesis ledger

Per the goal-session protocol: each hypothesis gets constraints → prior-art/larp check → novelty
→ statement → prove-out disposition. "Known" hypotheses are within reach of current machinery;
"advanced" ones posit machinery the repo (and sometimes the literature) does not have.

### Known-direction hypotheses

**H-K1 (fiber–Hamming distance sandwich).**
*Constraints:* `fiberwiseDistance` in Code.lean is a literal `:= 0` stub; the honest object must
relate to Hamming distance for the existing UDR hypotheses to keep doing work. *Prior art:*
folklore in every FRI-style analysis (DP24 uses it silently); not in ArkLib, not in Mathlib.
*Larp check:* the inequality itself is certainly not new math; the contribution is purely the
mechanized object replacing a dishonest stub. *Novelty:* repo-honesty only. *Hypothesis:* define
`fiberwiseDistanceHonest i steps f g := (fiberwiseDisagreementSetPerFiber … f g).card`; then
`fiberwiseDistanceHonest ≤ Δ₀(f,g) ≤ 2^steps · fiberwiseDistanceHonest`, both tight.
*Prove-out:* Lean probe, wave-3.

**H-K2 (case-split exhaustiveness is preserved under the UDR-only surface).**
*Constraints:* DP24 splits on fiberwise distance; the formalization splits on `fiberwiseClose` =
UDR closeness. The composed soundness chain only consumes the two branch bounds through
`prop_4_21_bad_event_probability`'s dite on the SAME predicate, so the split is exhaustive *for
the formalized predicate* by construction. The faithfulness question is whether each branch's
PAPER argument still applies to its formalized branch hypothesis. *Prior art:* this is a
formalization-design question, no literature. *Larp check:* n/a. *Hypothesis:* Case 1's argument
needs only "a UDR codeword f̄ exists" (weaker than the paper's fiber-close), and Case 2's needs
only "f is UDR-far" — so the UDR-only split is sound and in fact *simpler* than the paper's; no
coverage is lost. *Prove-out:* established by the Case-1/Case-2 discharges themselves; recorded
here so nobody "repairs" the divergence backwards.

**H-K3 (`steps = 0` boundary).** *Constraints:* `fiberwiseClose` carries `[NeZero steps]` while
the Case-2 chain hits `ϑ-(k+1) = 0`; the blocked bridge
`fiberwiseClose_fold_implies_affineLineEval_close` is commented out for exactly this reason.
*Prior art:* none (convention question). *Hypothesis:* at `steps = 0` the right reading is plain
`UDRClose` at the destination (= source) level, and since `fiberwiseClose` is *definitionally*
UDR-closeness ignoring `steps`, dropping `[NeZero steps]` from `fiberwiseClose` is conservative:
every consumer stays well-typed and the `s = 0` boundary case of the bridge becomes the identity
statement. *Prove-out:* Lean probe (drop the instance argument, rebuild cone), wave-3.

**H-K4 (block-level Case 1 needs no product-measure Fubini).** *Constraints:* the block event is
over `r ←$ᵖ (Fin steps → L)`; a per-step telescoping would need a marginal decomposition of the
uniform PMF (machinery the repo lacks). *Prior art:* DP24 proves the block bound directly by
multivariate SZ on the tensor-dotted fold matrix — and ArkLib already has
`prob_schwartz_zippel_mv_polynomial`. *Larp check:* the audit located every brick; nothing new is
claimed. *Hypothesis:* the per-point drop event equals `{r : ctp(r) ⬝ (M_y *ᵥ v_diff) = 0}` with
`ctp(r) = challengeTensorExpansion (r ∘ Fin.rev)` a nonzero multilinear polynomial of total degree
≤ steps, so the direct route gives `steps·|S|/|L|` with zero Fubini. *Prove-out:* wave-2 lane
`prove:317-p421case1` (running).

**H-K5 (degenerate-set retirement).** *Constraints:* the degenerate legacy
`fiberwiseDisagreementSet` (`steps ≠ 0` branch ignores its quotient point) still has live uses in
8 files although both bad-event definitions migrated to the per-fiber set. *Hypothesis:* every
remaining live use is either (i) `steps = 0` (where legacy = `disagreementSet`, honest), or (ii)
upper-bound position where `PerFiber ⊆ legacy` (`fiberwiseDisagreementSetPerFiber_subset_legacy_of_ne_zero`)
suffices, so the legacy definition can be deleted or reduced to the `steps = 0` case with no
proof loss. *Prove-out:* mechanical sweep after Case-1 lands (it's the largest consumer).

### Advanced hypotheses

**H-A1 (bad-event chains as PMF martingale infrastructure).**
*Constraints:* the incremental decomposition `Pr[bad] ≤ Σ_k Pr[¬E(k) ∧ E(k+1)]` with the k-th
bound uniform over prefixes recurs in Binius (Def 4.20.2), FRI round-by-round soundness (#303),
STIR (#301) and WHIR (#302) — each formalization currently hand-rolls it. *Prior art / larp
check:* mathematically this is the trivial union/Doob decomposition; as reusable Lean
infrastructure over VCVio PMFs it does NOT exist in ArkLib or Mathlib (each proof re-derives it
in-place; checked `Data/Probability/Instances.lean` and the FRI/STIR soundness files). *Novelty:*
engineering-novel only; honest value = de-duplication across four proof systems. *Hypothesis:* a
single lemma `Pr_{v ←$ᵖ (Fin n → α)}[E_n(v)] ≤ Σ_k sup-over-prefix Pr_{x}[¬E_k ∧ E_{k+1}]`-shaped
(stated with explicit prefix conditioning, avoiding measure-theoretic sup via a uniform bound
hypothesis) suffices to derive ALL the repo's round-by-round folding bounds from their
single-round versions. *Prove-out:* scoped probe in wave-3; success metric = re-deriving the
block-level Case 1 from the incremental Case 1 in ≤ ~80 lines.

**H-A2 (constructive distance amplification from the determinant factorization).**
*Constraints:* `foldMatrixNat (n+1) ≅ fromBlocks (x₁•M₀) ((−x₀)•M₁) ((−1)•M₀) M₁` with
`det = ±(x₁−x₀)^{2^n}·det M₀·det M₁` is now proven (`FoldDetSplit.lean`). DG25's far-branch
argument decodes via `Classical.choose`. *Prior art / larp check:* FRI's distortion lemmas do an
analogous explicit analysis over multiplicative cosets (BBHR18 §4; BKS18); for *binary additive
NTT towers* an explicit blockwise-Vandermonde route to the UDR far-bound is not something the
audit or the literature agents found written down — but the CLAIM (far stays far w.h.p.) is of
course DP24's, so only the *proof route* could be novel, and its payoff is constructivity, not
strength. *Hypothesis:* from the block factorization, for any `w` with
`d(w, C^{(i)}) ≥ e`, the per-fiber affine system gives
`Pr_r[d(fold(w,r), C^{(i+1)}) < e/2 − |S^{(i+1)}|-slack] ≤ |S^{(i+1)}|/|L|` by direct counting,
no decoder. *Prove-out:* exploratory scratch probe; NOT load-bearing (DG25 already serves Case 2);
abandon on first wall.

**H-A3 (Johnson-radius affine gaps for BBF codes).** *Constraints:* DG25 layer is UDR-only;
beyond-UDR list-decoding gaps for RS are BCIKS20 (formalization open repo-wide — same wall as
#62/#232); the additive-NTT/binary-tower analogue is DP24 §3 (they adapt correlated agreement).
*Larp check:* this IS open formalization territory and partially open math (capacity-regime gaps
are open even for RS; see the #232 ledger — `mca_capacity_bound_CONJECTURE` refuted-in-literature
note). *Hypothesis (scoped honestly):* the DG25 interleaved-lift theorem statement-shape admits a
Johnson-radius generalization whose ONLY unproven input is the plain (non-interleaved) RS Johnson
gap; i.e. the lift is radius-agnostic. *Prove-out:* statement-level probe only (state the lift
with a radius parameter + hypothesis; check the existing proof is radius-generic). No claim on
the RS Johnson gap itself — that remains the known wall.

**H-A4 (fiber-entropy interpolation).** *Constraints:* H-K1's sandwich is loose at both ends;
DP24's fiberwise distance is the `t = steps` endpoint of a natural family. *Prior art / larp
check:* no such interpolating family in DP24/Basefold/FRI literature found by the agents; closest
is the "block-wise distance" of interleaved-code folklore (distinct: that groups coordinates of
the SAME level). *Novelty:* genuinely new framing, low risk of larp because scoped as a
definition + monotonicity chain. *Hypothesis:* define `d^{(t)}(f,g) :=` number of level-`(i+t)`
points whose `t`-step fiber contains a disagreement; then `d^{(t+1)} ≤ d^{(t)} ≤ 2·d^{(t+1)}`,
`d^{(0)} = Δ₀`, `d^{(steps)} = fiberwiseDistanceHonest`, and the fold contracts:
`d^{(t)}(fold(f,r), fold(g,r)) ≤ d^{(t+1)}(f,g)` for every `r` (deterministic!), with equality
except on the SZ-bounded bad set. The deterministic contraction is the structural heart of Case 1
and would replace the per-proof witness extraction with one reusable inequality chain.
*Prove-out:* wave-3 probe (definitions + the two monotonicity lemmas + the deterministic
contraction); promote to Code.lean as the honest `fiberwiseDistance` if green.

**H-A5 (quotient-tower ↔ incidence-laboratory cross-pollination).** *Constraints:* the qMap
tower is an 𝔽₂-affine quotient chain; #232's incidence laboratory (O129) measures locus-overlap
channels for proximity bounds. *Larp check:* no literature connects additive-NTT fiber towers to
the #232 window-law/incidence machinery; this is speculative interpolation between two in-repo
programs. *Novelty:* high; probability of payoff: low; the honest framing is a measurement, not
a theorem. *Hypothesis:* the level-`t` disagreement loci of `(f, f̄)` across the tower form an
incidence structure whose overlap statistics obey the O129 exactness bound, giving a second,
independent estimate of the Case-1 drop probability. *Prove-out:* NOT scheduled this session
(would dilute the issue-closing goal); recorded for the #232 program with a pointer back here.

## D. Unification / DRY observations

1. `fiberwiseClose`, `UDRClose` (and `pair_*` variants) are definitionally identical modulo
   unused arguments — consolidate after the residual discharges land (do not churn the surface
   mid-proof).
2. `fiberwiseDistance`/`pair_fiberwiseDistance` are `:= 0` stubs with (audit-confirmed) no
   load-bearing consumers — replace with H-K1/H-A4's honest definition or delete.
3. The tensor-order bridge (H-K4 brick 1) retires the long-standing
   `challengeTensorProduct` vs `challengeTensorExpansion` bit-reversal hazard documented at
   Prelude.lean:1919–1925 — afterwards exactly one evaluator family is needed at proof sites.
4. The legacy degenerate `fiberwiseDisagreementSet` (H-K5) and the dead
   `iteratedQuotientMap`-era extraction lemmas it forced are the last remnants of the
   pre-per-fiber API; deleting them shrinks the audit surface that made Prop4212Case1 look false.
5. The incremental (`4.2.12`) and block (`4.21`) developments will, after H-K4 and H-A1, share
   one SZ core (`ctp ⬝ w = 0` bound) — the duplicated butterfly-algebra blocks in
   Proposition4_21.lean and Incremental.lean collapse onto it.

## E. Session status pointers

- #327 final weld + assembly: scratch lane running (`/tmp/i327/`).
- #317 Case 1 incremental: scratch lane running (`/tmp/i317case1/`).
- #317 suffix-align, block Case 1, fold-preserves: sequential wave-2 lanes running.
- Case 2 / JointProximity / ExtractMLP: audits re-running; prove lanes follow.
- Issue threads carry the same maps: #327 comment 2026-06-10 (afternoon), #317 comment
  2026-06-10 (afternoon).
