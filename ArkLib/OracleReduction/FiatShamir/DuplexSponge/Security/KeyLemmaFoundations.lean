/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents
import ArkLib.OracleReduction.Security.OracleDistribution

/-!
# Foundations bricks for the DSFS Key Lemma (CO25 Lemma 5.1)

This module lands the bounded foundations layer of the bricks decomposition for
`DuplexSpongeFS.KeyLemmaResidual` (CO25, Lemma 5.1): proven game/budget/numeric level
lemmas that the §5.8 hybrid argument consumes, the repaired *eager* statement surface, and
named `*Residual : Prop` interfaces for the remaining security-analysis obligations. Several
interfaces defined here are discharged downstream; they remain here so all consumers share one
stable statement surface.

## Proven bricks (no `sorry`, axiom-clean)

- `tvDist_chain4` (F2): four-step TV triangle chain for the `Hyb₀ … Hyb₄` ladder (§5.8).
- `ηStar_le_ηStarPaper` / `claimSum_le_ηStarPaper` (F1): the in-tree `ηStar` (denominator
  exponent `C+1`) is **stronger** than the paper bound `ηStarPaper` (exponent `C`, Eq. 5),
  and the three nonzero per-step claim bounds (Claims 5.21/5.22/5.24; Claim 5.23's step is
  exactly `0`) sum to at most `ηStarPaper`. Together these certify that the hybrid chain can
  only deliver the `C`-exponent bound — the `C+1` claim in `KeyLemma.ηStar` needs the
  one-token upstream fix before `KeyLemmaResidual` can be provable.
- `isQueryBoundP_simulateQ_stateT_optionT_of_step` /
  `isQueryBoundP_simulateQ_stateT2_optionT_of_step` (F3): predicate-targeted query-budget
  transfer through the §5.4 simulator monad stacks `StateT σ (OptionT (OracleComp _))` and
  `StateT σ₁ (StateT σ₂ (OptionT (OracleComp _)))` (VCVio has only the plain-`StateT` case).
- `isQueryBoundP_simulateQ_of_step_zero`: stateless zero-budget transfer (coin realizations).
- `uniformDeserializePreimage_left_budget` / `d2sCodecBridgeImpl_run_left_budget` /
  `d2sCodecBridgeImplMemo_challenge_budget` (F5): the Eq. 16 memoized codec bridge makes at
  most one basic-FS challenge query per `gSpec` query (zero on a `tr_i` memo hit).
- `lookupD2SAlgoMemo_insert_self_of_none` / `lookupD2SAlgoMemo_insert_stable` (F6):
  determinism of the `tr_i` memo (CO25 §5.4 D2SAlgo Item 3).
- `projectSharedQueryLog_append` / `projectSharedQueryLogSalted_append` (F7): the shared-log
  projections are list homomorphisms (used by every game-rewrite step that splits
  `proveQueryLog ++ verifyQueryLog`).
- `isQueryBoundP_deAbort` (F8a) and `tvDist_deAbort_le_probFailure` (F8b): abort elimination
  preserves budgets and moves at most the abort mass in total variation (consumed by the
  Hyb₄ → witness bridge together with the §5.7 abort analysis).

## Definitions (program text, no proof obligations)

- Honest bad events `E_inv_honest` / `E_fork_honest` / `E_time_honest` (F9) over
  `Backtrack.S_BT` (CO25 Defs. 5.11/5.13/5.15), replacing the placebo `BadEventDS.E_inv` /
  `E_fork` / `E_time` (which are `E tr ∧ state = 0` and carry no CO25 content).
- The repaired eager statement surface (F10–F12): `basicFiatShamirGameEagerRand`,
  `duplexSpongeFiatShamirGameRemappedEager`, `D_DS` (CO25 Def. 4.2 — one `Equiv.Perm`
  answering both `p` and `p⁻¹`), `KeyLemmaStatementEager`. The in-tree `KeyLemmaStatement`
  resamples repeated oracle queries i.i.d. (`𝒟[·]` semantics) and demands a coinless witness;
  the eager surface samples each oracle **once** and equips the witness with `unifSpec` coins,
  matching the paper's experiment.
- The witness construction (M1): `simulatedProverImpl` / `simulatedProverSalted` — CO25's
  `D2SAlgo^f(𝒜)` re-associated onto the coin-equipped witness spec with abort collapsed —
  plus the canonical coin realization `coinUnitImpl` (M5) with proven zero-budget lemmas.

## Residual interfaces and current status

- `D2sQueryStepGSpecBudgetResidual` (F4), `D2fOuterImplSharedBudgetResidual` (F4b):
  per-step and shared-budget dispatcher obligations, both proven in `SimulatorBudgets`.
- `SimulatedProverChallengeBudgetResidual` (M1c), `SimulatedProverSharedBudgetResidual` (M1d):
  the budget conjuncts of Lemma 5.1 for the `d2sAlgo` witness, both proven in
  `SimulatorBudgets`.
- `Lemma5_12HonestResidual` / `Lemma5_14HonestResidual` / `Lemma5_16HonestResidual` (M2):
  `¬E ⇒ ¬E_inv / ¬E_fork / ¬E_time` with the honest definitions. M2a is proven by
  `Sponge316.lemma5_12_honest`; M2b/M2c remain open.
- `KeyLemmaEagerResidual` (R4): the full quantified CO25 Lemma 5.1 on the eager surface
  (requires the Hyb₀–Hyb₄ ladder, Claims 5.21–5.24, and the §5.7 abort analysis).
-/

open OracleComp OracleSpec ProtocolSpec OracleReduction

namespace DuplexSpongeFS.KeyLemmaFoundations

open Backtrack Lookahead DSTraceStorage TraceTransform ProverTransform
open scoped NNReal

/-! ## F2 — SPMF four-step triangle chain (CO25 §5.8 assembly)

Resurrects the May-18 `tvDist_hybridChain4` on the `SPMF.tvDist` surface: the total
variation between `Hyb₀` and `Hyb₄` is bounded by the sum of the four per-step bounds. -/

/-- F2 — four-step total-variation triangle chain across the CO25 §5.8 hybrid ladder
`Hyb₀ … Hyb₄`. -/
lemma tvDist_chain4 {α : Type} (H₀ H₁ H₂ H₃ H₄ : SPMF α)
    {e₀₁ e₁₂ e₂₃ e₃₄ : ℝ}
    (h₀₁ : H₀.tvDist H₁ ≤ e₀₁) (h₁₂ : H₁.tvDist H₂ ≤ e₁₂)
    (h₂₃ : H₂.tvDist H₃ ≤ e₂₃) (h₃₄ : H₃.tvDist H₄ ≤ e₃₄) :
    H₀.tvDist H₄ ≤ e₀₁ + e₁₂ + e₂₃ + e₃₄ := by
  have t₁ := SPMF.tvDist_triangle H₀ H₁ H₄
  have t₂ := SPMF.tvDist_triangle H₁ H₂ H₄
  have t₃ := SPMF.tvDist_triangle H₂ H₃ H₄
  linarith

/-! ## F8 — abort elimination (`OptionT` → plain `OracleComp`) for the witness prover -/

section DeAbort

/-- Single-defect coupling bound for pushforwards: if `g₁` and `g₂` agree everywhere except
possibly at `z₀`, the TV distance between the pushforwards of `μ` is at most the mass of
`z₀`. -/
private lemma pmf_tvDist_map_map_le_apply {γ β : Type} (μ : PMF γ) (g₁ g₂ : γ → β) (z₀ : γ)
    (hagree : ∀ z, z ≠ z₀ → g₁ z = g₂ z) :
    PMF.tvDist (μ.map g₁) (μ.map g₂) ≤ (μ z₀).toReal := by
  letI : DecidableEq β := Classical.decEq β
  rw [PMF.tvDist_def]
  refine ENNReal.toReal_mono (PMF.apply_ne_top μ z₀) ?_
  rw [PMF.etvDist]
  have hpoint : ∀ y, ENNReal.absDiff ((μ.map g₁) y) ((μ.map g₂) y)
      ≤ (if y = g₁ z₀ then μ z₀ else 0) + (if y = g₂ z₀ then μ z₀ else 0) := by
    intro y
    rw [PMF.map_apply, PMF.map_apply]
    refine le_trans (ENNReal.absDiff_tsum_le _ _) ?_
    have hzero : ∀ z, z ≠ z₀ →
        ENNReal.absDiff (if y = g₁ z then μ z else 0) (if y = g₂ z then μ z else 0) = 0 := by
      intro z hz
      rw [hagree z hz]
      exact ENNReal.absDiff_self _
    rw [tsum_eq_single z₀ hzero]
    exact ENNReal.absDiff_le_add _ _
  refine le_trans (ENNReal.div_le_div_right (ENNReal.tsum_le_tsum hpoint) 2) ?_
  rw [ENNReal.tsum_add, tsum_ite_eq, tsum_ite_eq, ← two_mul, mul_div_assoc,
    ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- Abort elimination (`OptionT` → plain `OracleComp`): replace abort by a default output.
This is how the (aborting) `d2sAlgo` becomes the plain `OracleComp` witness `P'` demanded by
`KeyLemmaStatement` (CO25 §5.4 wrapper around Items 4-6). -/
noncomputable def deAbort {ι' : Type} {spec : OracleSpec ι'} {α : Type} [Inhabited α]
    (oa : AbortComp spec α) : OracleComp spec α :=
  (fun o => o.getD default) <$> oa.run

/-- F8a — `deAbort` preserves query budgets (it is a `map` of the underlying computation). -/
lemma isQueryBoundP_deAbort {ι' : Type} {spec : OracleSpec ι'} {α : Type} [Inhabited α]
    {oa : AbortComp spec α} {p : ι' → Prop} [DecidablePred p] {b : ℕ}
    (h : IsQueryBoundP oa.run p b) :
    IsQueryBoundP (deAbort oa) p b :=
  (isQueryBoundP_map_iff _ _ _).mpr h

/-- F8b — `deAbort` moves at most the abort mass: the TV distance between the de-aborted
computation and the sub-probability original is bounded by the abort probability. Consumed by
the Hyb₄ → witness bridge together with the §5.7 abort analysis (`Pr[abort] ≤ Pr[E]`). -/
lemma tvDist_deAbort_le_probFailure {ι' : Type} {spec : OracleSpec ι'}
    [spec.Fintype] [spec.Inhabited] {α : Type} [Inhabited α]
    (oa : AbortComp spec α) :
    SPMF.tvDist 𝒟[deAbort oa] 𝒟[oa] ≤ (Pr[⊥ | oa]).toReal := by
  classical
  set μ : PMF (Option (Option α)) := (𝒟[oa.run]).toPMF with hμ
  have h₁ : (𝒟[deAbort oa]).toPMF = μ.map (Option.map (fun o => o.getD default)) := by
    rw [deAbort, evalDist_map, SPMF.toPMF_map, hμ]
    rfl
  have h₂ : (𝒟[oa]).toPMF = μ.map (fun z => z.bind id) := by
    have hbind : (𝒟[oa] : SPMF α)
        = (𝒟[oa.run] >>= fun y => match y with | some a => pure a | none => failure) := rfl
    rw [hbind, SPMF.toPMF_bind, ← PMF.bind_pure_comp]
    unfold Option.elimM
    rw [PMF.monad_bind_eq_bind]
    refine PMF.bind_congr _ _ _ fun z => ?_
    intro _
    match z with
    | none => rfl
    | some none => simp [SPMF.toPMF_failure, Function.comp]
    | some (some a) => simp [SPMF.toPMF_pure, Function.comp]
  unfold SPMF.tvDist
  rw [h₁, h₂]
  refine le_trans (pmf_tvDist_map_map_le_apply μ _ _ (some none) ?_) ?_
  · intro z hz
    match z with
    | none => rfl
    | some none => exact absurd rfl hz
    | some (some a) => rfl
  · refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top probFailure_le_one) ?_
    rw [OptionT.probFailure_eq]
    exact le_add_self

end DeAbort

/-! ## F1 — `ηStar` numerics (CO25 Eq. 5 / Claims 5.21, 5.22, 5.24 bounds)

**Statement-fidelity note**: the in-tree `ηStar` (KeyLemma.lean) has denominator
`2·|U|^(C+1)`, while the May-18 blueprint, the per-claim bounds below, and CO25 Eq. 5 use
`2·|U|^C`. `ηStarPaper` is the `C`-exponent bound the hybrid chain delivers;
`ηStar_le_ηStarPaper` records that the in-tree bound is strictly stronger (hence the
in-tree `KeyLemmaResidual` claims more than Claims 5.21–5.24 can prove); the upstream
one-token fix is brick F0a. -/

section EtaStarNumerics

variable {n : ℕ} {pSpec : ProtocolSpec n}

/-- CO25 Claim 5.21 bound: `(7T² − 3T)/(2|Σ|^c)`, `T = tₕ + 1 + tₚ + L + tₚᵢ` (Lemma 5.8's
birthday bound at the Hyb₀/Hyb₁ trace length). -/
noncomputable def claim5_21Bound (U : Type) [SpongeUnit U] [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  (7 * ((tₕ + 1 + tₚ + L + tₚᵢ : ℕ) : ℝ) ^ 2 - 3 * ((tₕ + 1 + tₚ + L + tₚᵢ : ℕ) : ℝ))
    / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)

/-- CO25 Claim 5.22 bound (Eq. 53): `θ★ · maxᵢ ε_cdc,i + Σᵢ ε_cdc,i` — the codec decoding
bias paid once per prover-side `gᵢ` query plus once per round for the verifier side. -/
noncomputable def claim5_22Bound {n : ℕ} {pSpec : ProtocolSpec n}
    (tₕ tₚ tₚᵢ : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) : ℝ :=
  (θStar tₕ tₚ tₚᵢ : ℝ) * ((⨆ i, εcodec i : ℝ≥0) : ℝ) + ((∑ i, εcodec i : ℝ≥0) : ℝ)

/-- CO25 Claim 5.24 bound (Eq. 55): `7L(2tₕ+2+2tₚ+L+2tₚᵢ)/(2|Σ|^c) − 5(L+1)/|Σ|^c` — the
verifier-replay bad-event probability for the Hyb₃/Hyb₄ step. -/
noncomputable def claim5_24Bound (U : Type) [SpongeUnit U] [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ L : ℕ) : ℝ :=
  (7 * (L : ℝ) * (2 * (tₕ : ℝ) + 2 + 2 * (tₚ : ℝ) + (L : ℝ) + 2 * (tₚᵢ : ℝ)))
      / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
    - (5 * ((L : ℝ) + 1)) / ((Fintype.card U : ℝ) ^ SpongeSize.C)

/-- Paper-exponent `ηStar` (denominator `2·|U|^C`, CO25 Eq. 5): the bound the §5.8 hybrid
chain delivers. Mirrors `DuplexSpongeFS.ηStar` except for the denominator exponent. -/
noncomputable def ηStarPaper (U : Type) [SpongeUnit U] [Fintype U] [SpongeSize]
    (tₕ tₚ tₚᵢ L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) : ℝ :=
  (7 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) ^ 2 + (28 * (L : ℝ) + 25) * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ)
      + (14 * (L : ℝ) + 1) * ((L : ℝ) + 1))
    / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
    + (θStar tₕ tₚ tₚᵢ : ℝ) * ((⨆ i, εcodec i : ℝ≥0) : ℝ) + ((∑ i, εcodec i : ℝ≥0) : ℝ)

/-- F1a — the in-tree `ηStar` (exponent `C+1`) is ≤ the paper bound (exponent `C`); i.e. the
residual as stated claims something **stronger** than Claims 5.21–5.24 deliver. Records the
exponent gap. -/
lemma ηStar_le_ηStarPaper (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) :
    ((ηStar (pSpec := pSpec) U tₕ tₚ tₚᵢ L εcodec : ℝ≥0) : ℝ)
      ≤ ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L εcodec := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc0 : (0 : ℝ) < (Fintype.card U : ℝ) := lt_of_lt_of_le zero_lt_one hcard1
  simp only [ηStar, ηStarPaper]
  push_cast
  have hpow : (Fintype.card U : ℝ) ^ SpongeSize.C
      ≤ (Fintype.card U : ℝ) ^ (SpongeSize.C + 1) :=
    pow_le_pow_right₀ hcard1 (Nat.le_succ _)
  refine add_le_add (add_le_add ?_ le_rfl) le_rfl
  refine div_le_div_of_nonneg_left ?_ ?_ ?_
  · positivity
  · exact mul_pos two_pos (pow_pos hc0 _)
  · nlinarith [pow_pos hc0 SpongeSize.C]

/-- F1b — numeric assembly (CO25 §5.8): the three nonzero per-step bounds sum to at most
`ηStarPaper` (Claim 5.23's step is exactly `0`). The slack is `(14t + 7)/(2|U|^C) ≥ 0`. -/
lemma claimSum_le_ηStarPaper (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]
    (tₕ tₚ tₚᵢ L : ℕ) (εcodec : pSpec.ChallengeIdx → ℝ≥0) :
    claim5_21Bound U tₕ tₚ tₚᵢ L + claim5_22Bound (pSpec := pSpec) tₕ tₚ tₚᵢ εcodec
        + claim5_24Bound U tₕ tₚ tₚᵢ L
      ≤ ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L εcodec := by
  have hU : Nonempty U := ⟨0⟩
  have hcard1 : (1 : ℝ) ≤ (Fintype.card U : ℝ) := by exact_mod_cast Fintype.card_pos
  have hc0 : (0 : ℝ) < (Fintype.card U : ℝ) := lt_of_lt_of_le zero_lt_one hcard1
  have hP : (0 : ℝ) < (Fintype.card U : ℝ) ^ SpongeSize.C := pow_pos hc0 _
  have h2P : (0 : ℝ) < 2 * (Fintype.card U : ℝ) ^ SpongeSize.C := by linarith
  have frac_le : ∀ x y z w : ℝ, x + y - 2 * z ≤ w →
      x / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
        + (y / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
          - z / ((Fintype.card U : ℝ) ^ SpongeSize.C))
      ≤ w / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := by
    intro x y z w hxyz
    have hcomb : x / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
        + (y / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C)
          - z / ((Fintype.card U : ℝ) ^ SpongeSize.C))
        = (x + y - 2 * z) / (2 * (Fintype.card U : ℝ) ^ SpongeSize.C) := by
      field_simp
      ring
    rw [hcomb, div_le_div_iff₀ h2P h2P]
    exact mul_le_mul_of_nonneg_right hxyz (le_of_lt h2P)
  have main : 7 * ((tₕ + 1 + tₚ + L + tₚᵢ : ℕ) : ℝ) ^ 2
        - 3 * ((tₕ + 1 + tₚ + L + tₚᵢ : ℕ) : ℝ)
        + (7 * (L : ℝ) * (2 * (tₕ : ℝ) + 2 + 2 * (tₚ : ℝ) + (L : ℝ) + 2 * (tₚᵢ : ℝ)))
        - 2 * (5 * ((L : ℝ) + 1))
      ≤ 7 * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ) ^ 2
        + (28 * (L : ℝ) + 25) * ((tₕ + tₚ + tₚᵢ : ℕ) : ℝ)
        + (14 * (L : ℝ) + 1) * ((L : ℝ) + 1) := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) tₕ, Nat.cast_nonneg (α := ℝ) tₚ,
      Nat.cast_nonneg (α := ℝ) tₚᵢ]
  have step := frac_le _ _ _ _ main
  unfold claim5_21Bound claim5_22Bound claim5_24Bound ηStarPaper
  linarith [step]

end EtaStarNumerics

/-! ## F3 — generic `IsQueryBoundP` lifts through the §5.4 monad stacks

VCVio has `IsQueryBoundP.simulateQ_run_StateT_of_step` for `StateT σ (OracleComp spec')`;
the §5.4 simulator stacks add `OptionT` (abort) and a second `StateT` (the `tr_i` memo).
These lemmas are the missing generic carriers (candidates for upstreaming to VCVio). -/

section QueryBoundLifts

universe u

/-- F3a — transfer a predicate-targeted query bound through a `StateT σ (OptionT _)`
simulation whose handler step consumes at most one target-side `q`-query exactly when the
source query satisfies `p`. The abort (`none`) continuation makes no queries. -/
theorem isQueryBoundP_simulateQ_stateT_optionT_of_step
    {ι₁ ι₂ : Type u} {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂} {α σ : Type u}
    {p : ι₁ → Prop} [DecidablePred p] {q : ι₂ → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ (OptionT (OracleComp spec')))}
    {oa : OracleComp spec α} {b : ℕ}
    (h : IsQueryBoundP oa p b)
    (hstep : ∀ t s, IsQueryBoundP (((impl t).run s).run) q (if p t then 1 else 0))
    (s : σ) :
    IsQueryBoundP (((simulateQ impl oa).run s).run) q b := by
  induction oa using OracleComp.inductionOn generalizing b s with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind, OptionT.run_bind]
      unfold Option.elimM
      have hstep' : IsQueryBoundP
          (((liftM (impl t) : StateT σ (OptionT (OracleComp spec')) (spec.Range t)).run s).run)
          q (if p t then 1 else 0) := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t s
      have hrest : ∀ x ∈ support (((liftM (impl t) :
            StateT σ (OptionT (OracleComp spec')) (spec.Range t)).run s).run),
          IsQueryBoundP
            (Option.elim x (pure none)
              (fun us => ((simulateQ impl (mx us.1)).run us.2).run))
            q (if p t then b - 1 else b) := by
        intro x _
        match x with
        | none => exact isQueryBoundP_pure _ _ _
        | some us => exact ih us.1 (h.2 us.1) us.2
      exact IsQueryBoundP.mono (isQueryBoundP_bind hstep' hrest) (by
        by_cases ht : p t
        · simp only [if_pos ht]
          rcases h.1 with hnot | hpos
          · exact absurd ht hnot
          · omega
        · simp only [if_neg ht]; omega)

/-- F3b — as `isQueryBoundP_simulateQ_stateT_optionT_of_step`, with a second `StateT` layer
(the §5.4 D2SAlgo Item 3 `tr_i` memo). -/
theorem isQueryBoundP_simulateQ_stateT2_optionT_of_step
    {ι₁ ι₂ : Type u} {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂} {α σ₁ σ₂ : Type u}
    {p : ι₁ → Prop} [DecidablePred p] {q : ι₂ → Prop} [DecidablePred q]
    {impl : QueryImpl spec (StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec'))))}
    {oa : OracleComp spec α} {b : ℕ}
    (h : IsQueryBoundP oa p b)
    (hstep : ∀ t s₁ s₂,
      IsQueryBoundP ((((impl t).run s₁).run s₂).run) q (if p t then 1 else 0))
    (s₁ : σ₁) (s₂ : σ₂) :
    IsQueryBoundP ((((simulateQ impl oa).run s₁).run s₂).run) q b := by
  induction oa using OracleComp.inductionOn generalizing b s₁ s₂ with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      rw [isQueryBoundP_query_bind_iff] at h
      rw [simulateQ_query_bind, StateT.run_bind, StateT.run_bind, OptionT.run_bind]
      unfold Option.elimM
      have hstep' : IsQueryBoundP
          ((((liftM (impl t) : StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))
            (spec.Range t)).run s₁).run s₂).run)
          q (if p t then 1 else 0) := by
        simpa [OracleComp.liftM_run_StateT, MonadLift.monadLift] using hstep t s₁ s₂
      have hrest : ∀ x ∈ support ((((liftM (impl t) :
            StateT σ₁ (StateT σ₂ (OptionT (OracleComp spec')))
            (spec.Range t)).run s₁).run s₂).run),
          IsQueryBoundP
            (Option.elim x (pure none)
              (fun uss => (((simulateQ impl (mx uss.1.1)).run uss.1.2).run uss.2).run))
            q (if p t then b - 1 else b) := by
        intro x _
        match x with
        | none => exact isQueryBoundP_pure _ _ _
        | some uss => exact ih uss.1.1 (h.2 uss.1.1) uss.1.2 uss.2
      exact IsQueryBoundP.mono (isQueryBoundP_bind hstep' hrest) (by
        by_cases ht : p t
        · simp only [if_pos ht]
          rcases h.1 with hnot | hpos
          · exact absurd ht hnot
          · omega
        · simp only [if_neg ht]; omega)

/-- Predicate-targeted budget for `Option.elimM`: the scrutinee budget plus a uniform budget
for the two continuations. Workhorse for the `OptionT.run`-normalized §5.4 goals, whose
abort plumbing is `Option.elimM _ (pure none) _`. -/
theorem isQueryBoundP_elimM
    {ι₂ : Type u} {spec' : OracleSpec ι₂} {α β : Type u}
    {q : ι₂ → Prop} [DecidablePred q] {x : OracleComp spec' (Option α)}
    {d : OracleComp spec' β} {k : α → OracleComp spec' β} {n m : ℕ}
    (hx : IsQueryBoundP x q n)
    (hd : IsQueryBoundP d q m) (hk : ∀ a, IsQueryBoundP (k a) q m) :
    IsQueryBoundP (Option.elimM x d k) q (n + m) := by
  unfold Option.elimM
  refine isQueryBoundP_bind hx fun o _ => ?_
  match o with
  | none => exact hd
  | some a => exact hk a

/-- Stateless zero-budget transfer: if every handler step makes no `q`-queries, neither does
the simulation. Used for coin realizations (`unifSpec`-only implementations make no
challenge/shared queries). -/
theorem isQueryBoundP_simulateQ_of_step_zero
    {ι₁ ι₂ : Type u} {spec : OracleSpec ι₁} {spec' : OracleSpec ι₂} {α : Type u}
    {q : ι₂ → Prop} [DecidablePred q]
    {impl : QueryImpl spec (OracleComp spec')}
    (oa : OracleComp spec α)
    (hstep : ∀ t, IsQueryBoundP (impl t) q 0) :
    IsQueryBoundP (simulateQ impl oa) q 0 := by
  induction oa using OracleComp.inductionOn with
  | pure x => simp [simulateQ_pure]
  | query_bind t mx ih =>
      simp only [simulateQ_query_bind, OracleQuery.input_query, monadLift_self]
      simpa using isQueryBoundP_bind (hstep t) (fun u _ => ih u)

end QueryBoundLifts

/-! ## F5/F6/F7 — §5.4 simulator bookkeeping bricks -/

section SimulatorBookkeeping

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U] {δ : ℕ}
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

section MemoDeterminism

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

omit [SpongeUnit U] [SpongeSize] [Fintype U] [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Fintype (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] [SaltCodec U δ Salt] in
/-- F6a — `tr_i` memo determinism, miss-then-insert: after inserting an entry whose key was
absent, lookup at that key returns the inserted response (CO25 §5.4 D2SAlgo Item 3). -/
lemma lookupD2SAlgoMemo_insert_self_of_none
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (e : D2SAlgoMemoEntry StmtIn U δ Salt pSpec)
    (h : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo e.roundIdx e.stmt e.salt e.encodedMessages = none) :
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        (insertD2SAlgoMemo memo e) e.roundIdx e.stmt e.salt e.encodedMessages
      = some e.response := by
  unfold lookupD2SAlgoMemo at h
  unfold lookupD2SAlgoMemo insertD2SAlgoMemo
  rw [List.foldl_append, h]
  simp only [List.foldl_cons, List.foldl_nil]
  simp

omit [SpongeUnit U] [SpongeSize] [Fintype U] [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)] [∀ i, Fintype (pSpec.Challenge i)]
  [∀ i, DecidableEq (pSpec.Challenge i)] [SaltCodec U δ Salt] in
/-- F6b — `tr_i` memo stability: an existing binding survives any later insert (first match
wins in `lookupD2SAlgoMemo`'s left fold). Together with F6a this gives CO25 §5.4 D2SAlgo
Item 3's determinism: same key ⇒ same response across the whole run. -/
lemma lookupD2SAlgoMemo_insert_stable
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec)
    (e : D2SAlgoMemoEntry StmtIn U δ Salt pSpec)
    (i : pSpec.ChallengeIdx) (x : StmtIn) (s : Salt)
    (em : pSpec.EncodedMessagesBefore U i.1.castSucc)
    (r : Vector U (challengeSize (pSpec := pSpec) i))
    (h : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        memo i x s em = some r) :
    lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt) (pSpec := pSpec)
        (insertD2SAlgoMemo memo e) i x s em = some r := by
  unfold lookupD2SAlgoMemo at h
  unfold lookupD2SAlgoMemo insertD2SAlgoMemo
  rw [List.foldl_append, h]
  rfl

end MemoDeterminism

omit [DecidableEq StmtIn] [DecidableEq U] [Fintype U] codec
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- F7 — the shared-log projection is a list homomorphism (needed by every game-rewrite step
that splits `proveQueryLog ++ verifyQueryLog`, CO25 §5.5). -/
lemma projectSharedQueryLog_append
    (l₁ l₂ : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    projectSharedQueryLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (l₁ ++ l₂)
      = projectSharedQueryLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U) l₁
        ++ projectSharedQueryLog (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) l₂ := by
  simp [projectSharedQueryLog]

omit [DecidableEq StmtIn] [DecidableEq U] [Fintype U] codec
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)] in
/-- F7b — salted twin of `projectSharedQueryLog_append`. -/
lemma projectSharedQueryLogSalted_append {Salt : Type}
    (l₁ l₂ : QueryLog (oSpec + duplexSpongeChallengeOracle StmtIn U)) :
    projectSharedQueryLogSalted (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (Salt := Salt) (l₁ ++ l₂)
      = projectSharedQueryLogSalted (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (Salt := Salt) l₁
        ++ projectSharedQueryLogSalted (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec)
            (U := U) (Salt := Salt) l₂ := by
  simp [projectSharedQueryLogSalted]

section CodecBridgeBudget

variable [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

omit [SpongeSize] [DecidableEq StmtIn] [∀ i, Fintype (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Message i)] in
/-- The `ψ⁻¹` uniform-preimage sampler makes no challenge-summand (left) queries: its only
query is the `unifSpec` index draw (CO25 §5.4 Step 3). -/
lemma uniformDeserializePreimage_left_budget
    {i : pSpec.ChallengeIdx} (ch : pSpec.Challenge i) :
    IsQueryBoundP
      (uniformDeserializePreimage (pSpec := pSpec) (U := U)
        (challengeSpec := fsChallengeOracle (StmtIn × Salt) pSpec) ch)
      (fun j => j.isLeft = true) 0 := by
  unfold uniformDeserializePreimage sampleFromList
  simp only [HasQuery.instOfMonadLift_query]
  rw [isQueryBoundP_query_bind_iff]
  exact ⟨Or.inl (by simp), fun u => isQueryBoundP_pure _ _ _⟩

omit [DecidableEq StmtIn] [∀ i, DecidableEq (pSpec.Message i)] in
/-- F5 helper — the raw Eq. 16 codec bridge `ψᵢ⁻¹ ∘ fᵢ ∘ φᵢ⁻¹` makes at most one
challenge-summand (left) query: the single `fᵢ` query (CO25 §5.4 Eq. 16 Step 2). -/
lemma d2sCodecBridgeImpl_run_left_budget
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain) :
    IsQueryBoundP
      ((d2sCodecBridgeImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
        (Salt := Salt) gq).run)
      (fun j => j.isLeft = true) 1 := by
  unfold d2sCodecBridgeImpl
  cases hmb : hybEncodedMessagesBefore? (pSpec := pSpec) (U := U) gq.1 gq.2.2.2 with
  | none =>
      simp [hmb]
  | some mb =>
      simp only [hmb, OptionT.run_bind, pure_bind, OptionT.run_lift,
        HasQuery.instOfMonadLift_query]
      unfold Option.elimM
      rw [bind_assoc]
      simp only [pure_bind, Option.elim]
      refine (isQueryBoundP_query_bind_iff _ _ _ _).mpr
        ⟨Or.inr one_pos, fun ch => ?_⟩
      exact IsQueryBoundP.mono
        (isQueryBoundP_bind (m := 0)
          (uniformDeserializePreimage_left_budget
            (pSpec := pSpec) (U := U) (StmtIn := StmtIn) (Salt := Salt) (i := gq.1) ch)
          (fun x _ => isQueryBoundP_pure _ _ _))
        (Nat.zero_le _)

omit [∀ i, DecidableEq (pSpec.Message i)] in
/-- F5 — the Eq. 16 **memoized** codec bridge makes at most one basic-FS challenge query per
`gSpec` query (zero on a `tr_i` memo hit; CO25 §5.4 D2SAlgo Item 3). This is the per-step
bound feeding the `θ★ = tₚ` challenge budget of the simulated prover. -/
lemma d2sCodecBridgeImplMemo_challenge_budget
    (gq : (gSpec (U := U) StmtIn pSpec δ).Domain)
    (memo : D2SAlgoMemo StmtIn U δ Salt pSpec) :
    IsQueryBoundP
      (((d2sCodecBridgeImplMemo (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ)
          (Salt := Salt) gq).run memo).run)
      (fun j => j.isLeft = true) 1 := by
  unfold d2sCodecBridgeImplMemo
  simp only [StateT.run_bind, StateT.run_get, pure_bind]
  cases hl : lookupD2SAlgoMemo (StmtIn := StmtIn) (U := U) (δ := δ) (Salt := Salt)
      (pSpec := pSpec) memo gq.1 gq.2.1
      (SaltCodec.encode (U := U) (δ := δ) (Salt := Salt) gq.2.2.1) gq.2.2.2 with
  | some r =>
      simp only [StateT.run_pure, OptionT.run_pure]
      exact isQueryBoundP_pure _ _ _
  | none =>
      simp only [StateT.run_bind, StateT.run_monadLift, OptionT.run_bind, monadLift_self]
      exact isQueryBoundP_elimM (n := 1) (m := 0)
        (isQueryBoundP_elimM (n := 1) (m := 0)
          (d2sCodecBridgeImpl_run_left_budget
            (pSpec := pSpec) (U := U) (StmtIn := StmtIn) (δ := δ) (Salt := Salt) gq)
          (isQueryBoundP_pure _ _ _) (fun _ => isQueryBoundP_pure _ _ _))
        (isQueryBoundP_pure _ _ _)
        (fun _ => isQueryBoundP_elimM (n := 0) (m := 0)
          (IsQueryBoundP.mono (isQueryBoundP_pure _ _ _) le_rfl)
          (isQueryBoundP_pure _ _ _) (fun _ => isQueryBoundP_pure _ _ _))

end CodecBridgeBudget

end SimulatorBookkeeping

/-! ## F9 — honest bad events `E_inv` / `E_fork` / `E_time` (CO25 Defs. 5.11/5.13/5.15)

Resurrected from the May-18 blueprint. The in-tree `BadEventDS.E_inv` / `E_fork` / `E_time`
are placebos (`E trace ∧ state = 0`), making "lemmas" 5.12/5.14/5.16 vacuous; the definitions
below are the real events over `Backtrack.S_BT`. The honest implications `¬E ⇒ ¬E_*` are the
`Lemma5_*HonestResidual` Props below. -/

section HonestBadEvents

open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
variable (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
  (state : CanonicalSpongeState U)

/-- CO25 Definition 5.11 / Eq. 35 — `E_inv(tr, s)`: some BackTrack chain step was constructed
using `p⁻¹` rather than `p` (an inverse-permutation entry anchors a forward chain link). -/
def E_inv_honest (S : Backtrack.S_BT tr state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S,
  ∃ ιx : Fin p.1.outputState.length,
  ∃ s_out s_in : CanonicalSpongeState U,
    tr[(p.2.2 ⟨ιx.val, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val]? = some ⟨.inr (.inr s_out), s_in⟩

/-- CO25 Definition 5.13 — `E_fork(tr, s)`: more than one maximal backtrack sequence,
`|S_BT(tr, s)| > 1`. -/
def E_fork_honest (S : Backtrack.S_BT tr state) : Prop :=
  S.seqFamily.card > 1

/-- CO25 Definition 5.15 / Eq. 41 — `E_{time,h}(tr, s)`: the anchoring hash query appears in
the trace **after** the first chain permutation query (out-of-order hash). -/
def E_time_h_honest (S : Backtrack.S_BT tr state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S,
    p.2.1.val > (p.2.2 ⟨0, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val

/-- CO25 Definition 5.15 / Eq. 42 — `E_{time,p}(tr, s)`: a later chain permutation query
appears in the trace **before** its predecessor (out-of-order permutation). -/
def E_time_p_honest (S : Backtrack.S_BT tr state) : Prop :=
  ∃ p ∈ Backtrack.J_BT S,
  ∃ ιx : Fin p.1.outputState.length,
    (p.2.2 ⟨ιx.val, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val >
    (p.2.2 ⟨ιx.val + 1, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val

/-- CO25 Definition 5.15 — `E_time = E_{time,h} ∨ E_{time,p}`. -/
def E_time_honest (S : Backtrack.S_BT tr state) : Prop :=
  E_time_h_honest tr state S ∨ E_time_p_honest tr state S

end HonestBadEvents

section HonestBadEventResiduals

open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

/-- M2a residual interface — CO25 Lemma 5.12 (honest form): off the combined bad event `E`,
no BackTrack chain step is anchored by an inverse-permutation entry,
`¬E(tr) → ¬E_inv(tr, s)`. Discharged in `Lemma512Honest.lean`. -/
def Lemma5_12HonestResidual (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ E tr → ¬ E_inv_honest tr state S

/-- M2b residual — CO25 Lemma 5.14 (honest form): off `E` the backtrack family has at most
one maximal sequence, `¬E(tr) → ¬E_fork(tr, s)`.

**Audit status (2026-06-10): REFUTED as stated** —
`DuplexSpongeFS.Sponge316.ForkCounter.lemma5_14HonestResidual_false`
(`Lemma514ForkFalse.lean`, axiom-clean) exhibits a 5-entry trace with two
alternating-pair loop chains to the same state, so `E_fork_honest` fires while `E` is
absent, exploiting the same `redundantEntryDS` deviation from CO25 Def. 5.5
(same-direction swapped certificates instead of the paper's opposite-direction `p⁻¹` one)
that refutes the sibling `Lemma5_16HonestResidual` (`Lemma516TimePFalse.lean`).
Do NOT add this residual as a hypothesis expecting a future discharge; repair
`redundantEntryDS` first. -/
def Lemma5_14HonestResidual (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ E tr → ¬ E_fork_honest tr state S

/-- M2c residual — CO25 Lemma 5.16 (honest form): off `E` all chain queries appear in trace
order, `¬E(tr) → ¬E_time(tr, s)`.

**Audit status (2026-06-10): REFUTED as stated** —
`DuplexSpongeFS.Sponge316.TimePCounter.lemma5_16HonestResidual_false`
(`Lemma516TimePFalse.lean`, axiom-clean) exhibits a 4-entry trace where `E_time_p_honest`
fires while `E` is absent, exploiting the `redundantEntryDS` deviation from CO25 Def. 5.5
(same-direction swapped certificate instead of the paper's opposite-direction `p⁻¹` one).
The TRUE `E_{time,h}` half is proven in `Lemma516HashHalf.lean`
(`lemma5_16_honest_hash_half`). Do NOT add this residual as a hypothesis expecting a
future discharge; repair `redundantEntryDS` first. -/
def Lemma5_16HonestResidual (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ E tr → ¬ E_time_honest tr state S

end HonestBadEventResiduals

/-! ## F10–F12, M1, M5, R4 — the eager statement surface, the witness construction, and the
research-core target -/

section EagerSurface

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn StmtOut : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [VCVCompatible StmtIn] [∀ i, VCVCompatible (pSpec.Challenge i)]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U]
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-- Keep only left-summand entries of a mixed query log (used to hide the witness prover's
private `unifSpec` coins from the logged game output). -/
def projectLeftQueryLog {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁} {spec₂ : OracleSpec ι₂}
    (log : QueryLog (spec₁ + spec₂)) : QueryLog spec₁ :=
  log.filterMap fun e =>
    match e with
    | ⟨.inl q, r⟩ => some ⟨q, r⟩
    | ⟨.inr _, _⟩ => none

omit [SpongeSize] in
/-- `projectLeftQueryLog` is a list homomorphism (companion to F7). -/
lemma projectLeftQueryLog_append {ι₁ ι₂ : Type} {spec₁ : OracleSpec ι₁}
    {spec₂ : OracleSpec ι₂} (l₁ l₂ : QueryLog (spec₁ + spec₂)) :
    projectLeftQueryLog (l₁ ++ l₂)
      = projectLeftQueryLog l₁ ++ projectLeftQueryLog l₂ := by
  simp [projectLeftQueryLog]

/-- F11b — `SampleableType` for the random-permutation carrier of `D_𝔖` (CO25 Def. 4.2):
`Equiv.Perm (CanonicalSpongeState U)` is finite (via `Vector U N ≃ (Fin N → U)`), decidable,
and inhabited (`Equiv.refl`). Provided as a `def` (not an instance) to avoid overlap with the
`FinEnum`-route instances. -/
@[reducible]
noncomputable def sampleableTypePermCanonicalSpongeState
    (U : Type) [SpongeUnit U] [SpongeSize] [Fintype U] [DecidableEq U] :
    SampleableType (Equiv.Perm (CanonicalSpongeState U)) :=
  letI : Fintype (CanonicalSpongeState U) :=
    Fintype.ofEquiv (Fin SpongeSize.N → U) Equiv.rootVectorEquivFin.symm
  letI : Nonempty (Equiv.Perm (CanonicalSpongeState U)) := ⟨Equiv.refl _⟩
  SampleableType.ofFintype _

/-- F11a — `D_𝔖` rebuilt (CO25 Def. 4.2): eager random-function + random-permutation carrier
for the duplex-sponge challenge oracle. `p` and `p⁻¹` answer through **one** `Equiv.Perm`, so
repeated and inverse queries are mutually consistent — the property the i.i.d. `𝒟[·]`
surface lacks. -/
noncomputable def D_DS (StmtIn U : Type) [SpongeUnit U] [SpongeSize] [Fintype U]
    [DecidableEq U]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))] :
    OracleDistribution (duplexSpongeChallengeOracle StmtIn U) where
  Carrier := (StmtIn → Vector U SpongeSize.C) × Equiv.Perm (CanonicalSpongeState U)
  sample := do
    let h ← $ᵗ (StmtIn → Vector U SpongeSize.C)
    let p ← $ᵗ (Equiv.Perm (CanonicalSpongeState U))
    pure (h, p)
  toImpl := fun c q =>
    match q with
    | .inl x => pure (c.1 x)
    | .inr (.inl sIn) => pure (c.2 sIn)
    | .inr (.inr sOut) => pure (c.2.symm sOut)

variable [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec]
  [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]

/-- F10a — eager basic-FS game with a coin-equipped witness prover.

The FS challenge function is sampled **once** (`Df.sample`), so the prover and the
re-deriving verifier see the *same* function — the paper's experiment. The witness prover
gets private randomness through a `unifSpec` summand whose queries are *not* logged
(`projectLeftQueryLog`), matching CO25's randomized `D2SAlgo`. -/
noncomputable def basicFiatShamirGameEagerRand
    (Df : OracleDistribution (fsChallengeOracle StmtIn pSpec))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P' : OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) := do
  let c ← Df.sample
  let realImpl : QueryImpl (oSpec + fsChallengeOracle StmtIn pSpec) ProbComp :=
    oImpl + Df.toImpl c
  let coins : QueryImpl unifSpec ProbComp := fun m => (liftM (unifSpec.query m) : ProbComp _)
  let ⟨⟨stmtIn, messages⟩, pLogAll⟩ ←
    simulateQ (realImpl + coins) ((simulateQ loggingOracle P').run)
  let ⟨stmtOut?, vLog⟩ ←
    simulateQ realImpl
      ((simulateQ loggingOracle
        (V.fiatShamir.run stmtIn (fun i => match i with | ⟨0, _⟩ => messages))).run)
  match stmtOut? with
  | none => pure none
  | some stmtOut =>
      pure (some ⟨stmtIn, stmtOut, messages, projectLeftQueryLog pLogAll, vLog⟩)

variable {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]

/-- F10b — eager remapped DSFS game (`Hyb₀` of the §5.8 ladder): run the DSFS game against a
once-sampled `(h, p, p⁻¹)` carrier, then push both logs through the §5.5 `D2STrace`
(transform randomness realized by `𝒰(Σ)` sampling, abort collapsing to `none`). -/
noncomputable def duplexSpongeFiatShamirGameRemappedEager
    [SampleableType U] (δ : ℕ)
    (Dds : OracleDistribution (duplexSpongeChallengeOracle StmtIn U))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages)) :
    ProbComp (Option (StmtIn × StmtOut × pSpec.Messages
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec)
      × QueryLog (oSpec + fsChallengeOracle StmtIn pSpec))) := do
  let c ← Dds.sample
  let out? ←
    simulateQ (oImpl + Dds.toImpl c)
      (DuplexSpongeFS.duplexSpongeFiatShamirGame (U := U) V P).run
  match out? with
  | none => pure none
  | some ⟨stmtIn, stmtOut, messages, pLog, vLog⟩ => do
      let pLog'? ←
        simulateQ (d2sUnitSampleImpl (U := U))
          ((TraceTransform.d2sTrace (T_H := T_H) (T_P := T_P) (δ := δ)
            (pSpec := pSpec) pLog).run)
      let vLog'? ←
        simulateQ (d2sUnitSampleImpl (U := U))
          ((TraceTransform.d2sTrace (T_H := T_H) (T_P := T_P) (δ := δ)
            (pSpec := pSpec) vLog).run)
      match pLog'?, vLog'? with
      | some pLog', some vLog' => pure (some ⟨stmtIn, stmtOut, messages, pLog', vLog'⟩)
      | _, _ => pure none

/-- Challenge-query classifier on the coin-equipped witness index type. -/
def isFSChallengeCoinIdx {ι₁ κ : Type} : ((ι₁ ⊕ κ) ⊕ ℕ) → Bool
  | .inl (.inr _) => true
  | _ => false

/-- Shared-query classifier (at a fixed `oSpec` index) on the coin-equipped witness index. -/
def isSharedCoinIdx {ι₁ κ : Type} [DecidableEq ι₁] (i : ι₁) : ((ι₁ ⊕ κ) ⊕ ℕ) → Bool
  | .inl (.inl i') => decide (i' = i)
  | _ => false

/-- F12 — **repaired** key-lemma surface (per-prover): eager-sampled oracles on both sides,
coin-equipped witness prover, paper-exponent error bound. This is the statement the CO25
§5.8 hybrid chain proves; the in-tree `KeyLemmaStatement` (i.i.d. `𝒟[·]` oracles, coinless
`P'`, `C+1` exponent) does **not** match it — see the module docstring. -/
def KeyLemmaStatementEager
    [DecidableEq ι] [SampleableType U]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (Df : OracleDistribution (fsChallengeOracle StmtIn pSpec))
    (Dds : OracleDistribution (duplexSpongeChallengeOracle StmtIn U))
    (oImpl : QueryImpl oSpec ProbComp)
    (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ L : ℕ) : Prop :=
  ∃ P' : OracleComp ((oSpec + fsChallengeOracle StmtIn pSpec) + unifSpec)
      (StmtIn × pSpec.Messages),
    (∀ i : ι, IsQueryBoundP P' (fun j => isSharedCoinIdx i j = true) (tₒ i)) ∧
    IsQueryBoundP P' (fun j => isFSChallengeCoinIdx j = true) (θStar tₕ tₚ tₚᵢ) ∧
    SPMF.tvDist
        𝒟[basicFiatShamirGameEagerRand Df oImpl V P']
        𝒟[duplexSpongeFiatShamirGameRemappedEager (T_H := T_H) (T_P := T_P) δ Dds oImpl V P]
      ≤ ηStarPaper (pSpec := pSpec) U tₕ tₚ tₚᵢ L codec.decodingBias

section Witness

variable {δ : ℕ} [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)]
  {Salt : Type} [SaltCodec U δ Salt]

/-- M1a — oracle re-association for the witness: realize `d2sAlgo`'s spec
`oSpec + (fsCh' + ((Unit →ₒ U) + unifSpec))` inside the witness spec
`(oSpec + fsCh') + unifSpec`, with `Unit →ₒ U` realized by `unitImpl` (canonically
`coinUnitImpl`: uniform `U`-sampling from `unifSpec` coins). -/
noncomputable def simulatedProverImpl
    (unitImpl : QueryImpl (Unit →ₒ U)
      (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec))) :
    QueryImpl
      (oSpec + D2SChallengePlusUnitOracle (U := U)
        (fsChallengeOracle (StmtIn × Salt) pSpec))
      (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)) :=
  fun qq =>
    match qq with
    | .inl qo =>
        query (spec := (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
          (.inl (.inl qo))
    | .inr (.inl qf) =>
        query (spec := (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
          (.inl (.inr qf))
    | .inr (.inr (.inl qu)) => unitImpl qu
    | .inr (.inr (.inr m)) =>
        query (spec := (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
          (.inr m)

/-- M5 — the canonical coin realization of the `𝒰(Σ)` oracle: answer each `Unit →ₒ U` query
by uniform sampling from the witness's private `unifSpec` coins. -/
noncomputable def coinUnitImpl [SampleableType U] :
    QueryImpl (Unit →ₒ U)
      (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)) :=
  fun _ =>
    simulateQ
      (fun m =>
        (query (spec := (oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
          (.inr m)))
      ($ᵗ U)

omit [SpongeUnit U] [SpongeSize] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  codec [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec]
  [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- M5 — `coinUnitImpl` makes no FS-challenge queries. -/
lemma coinUnitImpl_challenge_budget [SampleableType U] (qu : Unit) :
    IsQueryBoundP
      (coinUnitImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (Salt := Salt) qu)
      (fun j => isFSChallengeCoinIdx j = true) 0 := by
  refine isQueryBoundP_simulateQ_of_step_zero _ fun m => ?_
  simp only [HasQuery.instOfMonadLift_query]
  exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isFSChallengeCoinIdx])

omit [SpongeUnit U] [SpongeSize] [VCVCompatible StmtIn]
  [∀ i, VCVCompatible (pSpec.Challenge i)] [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  codec [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]
  [HasMessageSize pSpec] [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
  [HasChallengeSize pSpec]
  [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]
  [∀ i, Fintype (pSpec.Challenge i)] [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- M5 — `coinUnitImpl` makes no shared-`oSpec` queries. -/
lemma coinUnitImpl_shared_budget [SampleableType U] [DecidableEq ι] (qu : Unit) (i : ι) :
    IsQueryBoundP
      (coinUnitImpl (oSpec := oSpec) (StmtIn := StmtIn) (pSpec := pSpec) (U := U)
        (Salt := Salt) qu)
      (fun j => isSharedCoinIdx i j = true) 0 := by
  refine isQueryBoundP_simulateQ_of_step_zero _ fun m => ?_
  simp only [HasQuery.instOfMonadLift_query]
  exact (isQueryBoundP_query_iff _ _ _).mpr (by simp [isSharedCoinIdx])

/-- M1b — the **witness** for the (salted) eager key lemma: `D2SAlgo^f(𝒜)` (CO25 §5.4
Items 1–6, `ProverTransform.d2sAlgo`) re-associated onto the coin-equipped witness spec,
with abort collapsed to a default output (F8). -/
noncomputable def simulatedProverSalted
    {T_H T_P : Type} [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)]
    (unitImpl : QueryImpl (Unit →ₒ U)
      (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)))
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) :
    OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)
      (StmtIn × FSSaltedProof pSpec Salt) :=
  (fun o => o.getD default) <$>
    simulateQ (simulatedProverImpl (oSpec := oSpec) (U := U) (pSpec := pSpec)
        (Salt := Salt) unitImpl)
      ((d2sAlgo (T_H := T_H) (T_P := T_P) (Salt := Salt) 𝒜).run)

/-- M1c residual interface — challenge budget of the witness (Lemma 5.1 conjunct (b)): the simulated
prover makes at most `θ★ = tₚ` FS-challenge queries, provided the malicious prover makes at
most `tₚ` forward-perm queries and the coin realization makes no challenge queries. This is
proven in `SimulatorBudgets` from F3b, F4, and the F5 bridge budget through the `d2fRaw`
`simulateQ` pipeline. -/
def SimulatedProverChallengeBudgetResidual
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)] : Prop :=
  ∀ (unitImpl : QueryImpl (Unit →ₒ U)
      (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)))
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) (tₕ tₚ tₚᵢ : ℕ),
    (∀ qu, IsQueryBoundP (unitImpl qu) (fun j => isFSChallengeCoinIdx j = true) 0) →
    IsQueryBoundP 𝒜
      (fun j => DuplexSpongeFS.dsQueryFlavor j = DuplexSpongeFS.DSQueryFlavor.perm) tₚ →
    IsQueryBoundP
      (simulatedProverSalted (T_H := T_H) (T_P := T_P) (Salt := Salt) unitImpl 𝒜)
      (fun j => isFSChallengeCoinIdx j = true)
      (θStar tₕ tₚ tₚᵢ)

/-- M1d residual interface — shared budget of the witness (Lemma 5.1 conjunct (a)): `oSpec`
queries are forwarded 1:1 (`QueryImpl.id` summand of `d2fOuterImpl`), provided the coin
realization makes no shared queries. This is proven in `SimulatorBudgets` from F3b and F4b. -/
def SimulatedProverSharedBudgetResidual [DecidableEq ι]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U]
    [Inhabited (StmtIn × FSSaltedProof pSpec Salt)] : Prop :=
  ∀ (unitImpl : QueryImpl (Unit →ₒ U)
      (OracleComp ((oSpec + fsChallengeOracle (StmtIn × Salt) pSpec) + unifSpec)))
    (𝒜 : MaliciousProver oSpec pSpec StmtIn U δ) (tₒ : ι → ℕ),
    (∀ qu i, IsQueryBoundP (unitImpl qu) (fun j => isSharedCoinIdx i j = true) 0) →
    (∀ i, IsQueryBoundP 𝒜 (fun j => j.getLeft? = some i) (tₒ i)) →
    ∀ i, IsQueryBoundP
      (simulatedProverSalted (T_H := T_H) (T_P := T_P) (Salt := Salt) unitImpl 𝒜)
      (fun j => isSharedCoinIdx i j = true) (tₒ i)

end Witness

/-- R4 residual — **the research core**: the full quantified CO25 Lemma 5.1 on the eager
surface with the canonical oracle distributions (uniform FS challenge functions, `D_DS`
random function + permutation). Proving it requires the resurrected Hyb₀–Hyb₄ ladder,
Claims 5.21–5.24 (R1: the Lemma 5.8 birthday bound, R2: the StdTrace/D2SQuery coupling off
`E`, R3: the verifier-replay analysis), the §5.7 abort analysis, and assembly via
`tvDist_chain4` + `claimSum_le_ηStarPaper`. -/
def KeyLemmaEagerResidual
    [DecidableEq ι] [SampleableType U]
    [SampleableType (OracleFamily (fsChallengeOracle StmtIn pSpec))]
    [SampleableType (StmtIn → Vector U SpongeSize.C)]
    [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] (δ : ℕ)
    (oImpl : QueryImpl oSpec ProbComp) : Prop :=
  ∀ (V : Verifier oSpec StmtIn StmtOut pSpec)
    (P : OracleComp (oSpec + duplexSpongeChallengeOracle StmtIn U)
      (StmtIn × pSpec.Messages))
    (tₒ : ι → ℕ) (tₕ tₚ tₚᵢ L : ℕ),
    pSpec.totalNumPermQueries ≤ L →
    (∀ i : ι, IsQueryBoundP P (fun j => j.getLeft? = some i) (tₒ i)) →
    IsQueryBoundP P
      (fun j => DuplexSpongeFS.dsQueryFlavor j = DuplexSpongeFS.DSQueryFlavor.hash) tₕ →
    IsQueryBoundP P
      (fun j => DuplexSpongeFS.dsQueryFlavor j = DuplexSpongeFS.DSQueryFlavor.perm) tₚ →
    IsQueryBoundP P
      (fun j => DuplexSpongeFS.dsQueryFlavor j = DuplexSpongeFS.DSQueryFlavor.permInv) tₚᵢ →
    KeyLemmaStatementEager (T_H := T_H) (T_P := T_P) (oSpec := oSpec) (StmtOut := StmtOut) δ
      (OracleDistribution.uniform (fsChallengeOracle StmtIn pSpec))
      (D_DS StmtIn U) oImpl V P tₒ tₕ tₚ tₚᵢ L

end EagerSurface

/-! ## F4 residual interfaces — §5.4 dispatcher per-step budgets -/

section DispatcherBudgetResiduals

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn] [DecidableEq U] [Fintype U]
  [codec : Codec pSpec U] {δ : ℕ}
  [∀ i, Fintype (pSpec.Message i)] [∀ i, DecidableEq (pSpec.Message i)]

/-- F4 residual interface — per-step `gᵢ`-budget of the §5.4 dispatcher:
`d2sQueryStep` makes at most one `gSpec` query, and only on a forward-perm query
(CO25 §5.4 Item 4(e)i); the hash/permInv/no-result branches make none. Proven in
`SimulatorBudgets` by unfolding the five-handler branch tree (including the `𝒰(Σ)`-sampler
helpers) through the `StateT`/`OptionT` runs. -/
def D2sQueryStepGSpecBudgetResidual
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] : Prop :=
  ∀ (qq : (duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U)),
    IsQueryBoundP
      (((d2sQueryStep (δ := δ) (T_H := T_H) (T_P := T_P)
          (StmtIn := StmtIn) (pSpec := pSpec) (U := U) qq).run st).run)
      (fun j => j.isLeft = true)
      (match qq with | .inr (.inl _) => 1 | _ => 0)

/-- F4b residual interface — shared-budget forwarding of the composed outer implementation:
per source query, `d2fOuterImpl` makes at most one `oSpec` query at index `i`, and only when
the source query itself is the `oSpec` query at `i` (the `QueryImpl.id` summand forwards 1:1;
the duplex-sponge summand lands in a spec without `oSpec`). Proven in `SimulatorBudgets` from
the explicit `addLift` run-shapes plus the F4 branch-tree analysis. -/
def D2fOuterImplSharedBudgetResidual [DecidableEq ι]
    (T_H T_P : Type) [LawfulTraceNablaImpl T_H T_P StmtIn U] : Prop :=
  ∀ {κ : Type} (challengeSpec : OracleSpec κ) (M : Type)
    (gImpl : GImpl (U := U) (StmtIn := StmtIn) (pSpec := pSpec) (δ := δ) challengeSpec M)
    (t : (oSpec + duplexSpongeChallengeOracle StmtIn U).Domain)
    (st : D2SQueryState (δ := δ) (T_H := T_H) (T_P := T_P)
      (StmtIn := StmtIn) (pSpec := pSpec) (U := U))
    (m : M) (i : ι),
    IsQueryBoundP
      ((((d2fOuterImpl (oSpec := oSpec) (T_H := T_H) (T_P := T_P) gImpl t).run st).run m).run)
      (fun j => j.getLeft? = some i)
      (if t.getLeft? = some i then 1 else 0)

end DispatcherBudgetResiduals

#print axioms DuplexSpongeFS.KeyLemmaFoundations.tvDist_chain4
#print axioms DuplexSpongeFS.KeyLemmaFoundations.isQueryBoundP_deAbort
#print axioms DuplexSpongeFS.KeyLemmaFoundations.tvDist_deAbort_le_probFailure
#print axioms DuplexSpongeFS.KeyLemmaFoundations.ηStar_le_ηStarPaper
#print axioms DuplexSpongeFS.KeyLemmaFoundations.claimSum_le_ηStarPaper
#print axioms DuplexSpongeFS.KeyLemmaFoundations.isQueryBoundP_simulateQ_stateT_optionT_of_step
#print axioms DuplexSpongeFS.KeyLemmaFoundations.isQueryBoundP_simulateQ_stateT2_optionT_of_step
#print axioms DuplexSpongeFS.KeyLemmaFoundations.isQueryBoundP_elimM
#print axioms DuplexSpongeFS.KeyLemmaFoundations.isQueryBoundP_simulateQ_of_step_zero
#print axioms DuplexSpongeFS.KeyLemmaFoundations.lookupD2SAlgoMemo_insert_self_of_none
#print axioms DuplexSpongeFS.KeyLemmaFoundations.lookupD2SAlgoMemo_insert_stable
#print axioms DuplexSpongeFS.KeyLemmaFoundations.projectSharedQueryLog_append
#print axioms DuplexSpongeFS.KeyLemmaFoundations.projectSharedQueryLogSalted_append
#print axioms DuplexSpongeFS.KeyLemmaFoundations.uniformDeserializePreimage_left_budget
#print axioms DuplexSpongeFS.KeyLemmaFoundations.d2sCodecBridgeImpl_run_left_budget
#print axioms DuplexSpongeFS.KeyLemmaFoundations.d2sCodecBridgeImplMemo_challenge_budget
#print axioms DuplexSpongeFS.KeyLemmaFoundations.projectLeftQueryLog_append
#print axioms DuplexSpongeFS.KeyLemmaFoundations.coinUnitImpl_challenge_budget
#print axioms DuplexSpongeFS.KeyLemmaFoundations.coinUnitImpl_shared_budget

end DuplexSpongeFS.KeyLemmaFoundations
