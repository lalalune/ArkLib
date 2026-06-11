/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Security.LogupCompletenessClose
import ArkLib.ProofSystem.Logup.Security.SumcheckCompletenessUncond
import ArkLib.OracleReduction.Composition.Sequential.AppendSeamBridges3
import ArkLib.OracleReduction.Composition.Sequential.AppendToVerifierKeystone

/-!
# LogUp Protocol 2 — wiring the proven completeness keystones (issue #13)

This file discharges the LogUp Protocol 2 `AppendCompletenessResidual` — the **non-perfect**
(error-bearing) sequential-composition completeness brick — using two now-proven, axiom-clean
keystones already on `main`:

* `Reduction.append_completeness_msg` (`AppendSeamBridges3.lean`) — the **plain `Reduction`-level**
  non-perfect message-seam append completeness: from component completenesses `R₁ … e₁`, `R₂ … e₂`,
  the appended reduction is complete with error `e₁ + e₂`, given the message-seam direction facts and
  the honest-implementation side conditions (`hInit` + the `himplSP/himplNF/himplVB` triple).

* `OracleReduction.appendToReductionResidual_proof` (`AppendToVerifierKeystone.lean`) — the
  **unconditional** verifier-fusion bridge `(R₁.append R₂).toReduction =
  R₁.toReduction.append R₂.toReduction`.

## The oracle-vs-plain situation (resolved, not faked)

`AppendCompletenessResidual` is **oracle-level**: it unfolds (by
`OracleReduction.appendCompletenessResidual` and `OracleReduction.completeness`) to
`Reduction.completeness … (outer.append sumcheck).toReduction …`. The proven non-perfect append
keystone `Reduction.append_completeness_msg` is **plain `Reduction`-level**.

The two are bridged honestly by the proven `appendToReductionResidual_proof`, which rewrites
`(R₁.append R₂).toReduction` to `R₁.toReduction.append R₂.toReduction` **on the nose** (it is `rfl`-up-to
the verifier fusion, proven unconditionally in-tree). Crucially, the component completenesses match by
*definition*: `OracleReduction.completeness … Rᵢ eᵢ` **is** `Reduction.completeness … Rᵢ.toReduction eᵢ`
(see `OracleReduction.completeness` in `Security/Basic.lean`), so `hOuter`/`hSumcheck` feed straight
into `Reduction.append_completeness_msg` with no coercion. There is therefore **no genuine
oracle-vs-plain mismatch** for the non-perfect append: the perfect-completeness keystone
`OracleReduction.append_perfectCompleteness_msg_proof` is built the same way, and we build its
non-perfect analogue here.

## What is proven (no `sorry`, no new axioms)

* `OracleReduction.append_completeness_msg_proof` — the **general** oracle-level non-perfect
  message-seam append completeness keystone (the error-bearing analogue of the in-tree
  `append_perfectCompleteness_msg_proof`), with the verifier-fusion bridge discharged *internally*
  via `appendToReductionResidual_proof`. New, reusable.

* `Logup.appendCompletenessResidual_wired` — the LogUp `AppendCompletenessResidual` discharged from
  that keystone, taking the **two genuine remaining inputs** as explicit, consumer-supplied
  hypotheses: the embedded-sumcheck completeness (`hSumcheck`, blocked upstream by the missing
  generic `Sumcheck.Spec` completeness) and the honest-implementation side conditions
  (`hInit`/`himplSP`/`himplNF`/`himplVB`, vacuous when `oSpec = []ₒ`, supplied by every honest
  interactive implementation). The message-seam direction facts are structural
  (discharged from `0 < n` by `LogupSoundnessMsgSeam.lean`).

* `Logup.logup_completeness_wired` — the **end-to-end** LogUp completeness, with the outer half
  discharged in-tree by `outerCompletenessResidual_of_neverFail` and the append half discharged by
  `appendCompletenessResidual_wired`. The **only** remaining input is the embedded-sumcheck
  completeness `hSumcheck`.

This strictly improves on `LogupCompletenessClose.lean`: there, the `AppendCompletenessResidual`
remained an explicit hypothesis (its historical "perfect special case" discharge was vacuous —
`logupCompletenessError F n = 0` is impossible by `logupCompletenessError_ne_zero` — and has been
deleted). Here it is discharged for the **actual non-zero error** `logupCompletenessError F n`,
carrying the outer pole-rejection error through the composition — which is exactly the wall that
file flagged as remaining.

The axiom audit at the bottom confirms axiom-cleanliness (`propext`, `Classical.choice`, `Quot.sound`;
no `sorryAx`).
-/

open scoped NNReal ENNReal
open OracleComp OracleSpec ProtocolSpec

namespace OracleReduction

section NonPerfectKeystone

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
    {m n : ℕ}
    {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

/-- **Oracle-level non-perfect append completeness keystone (message seam) — verifier bridge
discharged internally.**

The *error-bearing* analogue of `append_perfectCompleteness_msg_proof`: from the two component
oracle-reduction completenesses `h₁ : R₁.completeness … e₁`, `h₂ : R₂.completeness … e₂`, the appended
oracle reduction `R₁.append R₂` is complete with additive error `e₁ + e₂`, given the message-seam
direction facts and the honest-implementation side conditions.

The verifier-fusion bridge `appendToReductionResidual` is supplied **internally** by the proven
`appendToReductionResidual_proof`, so no `hBridge` hypothesis remains. The proof is a pure
pass-through: `OracleReduction.completeness … R e` is **definitionally** `Reduction.completeness …
R.toReduction e`, the bridge rewrites `(R₁.append R₂).toReduction` to
`R₁.toReduction.append R₂.toReduction`, and the component completenesses `h₁`/`h₂` are *already*
`Reduction.completeness` of `Rᵢ.toReduction` by the same definitional unfolding, so they feed straight
into the proven `Reduction.append_completeness_msg`. -/
theorem append_completeness_msg_proof
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {e₁ e₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ e₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ e₂)
    (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (⟨m, by omega⟩ : Fin (m + n)) = .P_to_V)
    (hDir₂ : pSpec₂.dir (⟨0, hn⟩ : Fin n) = .P_to_V)
    (hInit : Pr[⊥ | init] = 0)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (R₁.append R₂).completeness init impl rel₁ rel₃ (e₁ + e₂) := by
  -- `OracleReduction.completeness … R e` is by definition `Reduction.completeness … R.toReduction e`.
  change Reduction.completeness init impl rel₁ rel₃ (R₁.append R₂).toReduction (e₁ + e₂)
  -- Discharge the verifier-fusion bridge internally with the proven unconditional residual proof.
  rw [show (R₁.append R₂).toReduction = R₁.toReduction.append R₂.toReduction from
    appendToReductionResidual_proof R₁ R₂]
  -- The component completenesses are already `Reduction.completeness` of the `toReduction`s, so feed
  -- them straight into the proven plain-level non-perfect message-seam append completeness.
  exact Reduction.append_completeness_msg R₁.toReduction R₂.toReduction h₁ h₂ hn hDir hDir₂
    hInit himplSP himplNF himplVB

end NonPerfectKeystone

end OracleReduction

open scoped NNReal ENNReal
open OracleComp OracleSpec

namespace Logup

section Wired

variable {ι : Type} (oSpec : OracleSpec ι)
variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [Fact ((-1 : F) ≠ 1)]
  [SampleableType F]
variable (n M : ℕ)
variable (params : ProtocolParams M)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- `F` is inhabited (by `0`), needed to synthesize the outer-phase challenge `SampleableType`
instances when naming the sub-phase obligations. -/
local instance instInhabitedFieldLogupWired : Inhabited F := ⟨0⟩

variable [oSpec.Fintype] [oSpec.Inhabited]

/-- **LogUp `AppendCompletenessResidual` discharged for the general (non-zero) error.**

Here the residual is discharged for the **actual** LogUp error `logupCompletenessError F n`
(= `|Hypercube n| / |F|`, non-zero over a finite field — `logupCompletenessError_ne_zero`, which is
why the historical perfect-special-case lemma was vacuous and is gone), carrying the outer
pole-rejection error through the composition.

The proof feeds the in-tree outer completeness (`outerCompletenessResidual_of_neverFail`, error
`logupCompletenessError F n`) and the embedded-sumcheck completeness `hSumcheck` (error `0`) into the
new oracle-level non-perfect keystone `OracleReduction.append_completeness_msg_proof`, whose verifier
bridge is discharged internally. The error reconciles `logupCompletenessError F n + 0 =
logupCompletenessError F n` via the `appendCompletenessResidual` definition.

The remaining inputs are exactly the consumer-supplied honest-implementation side conditions
(`hInit`, `himplSP`, `himplNF`, `himplVB` — vacuous when `oSpec = []ₒ`) and the structural
message-seam direction facts (`hn`, `hDir`, `hDir₂`), identical to those the perfect case already
takes. -/
theorem appendCompletenessResidual_wired
    (hInit : NeverFail init)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hn : 0 < Fin.vsum (fun _ : Fin n => 2))
    (hDir :
      (pSpec F n M params).dir (⟨4, by
        change 4 < 4 + Fin.vsum (fun _ : Fin n => 2); omega⟩ :
          Fin (4 + Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (hDir₂ : (logupSumcheckPSpec F n M params).dir (⟨0, hn⟩ :
        Fin (Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    AppendCompletenessResidual oSpec F n M params init impl
      (outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit) hSumcheck := by
  -- The outer half is the in-tree proven completeness at error `logupCompletenessError F n`.
  have hOuter :
      (outerOracleReduction oSpec F n M params).completeness init impl
        (inputRelation F n M) (midRelation F n M params) (logupCompletenessError F n) :=
    outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit
  -- The sumcheck half is completeness at error `0` (definitional).
  have hSum :
      (sumcheckOracleReduction oSpec F n M params).completeness init impl
        (midRelation F n M params) outputRelation 0 := hSumcheck
  -- Apply the oracle-level non-perfect message-seam keystone (bridge discharged internally).
  have hApp :
      (OracleReduction.append (outerOracleReduction oSpec F n M params)
          (sumcheckOracleReduction oSpec F n M params)).completeness init impl
        (inputRelation F n M) outputRelation (logupCompletenessError F n + 0) :=
    OracleReduction.append_completeness_msg_proof.{0, 0}
      (outerOracleReduction oSpec F n M params)
      (sumcheckOracleReduction oSpec F n M params)
      hOuter hSum hn hDir hDir₂ (probFailure_eq_zero' hInit) himplSP himplNF himplVB
  -- `AppendCompletenessResidual … = (outer.append sumcheck).completeness … (logupErr + 0)`.
  unfold AppendCompletenessResidual OracleReduction.appendCompletenessResidual
  exact hApp

/-- **End-to-end LogUp Protocol 2 completeness — append discharged for the general error.**

The full LogUp oracle reduction is complete with error `logupCompletenessError F n`. The **outer**
pole-rejection half is the in-tree proven `outerCompletenessResidual_of_neverFail`; the
**append-composition** half is discharged here by `appendCompletenessResidual_wired` (general non-zero
error, via the proven non-perfect keystone). The **only** remaining input is the embedded-sumcheck
completeness `hSumcheck` (blocked upstream by the missing generic `Sumcheck.Spec` completeness + lens
`IsComplete` instance) plus the honest-implementation side conditions every interactive
implementation satisfies.

This carries the genuine non-zero error end-to-end (the historical perfect-special-case variant
hypothesized the impossible `logupCompletenessError F n = 0` and has been deleted). -/
theorem logup_completeness_wired
    (hInit : NeverFail init)
    (hSumcheck : SumcheckCompletenessResidual oSpec F n M params init impl)
    (hn : 0 < Fin.vsum (fun _ : Fin n => 2))
    (hDir :
      (pSpec F n M params).dir (⟨4, by
        change 4 < 4 + Fin.vsum (fun _ : Fin n => 2); omega⟩ :
          Fin (4 + Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (hDir₂ : (logupSumcheckPSpec F n M params).dir (⟨0, hn⟩ :
        Fin (Fin.vsum (fun _ : Fin n => 2))) = .P_to_V)
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    (logupOracleReduction oSpec F n M params).completeness init impl
      (inputRelation F n M) outputRelation (logupCompletenessError F n) :=
  logup_completeness_full oSpec F n M params init impl hInit hSumcheck
    (appendCompletenessResidual_wired oSpec F n M params init impl hInit hSumcheck
      hn hDir hDir₂ himplSP himplNF himplVB)

set_option maxHeartbeats 1000000 in
/-- **`LogupCompletenessBrickResidual` — fully discharged** (for `0 < n`, the nontrivial case):
the outer half is `outerCompletenessResidual_of_neverFail`, the sumcheck half is
`sumcheckCompletenessResidual_unconditional`, and the append brick is
`appendCompletenessResidual_wired` with the two seam-direction facts proven concretely (the
embedded sumcheck is message-leading: `Sumcheck.Spec.pSpec` is a `seqCompose` of
`[P_to_V, V_to_P]` rounds). -/
theorem logupCompletenessBrickResidual_holds
    [oSpec.Fintype] [oSpec.Inhabited]
    (hn : 0 < n) (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s)
        = support (liftM q : OracleComp oSpec β))
    (himplSP : ∀ (t : oSpec.Domain) (s : σ) (x : oSpec.Range t × σ),
      x ∈ support ((impl t).run s) → x.2 = s)
    (himplNF : ∀ (t : oSpec.Domain) (s : σ), Pr[⊥ | (impl t).run s] = 0)
    (himplVB : ∀ (t : oSpec.Domain) (s s' : σ),
      evalDist ((impl t).run' s) = evalDist ((impl t).run' s')) :
    LogupCompletenessBrickResidual oSpec F n M params init impl := by
  have hSum := sumcheckCompletenessResidual_unconditional oSpec F n M params init impl
    hInit hImplSupp
  obtain ⟨hpos, hdir⟩ := (ProtocolSpec.seqCompose_appendValid
    (pSpec := fun _ : Fin n =>
      Sumcheck.Spec.SingleRound.pSpec F (logupSumcheckDegree M params))
    (fun _ => ⟨by omega, rfl⟩)).resolve_left (by
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      rw [Fin.vsum_succ]; omega)
  refine ⟨outerCompletenessResidual_of_neverFail oSpec F n M params init impl hInit, hSum,
    appendCompletenessResidual_wired oSpec F n M params init impl hInit hSum hpos ?_ hdir
      himplSP himplNF himplVB⟩
  rw [show (⟨4, by change 4 < 4 + Fin.vsum (fun _ : Fin n => 2); omega⟩ :
        Fin (4 + Fin.vsum (fun _ : Fin n => 2)))
      = Fin.natAdd 4 ⟨0, hpos⟩ from by ext; simp]
  rw [Prover.append_dir_natAdd]
  exact hdir

end Wired

end Logup

/- Axiom audit. -/
#print axioms OracleReduction.append_completeness_msg_proof
#print axioms Logup.appendCompletenessResidual_wired
#print axioms Logup.logup_completeness_wired
#print axioms Logup.logupCompletenessBrickResidual_holds
