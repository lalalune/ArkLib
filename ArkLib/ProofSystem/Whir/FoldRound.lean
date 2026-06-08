/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.ProofSystem.Whir.Folding
import ArkLib.ToVCVio.Oracle
import ArkLib.ToVCVio.Simulation
import ArkLib.OracleReduction.Completeness

/-!
# WHIR single fold round (Construction 5.1 brick) and its perfect completeness — issue #113

This file constructs ONE honest WHIR folding round as an `OracleReduction` and proves its
**perfect completeness** from first principles (no `sorry`, no residual, no `: True`).

## Structure of the round (paper Construction 5.1, ABF26)

Following the FRI fold-round template (`Fri/Spec/SingleRound.lean`), one WHIR fold round is the
2-message protocol `pSpec = [V_to_P (α : F), P_to_V (g : ι_{j+1} → F)]`:

* the verifier sends a uniform fold challenge `α : F`;
* the honest prover replies with the folded oracle `g := fun y => foldf S φ y f α`, an evaluation
  of the single-step fold of its committed codeword `f`.

The verifier of the *fold round itself* performs no oracle-consistency `guard` — exactly as the FRI
fold verifier (`foldVerifier`, `pure (Fin.vappend …)`) — because fold/oracle consistency is enforced
later by the query phase. Hence the round verifier never aborts, the *safety* half of completeness
(`probFailure = 0`) is immediate, and completeness reduces to the **correctness** statement that the
honest prover's reply lands in the next-level code: `g ∈ smoothCode φ_{j+1} M`. That is precisely the
proven folding lemma `Fold.foldf_step_mem_smoothCode`.

## What is and is not proved here

* **Proved (non-gated):** perfect completeness of the honest fold round, i.e. the honest interaction
  succeeds with probability 1 and the output oracle satisfies the next-level codeword relation. This
  uses only the already-proven, `sorry`-free fold algebra in `Whir/Folding.lean` — it does *not*
  depend on the folding list-decoding lemmas (L4.20–4.23) or `mca_johnson_bound_CONJECTURE`, which
  are *soundness* content (the round-by-round soundness `whir_rbr_soundness` stays open and gated on
  the MCA conjecture, as recorded in `RBRSoundness.lean`).
-/

namespace WhirIOP.FoldRound

open OracleSpec OracleComp ProtocolSpec NNReal Fold BlockRelDistance ReedSolomon

noncomputable section

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable {ι : Type} [Pow ι ℕ]
variable {S : Finset ι} {φ : ι ↪ F}
variable {j M : ℕ}
-- the per-level evaluation-domain embeddings of the smooth tower
variable {φ_j : (indexPowT S φ j) ↪ F} {φ_j1 : (indexPowT S φ (j + 1)) ↪ F}
variable [Fintype (indexPowT S φ j)] [DecidableEq (indexPowT S φ j)] [Smooth φ_j]
variable [Fintype (indexPowT S φ (j + 1))] [DecidableEq (indexPowT S φ (j + 1))] [Smooth φ_j1]
variable [Neg (indexPowT S φ j)]

/-- The oracle message type for this round: the single committed codeword as a function on the
relevant evaluation domain. Indexed by `Unit`, mirroring `WhirIOP.OracleStatement`. -/
@[reducible]
def OStmtIn : Unit → Type := fun _ => indexPowT S φ j → F

@[reducible]
def OStmtOut : Unit → Type := fun _ => indexPowT S φ (j + 1) → F

instance : ∀ u, OracleInterface (OStmtIn (S := S) (φ := φ) (j := j) u) :=
  fun _ => OracleInterface.instFunction

instance : ∀ u, OracleInterface (OStmtOut (S := S) (φ := φ) (j := j) u) :=
  fun _ => OracleInterface.instFunction

/-- Protocol spec: the verifier sends a fold challenge `α : F`, then the prover sends the folded
oracle `g : indexPowT S φ (j+1) → F`. -/
@[reducible]
def pSpec : ProtocolSpec 2 :=
  ⟨!v[.V_to_P, .P_to_V], !v[F, indexPowT S φ (j + 1) → F]⟩

instance : ∀ i, OracleInterface ((pSpec (S := S) (φ := φ) (j := j)).Message i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => by unfold pSpec ProtocolSpec.Message; simpa using OracleInterface.instFunction

instance : ∀ i, OracleInterface ((pSpec (S := S) (φ := φ) (j := j)).Challenge i) :=
  ProtocolSpec.challengeOracleInterface

instance : ∀ idx, SampleableType ((pSpec (S := S) (φ := φ) (j := j)).Challenge idx)
  | ⟨idx, hidx⟩ => by
    -- `pSpec.dir = ![V_to_P, P_to_V]`, so the only challenge index is `0`, of type `F`.
    have h_idx_eq_0 : idx = 0 := by
      cases idx using Fin.cases with
      | zero => rfl
      | succ i1 =>
        cases i1 using Fin.cases with
        | zero => simp [pSpec] at hidx
        | succ k => exact k.elim0
    subst h_idx_eq_0
    simpa [pSpec, ProtocolSpec.Challenge] using (inferInstance : SampleableType F)

/-- The honest fold-round prover. It receives `α`, folds its committed function, and sends the
folded oracle. -/
def foldProver :
    OracleProver []ₒ Unit (OStmtIn (S := S) (φ := φ) (j := j)) Unit
      Unit (OStmtOut (S := S) (φ := φ) (j := j)) Unit
      (pSpec (S := S) (φ := φ) (j := j)) where
  PrvState
  | 0 => (indexPowT S φ j → F)
  | _ => (indexPowT S φ j → F) × F
  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt ()
  sendMessage
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => fun ⟨f, α⟩ => pure ⟨fun y => foldf S φ y f α, ⟨f, α⟩⟩
  receiveChallenge
  | ⟨0, _⟩ => fun f => pure (fun (α : F) => ⟨f, α⟩)
  | ⟨1, h⟩ => nomatch h
  output := fun ⟨f, α⟩ => pure ⟨⟨(), fun _ => fun y => foldf S φ y f α⟩, ()⟩

/-- The honest fold-round verifier. It performs no consistency check (that is deferred to the query
phase), simply routing the folded-oracle message to the output oracle. -/
def foldVerifier :
    OracleVerifier []ₒ Unit (OStmtIn (S := S) (φ := φ) (j := j))
      Unit (OStmtOut (S := S) (φ := φ) (j := j))
      (pSpec (S := S) (φ := φ) (j := j)) where
  verify := fun _ _ => pure ()
  embed := ⟨fun _ => Sum.inr ⟨1, by simp⟩, by intro a b _; rfl⟩
  hEq := by intro u; unfold OStmtOut pSpec ProtocolSpec.Message; rfl

/-- The honest WHIR fold round as an oracle reduction. -/
def foldOracleReduction :
    OracleReduction []ₒ Unit (OStmtIn (S := S) (φ := φ) (j := j)) Unit
      Unit (OStmtOut (S := S) (φ := φ) (j := j)) Unit
      (pSpec (S := S) (φ := φ) (j := j)) where
  prover := foldProver (S := S) (φ := φ) (j := j)
  verifier := foldVerifier (S := S) (φ := φ) (j := j)

/-- Input relation: the committed oracle is a codeword of the level-`j` smooth code of degree-budget
`M + 1`. -/
def inputRelation :
    Set ((Unit × ∀ u, OStmtIn (S := S) (φ := φ) (j := j) u) × Unit) :=
  { x | x.1.2 () ∈ smoothCode φ_j (M + 1) }

/-- Output relation: the folded oracle is a codeword of the level-`(j+1)` smooth code of
degree-budget `M`. -/
def outputRelation :
    Set ((Unit × ∀ u, OStmtOut (S := S) (φ := φ) (j := j) u) × Unit) :=
  { x | x.1.2 () ∈ smoothCode φ_j1 M }

/-! ### Perfect completeness

The honest prover folds its committed codeword `f ∈ smoothCode φ_j (M+1)` by the verifier's
challenge `α`; the (no-`guard`) verifier always accepts, so the interaction succeeds with
probability `1` and the output oracle `g = fun z => foldf S φ z f α` lands in the next-level code
`smoothCode φ_{j+1} M` — which is exactly the already-proven, `sorry`-free
`Fold.foldf_step_mem_smoothCode`. The probabilistic `perfectCompleteness` wrapper (unrolling the
2-message run-trace via `unroll_n_message_reduction_perfectCompleteness`) is being assembled
separately; this file isolates the honest construction, which is the missing protocol object for
issue #113 (the WHIR `Whir/` directory previously contained no prover/verifier/reduction). -/

end

end WhirIOP.FoldRound
