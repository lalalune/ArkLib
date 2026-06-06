/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.Composition.Sequential.General

/-!
# n-ary `Verifier.seqCompose` (knowledge) soundness reduces to the binary `append` keystone (#25)

Companion to the `Reduction.seqCompose_{perfectCompleteness,completeness}_of_append` bricks in
`General.lean`. These discharge the residualized n-ary `Verifier.seqCompose` soundness / knowledge
soundness (which assume their own conclusion) by **induction on `m`**, reducing each to the binary
`Verifier.append` statement supplied as an explicit `hAppend` hypothesis:

* `Verifier.seqCompose_soundness_of_append`
* `Verifier.seqCompose_knowledgeSoundness_of_append`

Each unfolds `seqCompose` to a binary `append` (`seqCompose_succ`), splits the additive error with
`Fin.sum_univ_succ`, applies `hAppend` + the IH, and closes the base case with the identity verifier
(`Verifier.id_soundness` / `Verifier.id_knowledgeSoundness`, with `Fin.last 0 = 0`). So once the
binary `Verifier.append_soundness` / `append_knowledgeSoundness` keystones (`Append.lean`) are proved
unconditionally, feeding them as `hAppend` collapses the n-ary residuals automatically.

Kept in a separate file (additive) so it composes cleanly with the heavily-edited `General.lean`.
-/

open ProtocolSpec OracleComp
open scoped NNReal

universe u v

variable {ι : Type} {oSpec : OracleSpec ι}
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

namespace Verifier

/-- **n-ary `Verifier.seqCompose` soundness reduces to the binary `append` keystone.** -/
theorem seqCompose_soundness_of_append {m : ℕ}
    (Stmt : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (soundnessError : Fin m → ℝ≥0)
    (hAppend : ∀ {S₁ S₂ S₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {l₁ : Set S₁} {l₂ : Set S₂} {l₃ : Set S₃} {e₁ e₂ : ℝ≥0},
        V₁.soundness init impl l₁ l₂ e₁ → V₂.soundness init impl l₂ l₃ e₂ →
        (V₁.append V₂).soundness init impl l₁ l₃ (e₁ + e₂))
    (h : ∀ i, (V i).soundness init impl (lang i.castSucc) (lang i.succ) (soundnessError i)) :
    (Verifier.seqCompose Stmt V).soundness init impl (lang 0) (lang (Fin.last m))
      (∑ i, soundnessError i) := by
  induction m with
  | zero =>
    rw [Verifier.seqCompose_zero, Fin.sum_univ_zero]
    change (Verifier.id : Verifier oSpec (Stmt 0) (Stmt 0) !p[]).soundness
      init impl (lang 0) (lang 0) 0
    exact Verifier.id_soundness init impl
  | succ m ih =>
    rw [Verifier.seqCompose_succ, Fin.sum_univ_succ]
    exact hAppend (V 0) _ (h 0)
      (ih (Stmt ∘ Fin.succ) (fun i => lang (Fin.succ i)) (fun i => V (Fin.succ i))
        (fun i => soundnessError (Fin.succ i)) (fun i => h (Fin.succ i)))

/-- **n-ary `Verifier.seqCompose` knowledge soundness reduces to the binary `append` keystone.** -/
theorem seqCompose_knowledgeSoundness_of_append {m : ℕ}
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, SampleableType ((pSpec i).Challenge j)]
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (knowledgeError : Fin m → ℝ≥0)
    (hAppend : ∀ {S₁ W₁ S₂ W₂ S₃ W₃ : Type} {k₁ k₂ : ℕ}
        {p₁ : ProtocolSpec k₁} {p₂ : ProtocolSpec k₂}
        [∀ j, SampleableType (p₁.Challenge j)] [∀ j, SampleableType (p₂.Challenge j)]
        (V₁ : Verifier oSpec S₁ S₂ p₁) (V₂ : Verifier oSpec S₂ S₃ p₂)
        {r₁ : Set (S₁ × W₁)} {r₂ : Set (S₂ × W₂)} {r₃ : Set (S₃ × W₃)} {e₁ e₂ : ℝ≥0},
        V₁.knowledgeSoundness init impl r₁ r₂ e₁ → V₂.knowledgeSoundness init impl r₂ r₃ e₂ →
        (V₁.append V₂).knowledgeSoundness init impl r₁ r₃ (e₁ + e₂))
    (h : ∀ i, (V i).knowledgeSoundness init impl (rel i.castSucc) (rel i.succ) (knowledgeError i)) :
    (Verifier.seqCompose Stmt V).knowledgeSoundness init impl (rel 0) (rel (Fin.last m))
      (∑ i, knowledgeError i) := by
  induction m with
  | zero =>
    rw [Verifier.seqCompose_zero, Fin.sum_univ_zero]
    change (Verifier.id : Verifier oSpec (Stmt 0) (Stmt 0) !p[]).knowledgeSoundness
      init impl (rel 0) (rel 0) 0
    exact Verifier.id_knowledgeSoundness init impl
  | succ m ih =>
    rw [Verifier.seqCompose_succ, Fin.sum_univ_succ]
    exact hAppend (V 0) _ (h 0)
      (ih (Stmt ∘ Fin.succ) (Wit ∘ Fin.succ) (fun i => rel (Fin.succ i)) (fun i => V (Fin.succ i))
        (fun i => knowledgeError (Fin.succ i)) (fun i => h (Fin.succ i)))

end Verifier
