/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.ProtocolSpec.SeqCompose

/-!
# Transcript recomposition for sequentially-composed protocols

The inverse of `FullTranscript.append_fst` / `append_snd`: splitting an appended-protocol full
transcript into its two halves and re-appending recovers the original. Useful for the right-block
run characterization of `Prover.append_run` (reconciling the appended transcript with
`transcript₁ ++ₜ transcript₂`).
-/

open ProtocolSpec

namespace ProtocolSpec.FullTranscript

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- **Transcript recomposition**: splitting an appended-protocol transcript into its two halves and
re-appending recovers it (inverse of `append_fst` / `append_snd`). -/
theorem fst_append_snd (T : FullTranscript (pSpec₁ ++ₚ pSpec₂)) : T.fst ++ₜ T.snd = T := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [append, fst, Fin.happend_left]
  · simp [append, snd, Fin.happend_right]

end ProtocolSpec.FullTranscript

#print axioms ProtocolSpec.FullTranscript.fst_append_snd

namespace ProtocolSpec.Transcript

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Append a full `pSpec₁` transcript and a *partial* `pSpec₂` transcript into a partial transcript
for the concatenated protocol — the right-block analogue of the partial `fst`/`snd` projections,
needed to state the right-block run characterization of `Prover.append_run` (#13). -/
def appendRight (T₁ : FullTranscript pSpec₁) {k : Fin (n + 1)} (T₂ : pSpec₂.Transcript k) :
    (pSpec₁ ++ₚ pSpec₂).Transcript ⟨m + k.val, by omega⟩ :=
  fun i =>
    if hi : i.val < m then
      cast (Fin.vappend_left_of_lt pSpec₁.Type pSpec₂.Type ⟨i.val, by omega⟩ hi).symm
        (T₁ ⟨i.val, hi⟩)
    else
      have hi2 : i.val - m < k.val := by have := i.isLt; simp only [Fin.val_mk] at this; omega
      cast (Fin.vappend_right_of_not_lt pSpec₁.Type pSpec₂.Type ⟨i.val, by omega⟩ hi).symm
        (T₂ ⟨i.val - m, hi2⟩)

end ProtocolSpec.Transcript

#check @ProtocolSpec.Transcript.appendRight
