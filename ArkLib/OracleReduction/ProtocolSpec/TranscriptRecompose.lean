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
