import ArkLib.Data.CodingTheory.InterleavedCode

open scoped NNReal ENNReal BigOperators
open Code

/-- Projection: the relative distance of a single row to `C` is at most the relative distance of the
interleaved word to the interleaved code.  (Heart of `jointProximity → δᵣ(row,C) ≤ δ` for DG25 L4.19.) -/
lemma relDistFromCode_row_le_interleaved {κ ι A : Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
    [DecidableEq A] (C : Set (ι → A)) (u : Matrix κ ι A) (k : κ) :
    relDistFromCode (u k) C ≤ relDistFromCode (Matrix.transpose u) (interleavedCodeSet C) := by
  unfold relDistFromCode
  apply sInf_le_sInf
  rintro d ⟨V, hVmem, hVle⟩
  refine ⟨Matrix.transpose V k, hVmem k, ?_⟩
  refine le_trans ?_ hVle
  have hproj : hammingDist (u k) (Matrix.transpose V k)
      ≤ hammingDist (Matrix.transpose u) V := by
    have h := hammingDist_comp_le_hammingDist (fun (_ : ι) (col : κ → A) => col k)
                (x := Matrix.transpose u) (y := V)
    simpa [Matrix.transpose_apply] using h
  have hrel : relHammingDist (u k) (Matrix.transpose V k)
      ≤ relHammingDist (Matrix.transpose u) V := by
    unfold relHammingDist
    gcongr
    exact_mod_cast hproj
  exact_mod_cast hrel
