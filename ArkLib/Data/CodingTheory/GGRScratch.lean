import ArkLib.Data.CodingTheory.InterleavedCode

open ListDecodable Code InterleavedCode

namespace GGRScratch

variable {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]

-- Column projection shrinks relative Hamming distance.
lemma relHammingDist_transpose_le [Nonempty ι] {m : ℕ} (f V : Matrix ι (Fin m) F) (k : Fin m) :
    δᵣ(V.transpose k, f.transpose k) ≤ δᵣ(V, f) := by
  unfold relHammingDist
  have h : hammingDist (V.transpose k) (f.transpose k) ≤ hammingDist V f := by
    have := hammingDist_comp_le_hammingDist (γ := fun _ : ι => Fin m → F)
      (β := fun _ : ι => F) (fun (_ : ι) (row : Fin m → F) => row k) (x := V) (y := f)
    simpa [Matrix.transpose] using this
  gcongr

-- A close interleaved codeword projects, column-wise, to a close codeword of C.
lemma transpose_mem_closeCodewordsRel [Nonempty ι] {m : ℕ} {C : Set (ι → F)} {δ : ℝ}
    (f : Matrix ι (Fin m) F) {V : Matrix ι (Fin m) F}
    (hV : V ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ) (k : Fin m) :
    V.transpose k ∈ closeCodewordsRel C (f.transpose k) δ := by
  obtain ⟨hmem, hball⟩ := hV
  refine ⟨hmem k, ?_⟩
  rw [relHammingBall, Set.mem_setOf_eq] at hball ⊢
  calc (δᵣ(f.transpose k, V.transpose k) : ℝ)
      = (δᵣ(V.transpose k, f.transpose k) : ℝ) := by rw [relHammingDist_comm]
    _ ≤ (δᵣ(V, f) : ℝ) := by exact_mod_cast relHammingDist_transpose_le f V k
    _ = (δᵣ(f, V) : ℝ) := by rw [relHammingDist_comm]
    _ ≤ δ := hball

end GGRScratch
