import ArkLib.Data.CodingTheory.InterleavedCode

open ListDecodable Code InterleavedCode

namespace GGRScratch

variable {ι F : Type} [Fintype ι] [Field F] [DecidableEq F]

set_option maxHeartbeats 800000

-- hammingDist value is independent of the DecidableEq instance (it is a Subsingleton).
example (a b : ι → F) (i1 i2 : DecidableEq F) :
    @hammingDist ι (fun _ => F) a b = @hammingDist ι (fun _ => F) a b := rfl

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
lemma transpose_mem_closeCodewordsRel [Nonempty ι] {m : ℕ} [DecidableEq (Fin m → F)]
    {C : Set (ι → F)} {δ : ℝ}
    (f : Matrix ι (Fin m) F) {V : Matrix ι (Fin m) F}
    (hV : V ∈ closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ) (k : Fin m) :
    V.transpose k ∈ closeCodewordsRel C (f.transpose k) δ := by
  obtain ⟨hmem, hball⟩ := hV
  refine ⟨hmem k, ?_⟩
  simp only [relHammingBall, Set.mem_setOf_eq] at hball ⊢
  -- The relHammingDist value is independent of the DecidableEq instance.
  have hball' : (δᵣ(f, V) : ℝ) ≤ δ := by
    rw [Subsingleton.elim (fun a b => Classical.propDecidable (a = b)) (by infer_instance)] at hball
    exact hball
  have hcomm : ∀ (a b : ι → F), (δᵣ(a, b) : ℝ) = (δᵣ(b, a) : ℝ) := by
    intro a b; unfold relHammingDist; rw [hammingDist_comm]
  have key : (δᵣ(f.transpose k, V.transpose k) : ℝ) ≤ δ := by
    calc (δᵣ(f.transpose k, V.transpose k) : ℝ)
        = (δᵣ(V.transpose k, f.transpose k) : ℝ) := hcomm _ _
      _ ≤ (δᵣ(V, f) : ℝ) := by exact_mod_cast relHammingDist_transpose_le f V k
      _ = (δᵣ(f, V) : ℝ) := hcomm _ _
      _ ≤ δ := hball'
  rw [Subsingleton.elim (fun a b => Classical.propDecidable (a = b)) (by infer_instance)]
  exact key

end GGRScratch
