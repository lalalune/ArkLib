import ArkLib.Data.CodingTheory.InterleavedCode

open InterleavedCode

lemma minDist_eq_minDist {F A ι κ : Type*} [Semiring F] [AddCommMonoid A] [Module F A]
    [Fintype ι] [Fintype κ] [Nonempty κ] [DecidableEq A] (C : Set (ι → A)) :
    Code.minDist (C^⋈κ) = Code.minDist C := by
  sorry
