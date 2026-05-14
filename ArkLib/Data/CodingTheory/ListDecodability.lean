/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import Mathlib.InformationTheory.Hamming
import Mathlib.Analysis.Normed.Field.Lemmas
import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
/-! # List Decodability -/


namespace ListDecodable

section

variable {ι : Type*} [Fintype ι]
         {F : Type*}

abbrev Code.{u, v} (ι : Type u) (S : Type v) : Type (max u v) := Set (ι → S)

open Classical in
/-- Hamming ball of radius `r` centred at a word `y`. -/
def hammingBall (y : ι → F) (r : ℕ) : Set (ι → F) :=
  {x | hammingDist y x ≤ r}

open Classical in
/-- Ball of radius `r` centred at a word `y` with respect to the relative Hamming distance. -/
def relHammingBall (y : ι → F) (r : ℝ) : Set (ι → F) :=
  {x | Code.relHammingDist y x ≤ r}

/-- The set of `r`-close codewords to a given word `y` with respect to the Hamming distance. -/
def closeCodewords (C : Code ι F) (y : ι → F) (r : ℕ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ hammingBall y r}

/-- The set of `r`-close codewords to a given word `y` with respect to the relative Hamming
distance.
Note that this is exactly `Λ (C, y, r)` from [ACFY24] and ` List (C, y, r)` from [ACFY24stir]. -/
def closeCodewordsRel (C : Code ι F) (y : ι → F) (r : ℝ) : Set (ι → F) :=
  {c | c ∈ C ∧ c ∈ relHammingBall y r}

/-- A code `C` is `(r,ℓ)`-list decodable.

- Remark:
   Note that the number of codewords `ℓ` in the Hamming ball of radius `r`
   centred around `y` is a real number. The reasoning for this is to accommodate the statement of
   the Johnson Bound Theorem. For simplicity and ease of proving statements, `ℓ` can be considered a
   a natural number by taking the floor of the real value. This will not lead to information loss
   since the cardinality of the set of close codewords is a natural number anyway. -/
def listDecodable (C : Code ι F) (r : ℝ) (ℓ : ℝ) : Prop :=
  ∀ y : ι → F, (closeCodewordsRel C y r).ncard ≤ ℓ

/-- A code `C` is uniquely decodable up to a relative distance `r` if for any word `y : ι → F`,
there is at most one codeword in `C` within a relative Hamming distance of `r`.
This is a special case of list decodability where the list size `ℓ` is `1`. -/
def uniqueDecodable (C : Code ι F) (r : ℝ) : Prop :=
  listDecodable C r 1

end

/-! ## ABF26 Definition 2.8 — list around a word `Λ(C, δ, f)` and `|Λ(C, δ)|`

The paper writes `Λ(C, δ, f)` for the set of codewords of `C` whose relative Hamming distance
from `f` is at most `δ`, and `|Λ(C, δ)| = max_f |Λ(C, δ, f)|` for the maximised list size.
`Lambda_at` is a paper-named alias for the existing `closeCodewordsRel`, and `Lambda` is the
new maximised form used by Section 4's `ε_mca` (ABF26 Definition 4.3) and Section 3's
list-decoding bounds.
-/

section Lambda

variable {ι : Type*} [Fintype ι] {F : Type*}

/-- **ABF26 Definition 2.8 (point list).** The set of codewords of `C` within relative
Hamming distance `δ` of `f`. Synonymous with `closeCodewordsRel`; named to match the paper's
`Λ(C, δ, f)`. -/
abbrev Lambda_at (C : Code ι F) (δ : ℝ) (f : ι → F) : Set (ι → F) :=
  closeCodewordsRel C f δ

/-- **ABF26 Definition 2.8 (maximised list size).** The maximum over words `f` of
`|Λ(C, δ, f)|`. Named to match the paper's `|Λ(C, δ)|`. -/
noncomputable def Lambda (C : Code ι F) (δ : ℝ) : ℕ∞ :=
  ⨆ f : ι → F, ((Lambda_at C δ f).ncard : ℕ∞)

/-- `Lambda_at` is monotone in the radius. -/
lemma Lambda_at_subset_of_le {C : Code ι F} {δ₁ δ₂ : ℝ}
    (h : δ₁ ≤ δ₂) (f : ι → F) :
    Lambda_at C δ₁ f ⊆ Lambda_at C δ₂ f := by
  intro c hc
  exact ⟨hc.1, le_trans hc.2 h⟩

/-- `Lambda` is monotone in the radius. -/
lemma Lambda_mono {C : Code ι F} {δ₁ δ₂ : ℝ} [Finite F] (h : δ₁ ≤ δ₂) :
    Lambda C δ₁ ≤ Lambda C δ₂ := by
  refine iSup_mono fun f => ?_
  have hfin : (Lambda_at C δ₂ f).Finite := Set.toFinite _
  exact_mod_cast Set.ncard_le_ncard (Lambda_at_subset_of_le h f) hfin

/-- Any element of `Lambda_at C δ f` is a codeword of `C`. -/
lemma Lambda_at_subset_code {C : Code ι F} (δ : ℝ) (f : ι → F) :
    Lambda_at C δ f ⊆ C := fun _ hc => hc.1

/-- `|Λ(C, δ, f)| ≤ |C|` for finite `C`. -/
lemma ncard_Lambda_at_le_ncard {C : Code ι F} (δ : ℝ) (f : ι → F) (hC : C.Finite) :
    (Lambda_at C δ f).ncard ≤ C.ncard :=
  Set.ncard_le_ncard (Lambda_at_subset_code δ f) hC

/-- `|Λ(C, δ)| ≤ |C|` for finite `C`. -/
lemma Lambda_le_ncard {C : Code ι F} (δ : ℝ) (hC : C.Finite) :
    Lambda C δ ≤ (C.ncard : ℕ∞) := by
  refine iSup_le fun f => ?_
  exact_mod_cast ncard_Lambda_at_le_ncard δ f hC

end Lambda

end ListDecodable
