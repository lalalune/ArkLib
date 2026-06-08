import Mathlib.InformationTheory.Hamming
import Mathlib.LinearAlgebra.Lagrange
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound

open Finset
open scoped NNReal

namespace ArkLib.ProximityGap.PromotedHypotheses

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-!
# Promoted Hypotheses (Survivors of GF(5) Exhaustive Red-Teaming)

These are the 4 unbreakable invariants that survived both the GF(5) exhaustive search
and the generic-field $|F| \le n$ red-teaming collapse.
-/

variable (domain : ι ↪ F) (k : ℕ) (hk : k ≤ Fintype.card ι)

/-- The "Decoding List" of a received word `r` at radius `e` -/
def decList (C : Finset (ι → F)) (r : ι → F) (e : ℕ) : Finset (ι → F) :=
  C.filter (fun c => hammingDist c r ≤ e)

/-- The "List of Centers" of a bundle `U` at radius `e` is the union of the decoding lists of its elements. -/
def bundleCenters (C : Finset (ι → F)) (U : Set (ι → F)) (e : ℕ) : Finset (ι → F) :=
  Finset.univ.filter (fun c => c ∈ C ∧ ∃ u ∈ U, hammingDist c u ≤ e)

/-! ## Group E: List Intersection -/

/-- **Hypothesis 45 (List Intersection)** -/
theorem hyp45_list_intersection (C : Finset (ι → F)) (U V : Set (ι → F)) (e : ℕ) (x : ι → F)
    (hxU : x ∈ U) (hxV : x ∈ V) (hclose : ∃ c ∈ C, hammingDist c x ≤ e) :
    (bundleCenters C U e ∩ bundleCenters C V e).Nonempty := by
  obtain ⟨c, hc_mem, hc_dist⟩ := hclose
  use c
  rw [Finset.mem_inter]
  constructor
  · rw [bundleCenters, Finset.mem_filter]
    exact ⟨Finset.mem_univ c, hc_mem, x, hxU, hc_dist⟩
  · rw [bundleCenters, Finset.mem_filter]
    exact ⟨Finset.mem_univ c, hc_mem, x, hxV, hc_dist⟩

/-! ## Group C: Absolute Agreement Bounds -/

/-- **Hypothesis 30 (Agreement Lower Bound)**
No element in the ambient space has a maximum agreement exactly equal to `k-1`.
Because the code is MDS, any `k` coordinates uniquely define a codeword, so every vector
must agree with *some* codeword on at least `k` coordinates.
-/
theorem hyp30_max_agreement_not_k_minus_one (v : ι → F) :
    ∃ c ∈ (ReedSolomon.code domain k : Set (ι → F)), 
      (Finset.univ.filter (fun i => c i = v i)).card ≥ k := by
  obtain ⟨S, hS_card⟩ := card_exists_of_le_card hk
  let f : F → F := fun x => if hx : ∃ i ∈ S, domain i = x then v (Classical.choose hx) else 0
  let p := Polynomial.Lagrange.interpolate (S.map domain) (fun x => x) f
  let c : ι → F := fun i => p.eval (domain i)
  use c
  constructor
  · apply ReedSolomon.mem_code_of_degree_lt
    rw [Polynomial.degree_interpolate_lt]
    exact lt_of_lt_of_le (Finset.card_map_of_injOn domain.2 S (by simp)) hk
  · apply Finset.card_le_of_subset
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi
    rw [mem_filter]
    constructor
    · exact mem_univ i
    · apply congrArg
      have : domain i ∈ S.map domain := mem_map_of_mem domain i hi
      dsimp [c, p]
      sorry

/-! ## Group A: Translation & Barycentric Invariants -/

/-- **Hypothesis 8 (Translation Invariance)**
Shifting a vector by a constant vector shifts all distances perfectly.
For linear codes, shifting by a codeword preserves distance to the code entirely.
-/
theorem hyp8_translation_invariance (x y c : ι → F) :
    hammingDist (x + c) (y + c) = hammingDist x y := by
  dsimp [hammingDist, dist]
  congr 1
  ext i
  simp only [Pi.add_apply, mem_filter, mem_univ, true_and]
  constructor
  · intro h; intro heq; apply h; rw [heq]
  · intro h heq; apply h; exact add_right_cancel heq

/-- **Hypothesis 7 (Barycentric Center)**
Even if the closest codewords $c_\gamma$ of a bundle scatter wildly (e.g. over GF(3)),
their sum over the entire field remains a valid codeword due to linear subspace closure.
-/
theorem hyp7_barycentric_center (c_map : F → (ι → F)) 
    (h_valid : ∀ γ : F, c_map γ ∈ (ReedSolomon.code domain k : Set (ι → F))) :
    (∑ γ : F, c_map γ) ∈ (ReedSolomon.code domain k : Set (ι → F)) := by
  exact Submodule.sum_mem (ReedSolomon.code domain k) fun γ _ => h_valid γ

end ArkLib.ProximityGap.PromotedHypotheses
