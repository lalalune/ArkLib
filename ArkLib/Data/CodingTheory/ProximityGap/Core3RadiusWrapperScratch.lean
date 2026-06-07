import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ListDecoding.Agreement

open Polynomial Polynomial.Bivariate

namespace ArkLib
namespace Core3RadiusWrapperScratch

open ProximityGap Trivariate RatFunc

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F]
variable {n : ℕ}

omit [DecidableEq F] [DecidableEq (RatFunc F)] [Finite F] in
theorem keystone_count_of_radius
    {Qz : F[X][Y]} {m k : ℕ} {A : Finset (Fin n)} {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (hdist : dist ≤ n)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hwdeg : Bivariate.natWeightedDegree Qz 1 k ≤ proximity_gap_degree_bound k n m)
    (hcard : A.card = n - dist) :
    Bivariate.natWeightedDegree Qz 1 k < m * A.card := by
  have hsuff : (proximity_gap_degree_bound k n m : ℝ) < m * (n - dist) :=
    GuruswamiSudan.sufficient_multiplicity_bound (k := k) (n := n) (m := m)
      (dist := dist) hk hm hradius
  have hcastA : ((m * A.card : ℕ) : ℝ) = m * (n - dist) := by
    rw [hcard]; push_cast [Nat.cast_sub hdist]; ring
  have hwdegR :
      (Bivariate.natWeightedDegree Qz 1 k : ℝ) ≤
        (proximity_gap_degree_bound k n m : ℝ) := by exact_mod_cast hwdeg
  have hlt : (Bivariate.natWeightedDegree Qz 1 k : ℝ) < ((m * A.card : ℕ) : ℝ) := by
    rw [hcastA]; exact lt_of_le_of_lt hwdegR hsuff
  exact_mod_cast hlt

theorem Q_vanishes_on_close_codeword_graph_of_radius [DecidableEq (Polynomial F)]
    {m k : ℕ} {δ : ℚ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (hdist : dist ≤ n)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hwdeg :
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k ≤
        proximity_gap_degree_bound k n m)
    (hcard : A.card = n - dist) :
    (Trivariate.eval_on_Z Q z).eval (Pz hS) = 0 := by
  have hcount :
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k < m * A.card :=
    keystone_count_of_radius (Qz := Trivariate.eval_on_Z Q z) (m := m) (k := k)
      (A := A) (dist := dist) hk hm hdist hradius hwdeg hcard
  exact Q_vanishes_on_close_codeword_graph (F := F) (k := k) (z := z)
    (h_gs := h_gs) hS hQz_ne A hA hcount

theorem Q_graph_factor_dvd_of_radius [DecidableEq (Polynomial F)]
    {m k : ℕ} {δ : ℚ} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
    {z : F} (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
    (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
    (hQz_ne : Trivariate.eval_on_Z Q z ≠ 0)
    (A : Finset (Fin n))
    (hA : ∀ i ∈ A, (u₀ + z • u₁) i = (Pz hS).eval (ωs i))
    {dist : ℕ}
    (hk : k + 1 ≤ n) (hm : 1 ≤ m) (hdist : dist ≤ n)
    (hradius : (dist : ℝ) / n < proximity_gap_johnson k n m)
    (hwdeg :
      Bivariate.natWeightedDegree (Trivariate.eval_on_Z Q z) 1 k ≤
        proximity_gap_degree_bound k n m)
    (hcard : A.card = n - dist) :
    Polynomial.X - Polynomial.C (Pz hS) ∣ pg_eval_on_Z (F := F) Q z := by
  have hvanish := Q_vanishes_on_close_codeword_graph_of_radius (F := F)
    (h_gs := h_gs) hS hQz_ne A hA hk hm hdist hradius hwdeg hcard
  have hroot : (pg_eval_on_Z (F := F) Q z).eval (Pz hS) = 0 := by
    rwa [c57_eval_on_Z_eq_pg] at hvanish
  exact Polynomial.dvd_iff_isRoot.mpr hroot

#print axioms ArkLib.Core3RadiusWrapperScratch.keystone_count_of_radius
#print axioms ArkLib.Core3RadiusWrapperScratch.Q_vanishes_on_close_codeword_graph_of_radius
#print axioms ArkLib.Core3RadiusWrapperScratch.Q_graph_factor_dvd_of_radius

end Core3RadiusWrapperScratch
end ArkLib
