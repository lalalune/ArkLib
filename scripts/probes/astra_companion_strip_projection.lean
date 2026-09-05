/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Projection to the exact contact strip

This is the polynomial/linear-algebra bridge for the clipped contact-band
count. The index set includes only coefficients in the actual strip, rather
than delta coefficients in every channel of an enclosing box.

The nested support is the one used by LocatorLowQuotient at official companion
commit 032154395c51fd6f77715a7f42d9a987ab9fb48a. These declarations are independent
of that submission and contain no ProtocolClaim. Integration into its repeated
quotient selector, the fast arithmetic identity, and the final numerical
certificate remain separate obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace AstraCompanionStripProjection

open scoped BigOperators

noncomputable section

variable {K : Type*} [Field K]

def box (D w T Y S : ℕ) : Submodule K (MvPolynomial (Fin 4) K) :=
  MvPolynomial.restrictSupport K {d |
    d 1+d 2+d 3 ≤ T ∧ d 1+d 2 ≤ Y ∧ d 2 ≤ S ∧
    d 0+w*d 1+(w-1)*d 2 < D}

abbrev Index (D delta w T Y S : ℕ) :=
  (y : Fin (min T Y+1)) ×
    (r : Fin (min S (min (T-y.val) (Y-y.val))+1)) ×
      (Fin (T+1-y.val-r.val) × Fin (min delta (D-w*y.val-(w-1)*r.val)))

def budget (D delta w T Y S : ℕ) : ℕ :=
  ∑ y ∈ Finset.range (min T Y+1),
    ∑ r ∈ Finset.range (min S (min (T-y) (Y-y))+1),
      (T+1-y-r)*min delta (D-w*y-(w-1)*r)

theorem index_card (D delta w T Y S : ℕ) :
    Fintype.card (Index D delta w T Y S) = budget D delta w T Y S := by
  simp [Index, budget, Fintype.card_sigma, Finset.sum_range]

def exponent (D delta w : ℕ) {T Y S : ℕ} (c : Index D delta w T Y S) :
    Fin 4 →₀ ℕ :=
  Finsupp.single 0 (D-delta-w*c.1.val-(w-1)*c.2.1.val+c.2.2.2.val) +
    Finsupp.single 1 c.1.val + Finsupp.single 2 c.2.1.val +
      Finsupp.single 3 c.2.2.1.val

def stripMap (D delta w T Y S : ℕ) :
    MvPolynomial (Fin 4) K →ₗ[K] (Index D delta w T Y S → K) :=
  LinearMap.pi (fun c => MvPolynomial.lcoeff K (exponent D delta w c))

@[simp] theorem stripMap_apply (D delta w T Y S : ℕ)
    (P : MvPolynomial (Fin 4) K) (c : Index D delta w T Y S) :
    stripMap D delta w T Y S P c = MvPolynomial.coeff (exponent D delta w c) P := rfl

/-- Vanishing of exactly the strip coefficients leaves the lower contact box. -/
theorem mem_low_of_strip_zero (D delta w T Y S : ℕ)
    (P : MvPolynomial (Fin 4) K) (hP : P ∈ box D w T Y S)
    (hzero : stripMap D delta w T Y S P = 0) :
    P ∈ box (D-delta) w T Y S := by
  classical
  intro d hd
  rcases hP hd with ⟨hT, hY, hS, hD⟩
  refine ⟨hT, hY, hS, ?_⟩
  by_contra hnot
  have hy : d 1 < min T Y+1 := by omega
  have hr : d 2 < min S (min (T-d 1) (Y-d 1))+1 := by omega
  have hz : d 3 < T+1-d 1-d 2 := by omega
  have hx : d 0-(D-delta-w*d 1-(w-1)*d 2) <
      min delta (D-w*d 1-(w-1)*d 2) := by omega
  let c : Index D delta w T Y S :=
    ⟨⟨d 1, hy⟩, ⟨⟨d 2, hr⟩,
      ⟨⟨d 3, hz⟩, ⟨d 0-(D-delta-w*d 1-(w-1)*d 2), hx⟩⟩⟩⟩
  have he : exponent D delta w c = d := by
    ext i
    fin_cases i <;> (simp [exponent, c]; omega)
  have hc := congrFun hzero c
  have hcoeff : MvPolynomial.coeff d P = 0 := by
    simpa only [stripMap_apply, he, Pi.zero_apply] using hc
  exact (MvPolynomial.mem_support_iff.mp hd) hcoeff

variable {V : Type*} [AddCommGroup V] [Module K V]

/-- The exact strip budget bounds the rank of the coefficient projection. -/
theorem strip_range_finrank_le (D delta w T Y S : ℕ)
    (q : V →ₗ[K] MvPolynomial (Fin 4) K) :
    Module.finrank K ((stripMap D delta w T Y S).comp q).range ≤
      budget D delta w T Y S := by
  calc
    Module.finrank K ((stripMap D delta w T Y S).comp q).range ≤
        Module.finrank K (Index D delta w T Y S → K) :=
      ((stripMap D delta w T Y S).comp q).range.finrank_le
    _ = budget D delta w T Y S := by
      rw [Module.finrank_fintype_fun_eq_card, index_card]

/-- A subspace of the high box loses at most the exact strip budget when it
is restricted to the low box. This supplies the rank step of a band selector. -/
theorem exists_low_subspace (D delta w T Y S : ℕ)
    [FiniteDimensional K V]
    (q : V →ₗ[K] MvPolynomial (Fin 4) K)
    (hmem : ∀ v, q v ∈ box D w T Y S) :
    ∃ low : Submodule K V,
      Module.finrank K V-budget D delta w T Y S ≤ Module.finrank K low ∧
      ∀ v : low, q v.1 ∈ box (D-delta) w T Y S := by
  let band := (stripMap D delta w T Y S).comp q
  have hrank := strip_range_finrank_le D delta w T Y S q
  have hsum := band.finrank_range_add_finrank_ker
  refine ⟨band.ker, ?_, ?_⟩
  · change Module.finrank K band.range ≤ _ at hrank
    omega
  · intro v
    apply mem_low_of_strip_zero D delta w T Y S (q v.1) (hmem v.1)
    exact v.2

#print axioms index_card
#print axioms mem_low_of_strip_zero
#print axioms strip_range_finrank_le
#print axioms exists_low_subspace

end
end AstraCompanionStripProjection
