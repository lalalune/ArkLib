/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.GranularityLadderRS

/-!
# Möbius-inversion equivariance of the MCA event (#371, the σ-descent foundation)

The window adversary is Möbius-symmetric (probe record at two scales).  This file
proves the symmetry is structural: the MCA problem on an inversion-stable domain is
equivariant under `x ↦ −1/x` — via the **twisted** permutation action

  `(T u)(i) = (dom i)^{k−1} · u(σ i)`,

where `σ` is the index permutation realizing the inversion.  Plain precomposition
does NOT preserve the RS code (`P(−1/x)` is rational); the weight `x^{k−1}` repairs
it: `x^{k−1}·P(−1/x)` is the reversal-twist polynomial of degree `< k`.

* `mcaEvent_twisted_perm_mp` — the general engine: any weighted permutation with
  nonvanishing weights and code closure transports the MCA event (extends the
  in-tree untwisted engine `mcaEvent_comp_perm_iff`);
* `reversalTwist` / `reversalTwist_eval` — the polynomial closure;
* `rsCode_twist_mem` / `rsCode_twist_inv_mem` — RS closure both ways;
* `mcaEvent_rs_inversion` — the headline: the second PGL₂ generator.  Together with
  the in-tree rotation equivariance (`mcaEvent_rs_rotate`) this completes the
  Möbius symmetry of smooth-domain MCA — the formal ground for the σ-descent on
  the window residual `WindowRationalBounded`.
-/

open Finset Polynomial
open scoped NNReal ENNReal

namespace ProximityGap.MCAMobius

open ProximityGap.SpikeFloor ProximityGap

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## The twisted permutation engine -/

/-- The weighted-permutation action on words. -/
def twist (σ : Equiv.Perm ι) (m : ι → F) (u : ι → F) : ι → F :=
  fun i => m i * u (σ i)

/-- **The twisted-permutation engine**: a weighted permutation with nonvanishing
weights and code closure transports the MCA event at every scalar. -/
theorem mcaEvent_twisted_perm_mp (C : Submodule F (ι → F)) {δ : ℝ≥0}
    {u₀ u₁ : ι → F} {γ : F} (σ : Equiv.Perm ι) (m : ι → F) (hm : ∀ i, m i ≠ 0)
    (hT : ∀ w ∈ C, twist σ m w ∈ C)
    (hT' : ∀ w ∈ C, (fun j => (m (σ.symm j))⁻¹ * w (σ.symm j)) ∈ C) :
    mcaEvent (F := F) (C : Set (ι → F)) δ (twist σ m u₀) (twist σ m u₁) γ →
      mcaEvent (F := F) (C : Set (ι → F)) δ u₀ u₁ γ := by
  rintro ⟨S, hcard, ⟨w, hw, hag⟩, hno⟩
  refine ⟨S.image ⇑σ, ?_, ⟨fun j => (m (σ.symm j))⁻¹ * w (σ.symm j), hT' w hw, ?_⟩, ?_⟩
  · rw [Finset.card_image_of_injective S σ.injective]
    exact hcard
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    have h : w i = twist σ m u₀ i + γ • twist σ m u₁ i := hag i hi
    simp only [twist, smul_eq_mul] at h
    have hmi := hm i
    show (m (σ.symm (σ i)))⁻¹ * w (σ.symm (σ i)) = u₀ (σ i) + γ • u₁ (σ i)
    rw [Equiv.symm_apply_apply, h, smul_eq_mul]
    field_simp
  · intro hpair
    apply hno
    obtain ⟨v₀, hv₀, v₁, hv₁, hagp⟩ := hpair
    refine ⟨twist σ m v₀, hT v₀ hv₀, twist σ m v₁, hT v₁ hv₁, fun i hi => ?_⟩
    have h := hagp (σ i) (Finset.mem_image_of_mem ⇑σ hi)
    exact ⟨by simp only [twist]; rw [h.1], by simp only [twist]; rw [h.2]⟩

/-! ## The reversal twist polynomial -/

/-- The reversal twist `P* = Σ_j (−1)^j p_j X^{k−1−j}` — the polynomial computing
`x^{k−1}·P(−1/x)`. -/
noncomputable def reversalTwist (k : ℕ) (P : F[X]) : F[X] :=
  ∑ j ∈ Finset.range k, C ((-1) ^ j * P.coeff j) * X ^ (k - 1 - j)

theorem reversalTwist_degree_lt (k : ℕ) (hk : 1 ≤ k) (P : F[X]) :
    (reversalTwist k P).degree < k := by
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe k)]
  intro j hj
  refine lt_of_le_of_lt (degree_mul_le _ _) ?_
  calc (C ((-1) ^ j * P.coeff j)).degree + (X ^ (k - 1 - j) : F[X]).degree
      ≤ 0 + ((k - 1 - j : ℕ) : WithBot ℕ) := add_le_add degree_C_le
        (by rw [degree_X_pow])
    _ < (k : WithBot ℕ) := by
        rw [zero_add]
        exact_mod_cast (by omega : k - 1 - j < k)

/-- The evaluation identity: `P*(x) = x^{k−1}·P(−x⁻¹)` for `x ≠ 0`, `deg P < k`. -/
theorem reversalTwist_eval (k : ℕ) (P : F[X]) (hP : P.degree < k)
    {x : F} (hx : x ≠ 0) :
    (reversalTwist k P).eval x = x ^ (k - 1) * P.eval (-x⁻¹) := by
  by_cases hP0 : P = 0
  · subst hP0
    simp [reversalTwist]
  have hPdeg : P.natDegree < k := (natDegree_lt_iff_degree_lt hP0).mpr hP
  rw [reversalTwist, eval_finset_sum, eval_eq_sum_range' hPdeg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k - 1 := by
    have := Finset.mem_range.mp hj
    omega
  rw [eval_mul, eval_C, eval_pow, eval_X]
  have hpowj : x ^ (k - 1 - j) = x ^ (k - 1) * (x⁻¹) ^ j := by
    have h3 : x ^ (k - 1 - j) * x ^ j = x ^ (k - 1) * (x⁻¹) ^ j * x ^ j := by
      rw [← pow_add, mul_assoc, ← mul_pow, inv_mul_cancel₀ hx, one_pow, mul_one]
      congr 1
      omega
    exact mul_right_cancel₀ (pow_ne_zero j hx) h3
  rw [hpowj, show (-x⁻¹ : F) = (-1) * x⁻¹ by ring, mul_pow]
  ring

/-! ## RS closure under the inversion twist -/

variable {n : ℕ} [NeZero n]

/-- Forward closure: the twist of a codeword is a codeword (the reversal twist). -/
theorem rsCode_twist_mem (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹)
    {u : Fin n → F} (hu : u ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    twist σ (fun i => (dom i) ^ (k - 1)) u
      ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  obtain ⟨P, hPdeg, rfl⟩ := hu
  refine ⟨reversalTwist k P, reversalTwist_degree_lt k hk P, ?_⟩
  funext i
  show twist σ (fun i => (dom i) ^ (k - 1)) (fun i => P.eval (dom i)) i
    = (reversalTwist k P).eval (dom i)
  rw [twist]
  show (dom i) ^ (k-1) * P.eval (dom (σ i)) = (reversalTwist k P).eval (dom i)
  rw [reversalTwist_eval k P hPdeg (hdom0 i), hσ i]

/-- Backward closure: the inverse twist of a codeword is a codeword (a scalar
multiple of the reversal twist). -/
theorem rsCode_twist_inv_mem (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹)
    {u : Fin n → F} (hu : u ∈ (rsCode dom k : Submodule F (Fin n → F))) :
    (fun j => ((fun i => (dom i) ^ (k - 1)) (σ.symm j))⁻¹ * u (σ.symm j))
      ∈ (rsCode dom k : Submodule F (Fin n → F)) := by
  obtain ⟨P, hPdeg, rfl⟩ := hu
  -- dom (σ.symm j) = −(dom j)⁻¹  (the involution algebra)
  have hσsymm : ∀ j, dom (σ.symm j) = -(dom j)⁻¹ := by
    intro j
    have h := hσ (σ.symm j)
    rw [Equiv.apply_symm_apply] at h
    have hd := hdom0 (σ.symm j)
    -- h : dom j = −(dom (σ.symm j))⁻¹; solve for dom (σ.symm j)
    rw [h, inv_neg, inv_inv, neg_neg]
  refine ⟨((-1 : F) ^ (k - 1)) • reversalTwist k P,
    lt_of_le_of_lt (degree_smul_le _ _) (reversalTwist_degree_lt k hk P), ?_⟩
  funext j
  have hdj := hdom0 j
  have hdsj := hdom0 (σ.symm j)
  show (((dom (σ.symm j)) ^ (k - 1))⁻¹ * P.eval (dom (σ.symm j)))
    = (((-1 : F) ^ (k - 1)) • reversalTwist k P).eval (dom j)
  rw [eval_smul, smul_eq_mul, reversalTwist_eval k P hPdeg hdj, hσsymm j]
  have hinv : (((-(dom j)⁻¹ : F)) ^ (k - 1))⁻¹
      = ((-1 : F) ^ (k - 1)) * (dom j) ^ (k - 1) := by
    rw [show (-(dom j)⁻¹ : F) = (-1) * (dom j)⁻¹ by ring, mul_pow, mul_inv]
    congr 1
    · rw [← inv_pow, inv_neg, inv_one]
    · rw [← inv_pow, inv_inv]
  rw [hinv]
  ring

/-! ## The headline -/

open Classical in
/-- **Möbius-inversion equivariance of smooth-domain MCA** — the second PGL₂
generator: on an inversion-stable domain avoiding `0`, the twisted action
`(T u)(i) = (dom i)^{k−1}·u(σ i)` preserves the MCA event at every scalar. -/
theorem mcaEvent_rs_inversion (dom : Fin n ↪ F) {k : ℕ} (hk : 1 ≤ k)
    (σ : Equiv.Perm (Fin n)) (hdom0 : ∀ i, dom i ≠ 0)
    (hσ : ∀ i, dom (σ i) = -(dom i)⁻¹) (δ : ℝ≥0) (γ : F) (u₀ u₁ : Fin n → F) :
    mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ
        (twist σ (fun i => (dom i) ^ (k - 1)) u₀)
        (twist σ (fun i => (dom i) ^ (k - 1)) u₁) γ →
      mcaEvent (F := F)
        ((rsCode dom k : Submodule F (Fin n → F)) : Set (Fin n → F)) δ u₀ u₁ γ :=
  mcaEvent_twisted_perm_mp (rsCode dom k) σ _
    (fun i => pow_ne_zero _ (hdom0 i))
    (fun w hw => rsCode_twist_mem dom hk σ hdom0 hσ hw)
    (fun w hw => rsCode_twist_inv_mem dom hk σ hdom0 hσ hw)

end ProximityGap.MCAMobius

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.MCAMobius.mcaEvent_twisted_perm_mp
#print axioms ProximityGap.MCAMobius.reversalTwist_eval
#print axioms ProximityGap.MCAMobius.rsCode_twist_mem
#print axioms ProximityGap.MCAMobius.rsCode_twist_inv_mem
#print axioms ProximityGap.MCAMobius.mcaEvent_rs_inversion
