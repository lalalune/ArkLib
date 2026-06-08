/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# General-rate near-capacity MCA lower bound via window interpolation (Proximity Prize, #232)

This generalizes `MCANearCapacityLowerBound.lean` (the `k=1` constant code) to **every** Reed–Solomon
rate `ρ = k/n`, using an explicit codeword instead of the ad-hoc constant.

## The construction

For RS deg-`<k` on nodes `x₀,…,x_{n-1}` and the stack `u₀ i = xᵢᵏ⁺¹`, `u₁ i = xᵢᵏ`, fix any
`(k+1)`-subset `S` of coordinates with node values `s = {xᵢ : i∈S}` and let `σ = ∑_{x∈s} x`. The
explicit polynomial
`W_s = Xᵏ·(X - σ) − ∏_{x∈s}(X − x)`
is a **degree-`<k` codeword** (`Wpoly_degree_lt`): both terms are monic of degree `k+1` with the same
next coefficient `−σ`, so the top two coefficients cancel. On every node of `s` the product vanishes,
so `W_s(xᵢ) = xᵢᵏ⁺¹ − σ·xᵢᵏ = u₀ i + γ_S·u₁ i` with `γ_S := −σ` (`Wpoly_eval`). Meanwhile `xᵏ` is not
degree-`<k` on `k+1` distinct nodes, so no codeword *pair* agrees with `(u₀,u₁)` on `S`
(`¬ pairJointAgreesOn`). Hence `mcaEvent` fires at `γ_S` (`mcaEvent_of_window`).

Feeding a family `𝒮` of `(k+1)`-windows with **distinct** window-sums into the engine
`MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set` gives
`ε_mca(C, 1 − (k+1)/n) ≥ |𝒮| / |F|`  (`epsMCA_ge_of_window_family`),
at `δ = 1 − (k+1)/n = capacity − 1/n` — strictly inside the Johnson→capacity gap. The "sunflower"
family `{0,…,k-1, k+j}` for `j = 0,…,n-k-1` has `n-k` windows with distinct sums (its only varying
node is `k+j`), giving the headline `ε_mca ≥ (n-k)/|F|` for every rate.

## What this does and does not do (candidate analysis for #232)

* It **realizes** the witness spread that `MCAWitnessSpread.common_witness_badGamma_set_card_le_one`
  proves is necessary — distinct windows `⇒` distinct bad scalars — for arbitrary rate, kernel-checked.
* The same `mcaEvent_of_window` holds for *any* `(k+1)`-subset (not just consecutive), so on a
  structured/smooth domain `|𝒮|` may be pushed up to the number of distinct `(k+1)`-subset sums of the
  node set — quadratic `Θ(k(n-k))` for an arithmetic node set, more for spread-out nodes.
* **It is edge-tight.** A window of size `k+2` would force the line to be degree-`<k` there under *two*
  independent divided-difference conditions on a single `γ` — generically unsolvable; making them
  dependent forces `u₁∈C`, i.e. `pairJointAgreesOn` (the obstruction). So no single algebraic line
  beats `δ = capacity − 1/n`. The smooth-domain cyclic structure (`xⁿ=1` on `L`) does **not** rescue
  the *monomial* line (it degenerates: `x^{k+n}=xᵏ` on `L`); reaching the gap **interior** needs
  multiplicity (Guruswami–Sudan) or a genuinely different construction — the open prize.
* The bound is `O(n)/|F|` (or `O(n²)/|F|`), which is `< ε* = 2⁻¹²⁸` for the prize's large fields
  (`|F|` up to `2²⁵⁶`), so it does **not** pin the prize threshold `δ*` — that needs an *exponential*
  spread `|𝒮| ~ 2¹²⁸`. This file delineates the open core; it does not close it.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232 / #141.
-/

open Polynomial BigOperators
open scoped NNReal ENNReal

namespace ProximityGap.MCANearCapacityGK

open ProximityGap Code

/-! ## Core polynomial lemmas (the explicit codeword) -/

variable {F : Type} [Field F]

/-- The explicit codeword polynomial for a window of nodes `s` (`|s| = k+1`):
`W_s = Xᵏ·(X - σ) - ∏_{x∈s}(X - x)`, `σ = ∑_{x∈s} x`. -/
noncomputable def Wpoly (k : ℕ) (s : Finset F) : F[X] :=
  X ^ k * (X - C (∑ x ∈ s, x)) - ∏ x ∈ s, (X - C x)

theorem coeff_A_top (k : ℕ) (σ : F) : (X ^ k * (X - C σ)).coeff (k + 1) = 1 := by
  have h : X ^ k * (X - C σ) = X ^ (k + 1) - C σ * X ^ k := by ring
  rw [h]; simp [coeff_sub, coeff_X_pow, coeff_C_mul]

theorem coeff_A_next (k : ℕ) (σ : F) : (X ^ k * (X - C σ)).coeff k = -σ := by
  have h : X ^ k * (X - C σ) = X ^ (k + 1) - C σ * X ^ k := by ring
  rw [h]; simp [coeff_sub, coeff_X_pow, coeff_C_mul]

theorem natDegree_A (k : ℕ) (σ : F) : (X ^ k * (X - C σ)).natDegree = k + 1 := by
  rw [natDegree_mul (pow_ne_zero k X_ne_zero) (X_sub_C_ne_zero σ), natDegree_X_pow,
    natDegree_X_sub_C]

/-- **The codeword has degree `< k`.** Both `Xᵏ·(X-σ)` and `∏(X-x)` are monic of degree `k+1`
with the same next coefficient `-σ`, so the top two coefficients of `W_s` cancel. -/
theorem Wpoly_degree_lt (k : ℕ) (s : Finset F) (hs : s.card = k + 1) :
    (Wpoly k s).degree < (k : ℕ) := by
  set σ := ∑ x ∈ s, x with hσ
  have hBmonic : (∏ x ∈ s, (X - C x)).Monic := monic_prod_X_sub_C _ _
  have hBdeg : (∏ x ∈ s, (X - C x)).natDegree = k + 1 := by
    rw [natDegree_prod _ _ (fun x _ => X_sub_C_ne_zero x)]; simp [hs]
  have hBtop : (∏ x ∈ s, (X - C x)).coeff (k + 1) = 1 := by
    have h := hBmonic.coeff_natDegree; rwa [hBdeg] at h
  have hBnext : (∏ x ∈ s, (X - C x)).coeff k = -σ := by
    have h := prod_X_sub_C_nextCoeff (s := s) (f := fun x : F => x)
    rw [nextCoeff, if_neg (by rw [hBdeg]; omega), hBdeg] at h
    simpa [hσ] using h
  rw [degree_lt_iff_coeff_zero]
  intro m hm
  rw [Wpoly, coeff_sub, sub_eq_zero]
  rcases eq_or_lt_of_le hm with rfl | hm1
  · rw [coeff_A_next, hBnext]
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hm1) with h2 | h2
    · rw [← h2, coeff_A_top, hBtop]
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [natDegree_A]; omega),
          coeff_eq_zero_of_natDegree_lt (by rw [hBdeg]; omega)]

/-- The codeword agrees with `xᵏ⁺¹ - σ·xᵏ` on every node of the window. -/
theorem Wpoly_eval (k : ℕ) (s : Finset F) {x : F} (hx : x ∈ s) :
    (Wpoly k s).eval x = x ^ (k + 1) - (∑ y ∈ s, y) * x ^ k := by
  have hvanish : (∏ y ∈ s, (X - C y)).eval x = 0 := by
    rw [eval_prod]; exact Finset.prod_eq_zero hx (by simp)
  rw [Wpoly, eval_sub, hvanish, sub_zero, eval_mul, eval_pow, eval_X, eval_sub, eval_X, eval_C]
  ring

/-! ## The MCA event fires for every `(k+1)`-window of an explicit RS code -/

variable [Fintype F] [DecidableEq F] {n : ℕ}

/-- First row `u₀ i = (domain i)ᵏ⁺¹`. -/
noncomputable def urow0 (domain : Fin n ↪ F) (k : ℕ) : Fin n → F := fun i => (domain i) ^ (k + 1)
/-- Second row `u₁ i = (domain i)ᵏ`. -/
noncomputable def urow1 (domain : Fin n ↪ F) (k : ℕ) : Fin n → F := fun i => (domain i) ^ k

/-- **Core MCA event (general rate).** For RS deg-`<k` on an arbitrary node embedding `domain`,
stack `((domain i)ᵏ⁺¹, (domain i)ᵏ)`, and *any* `(k+1)`-window `S` of coordinates, `mcaEvent` fires
at `γ_S = -∑_{i∈S} domain i`. -/
theorem mcaEvent_of_window [NeZero n] (domain : Fin n ↪ F) (k : ℕ) (hk : 1 ≤ k)
    (S : Finset (Fin n)) (hS : S.card = k + 1) :
    mcaEvent (ReedSolomon.code (ι := Fin n) (F := F) (domain := domain) k : Set (Fin n → F))
      (1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)) (urow0 domain k) (urow1 domain k)
      (-(∑ i ∈ S, domain i)) := by
  set ws : Finset F := S.image domain with hws
  have hwscard : ws.card = k + 1 := by
    rw [hws, Finset.card_image_of_injective _ domain.injective, hS]
  have hwssum : (∑ x ∈ ws, x) = ∑ i ∈ S, domain i := by
    rw [hws, Finset.sum_image (fun a _ b _ h => domain.injective h)]
  set W : F[X] := Wpoly k ws with hW
  refine ⟨S, ?_, ⟨fun i => W.eval (domain i), ?_, ?_⟩, ?_⟩
  · have hnpos : (0 : ℝ≥0) < (n : ℝ≥0) := by
      have : (0 : ℕ) < n := Nat.pos_of_ne_zero (NeZero.ne n); exact_mod_cast this
    have hle : ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0) ≤ 1 := by
      rw [div_le_one hnpos]; exact_mod_cast (by
        have := S.card_le_univ; rw [hS, Fintype.card_fin] at this; exact this)
    rw [tsub_tsub_cancel_of_le hle, Fintype.card_fin, div_mul_cancel₀ _ (ne_of_gt hnpos), hS]
  · exact ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval W
      (by exact_mod_cast Wpoly_degree_lt k ws hwscard) (fun i => rfl)
  · intro i hi
    have hdi : domain i ∈ ws := by rw [hws]; exact Finset.mem_image_of_mem _ hi
    show W.eval (domain i) = urow0 domain k i + (-(∑ j ∈ S, domain j)) • urow1 domain k i
    rw [hW, Wpoly_eval k ws hdi, hwssum, urow0, urow1, smul_eq_mul]; ring
  · rintro ⟨v₀, _, v₁, hv₁C, hag⟩
    obtain ⟨Q, hQmem, hQeval⟩ := hv₁C
    have hQdeg : Q.degree < (k : ℕ) := Polynomial.mem_degreeLT.mp hQmem
    have hQeval' : ∀ i, v₁ i = Q.eval (domain i) := fun i => by rw [← hQeval]; rfl
    have hzero : ∀ x ∈ ws, (Q - X ^ k).eval x = 0 := by
      intro x hx
      rw [hws, Finset.mem_image] at hx
      obtain ⟨i, hiS, rfl⟩ := hx
      have h1 : v₁ i = (domain i) ^ k := (hag i hiS).2
      rw [eval_sub, eval_pow, eval_X, ← hQeval' i, h1, sub_self]
    have hcard : (Q - X ^ k).natDegree < ws.card := by
      rw [hwscard]
      calc (Q - X ^ k).natDegree ≤ max Q.natDegree (X ^ k).natDegree := natDegree_sub_le _ _
        _ < k + 1 := by
            rw [natDegree_X_pow]
            have hQn : Q.natDegree < k := by
              rcases eq_or_ne Q 0 with rfl | hQ0
              · simpa using hk
              · exact (natDegree_lt_iff_degree_lt hQ0).mpr hQdeg
            omega
    have hQk : Q = X ^ k :=
      sub_eq_zero.mp (eq_zero_of_natDegree_lt_card_of_eval_eq_zero' (Q - X ^ k) ws hzero hcard)
    rw [hQk, degree_X_pow] at hQdeg
    exact absurd hQdeg (lt_irrefl _)

/-- **General-rate near-capacity MCA lower bound.** For RS deg-`<k` on any node embedding, any
family `𝒮` of `(k+1)`-windows whose window-sums are distinct yields
`ε_mca(C, 1-(k+1)/n) ≥ |𝒮|/|F|`. The sunflower family `{0,…,k-1, k+j}` (`j=0,…,n-k-1`) over a field
with `n ≤ |F|` has `n-k` windows with distinct sums, giving `ε_mca ≥ (n-k)/|F|` at every rate. -/
theorem epsMCA_ge_of_window_family [NeZero n] (domain : Fin n ↪ F) (k : ℕ) (hk : 1 ≤ k)
    (𝒮 : Finset (Finset (Fin n))) (hcard : ∀ S ∈ 𝒮, S.card = k + 1)
    (hinj : Set.InjOn (fun S => -(∑ i ∈ S, domain i)) 𝒮) :
    ((𝒮.card : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          (ReedSolomon.code (domain := domain) k : Set (Fin n → F))
          (1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)) := by
  set G : Finset F := 𝒮.image (fun S => -(∑ i ∈ S, domain i)) with hG
  have hGcard : G.card = 𝒮.card := Finset.card_image_of_injOn hinj
  have hmca : ∀ γ ∈ G,
      mcaEvent (ReedSolomon.code (domain := domain) k : Set (Fin n → F))
        (1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0))
        ((![urow0 domain k, urow1 domain k] : WordStack F (Fin 2) (Fin n)) 0)
        ((![urow0 domain k, urow1 domain k] : WordStack F (Fin 2) (Fin n)) 1) γ := by
    intro γ hγ
    rw [hG, Finset.mem_image] at hγ
    obtain ⟨S, hS, rfl⟩ := hγ
    simpa using mcaEvent_of_window domain k hk S (hcard S hS)
  have hengine := ProximityGap.MCAWitnessSpread.epsMCA_ge_card_div_of_mcaEvent_set
    (ReedSolomon.code (domain := domain) k : Set (Fin n → F))
    (1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0))
    (![urow0 domain k, urow1 domain k] : WordStack F (Fin 2) (Fin n)) G hmca
  rwa [hGcard] at hengine

omit [DecidableEq F] in
/-- **Sunflower-family near-capacity MCA lower bound.** Fix a base `B` of `k` coordinates and a
disjoint tail `T`. The windows `insert i B`, for `i ∈ T`, all have size `k+1`, and their
window-sums are distinct under the domain embedding because only the tail coordinate varies.
Therefore `ε_mca(C, 1-(k+1)/n) ≥ |T|/|F|`. The concrete prose instance takes `B = {0,…,k-1}`
and `T = {k,…,n-1}`, yielding the advertised `n-k` windows. -/
theorem epsMCA_ge_of_sunflower_family [NeZero n] (domain : Fin n ↪ F)
    (k : ℕ) (hk : 1 ≤ k) (B T : Finset (Fin n))
    (hB : B.card = k) (hdisj : Disjoint B T) :
    ((T.card : ℕ) : ℝ≥0∞) / (Fintype.card F : ℝ≥0∞)
      ≤ epsMCA (F := F) (A := F)
          (ReedSolomon.code (domain := domain) k : Set (Fin n → F))
          (1 - ((k + 1 : ℕ) : ℝ≥0) / (n : ℝ≥0)) := by
  classical
  set 𝒮 : Finset (Finset (Fin n)) := T.image (fun i => insert i B) with h𝒮
  have hnot_mem (i : Fin n) (hi : i ∈ T) : i ∉ B := by
    intro hiB
    exact (Finset.disjoint_left.mp hdisj) hiB hi
  have hwindowInj : Set.InjOn (fun i : Fin n => insert i B) T := by
    intro i hi j hj hij
    have hiB : i ∉ B := hnot_mem i hi
    have hmem : i ∈ insert j B := by
      simpa [hij] using (Finset.mem_insert_self i B)
    rw [Finset.mem_insert] at hmem
    exact hmem.elim id (fun hiB' => False.elim (hiB hiB'))
  have h𝒮card : 𝒮.card = T.card := by
    rw [h𝒮]
    exact Finset.card_image_of_injOn hwindowInj
  have hcard : ∀ S ∈ 𝒮, S.card = k + 1 := by
    intro S hS
    rw [h𝒮, Finset.mem_image] at hS
    rcases hS with ⟨i, hi, rfl⟩
    simp [hnot_mem i hi, hB]
  have hinj : Set.InjOn (fun S => -(∑ i ∈ S, domain i)) 𝒮 := by
    intro S hS S' hS' heq
    have hSfin : S ∈ 𝒮 := by simpa using hS
    have hS'fin : S' ∈ 𝒮 := by simpa using hS'
    rw [h𝒮, Finset.mem_image] at hSfin hS'fin
    rcases hSfin with ⟨i, hi, rfl⟩
    rcases hS'fin with ⟨j, hj, rfl⟩
    have hiB : i ∉ B := hnot_mem i hi
    have hjB : j ∉ B := hnot_mem j hj
    have hsumEq : (∑ x ∈ insert i B, domain x) = ∑ x ∈ insert j B, domain x := by
      simpa using congrArg Neg.neg heq
    rw [Finset.sum_insert hiB, Finset.sum_insert hjB] at hsumEq
    have hdomain : domain i = domain j := add_right_cancel hsumEq
    have hij : i = j := domain.injective hdomain
    subst j
    rfl
  have hbound := epsMCA_ge_of_window_family domain k hk 𝒮 hcard hinj
  rwa [h𝒮card] at hbound

#print axioms mcaEvent_of_window
#print axioms epsMCA_ge_of_window_family
#print axioms epsMCA_ge_of_sunflower_family

end ProximityGap.MCANearCapacityGK
