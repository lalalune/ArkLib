/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCALowerBound
import ArkLib.Data.CodingTheory.ProximityGap.ReedSolomonUniqueDecode

/-!
# Connected unique-decoding-regime MCA bound for Reed–Solomon, from scratch (#232)

Wires the from-scratch UDR bad-scalar bound to the actual `ε_mca` of a Reed–Solomon code, yielding
ABF26 Table-1 row 2 (`ε_mca ≤ O(δn)/|F|` below the unique-decoding radius) with **no admit**:

  `epsMCA_rs_udr_le` — for `RS[F, α, k]` with `k ≤ n` and the regime `3(n − t) < n − k + 1`
  (`t = ⌈(1-δ)n⌉`, the witness-size floor), `ε_mca(RS, δ) ≤ 2(n − t)/|F|`.

Since `n − t ≈ δn`, this is `ε_mca ≤ 2δn/|F|`, a genuine positive-side lower-witness on `δ*`
(`δ* ≥ δ` whenever the regime holds). The minimum-distance input is `ReedSolomon.code_eq_of_agree`
(degree-`<k` codewords agreeing on `≥ k` points are equal).

Axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

namespace ProximityGap.UDRwire

open Finset ProximityGap
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem badGamma_le (e₀ e₁ : ι → F) :
    (univ.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card
      ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := by
  classical
  apply Finset.card_le_card_of_injOn
    (fun γ => if h : ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0 then h.choose else Classical.arbitrary ι)
  · intro γ hγ
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hγ
    simp only [dif_pos hγ, coe_filter, mem_univ, true_and, Set.mem_setOf_eq]
    exact hγ.choose_spec.1
  · intro γ₁ hγ₁ γ₂ hγ₂ heq
    simp only [coe_filter, mem_univ, true_and, Set.mem_setOf_eq] at hγ₁ hγ₂
    simp only [dif_pos hγ₁, dif_pos hγ₂] at heq
    have h1 := hγ₁.choose_spec; have h2 := hγ₂.choose_spec
    rw [← heq] at h2
    exact mul_right_cancel₀ h1.1
      (by linear_combination h1.2 - h2.2 : γ₁ * e₁ hγ₁.choose = γ₂ * e₁ hγ₁.choose)

theorem badCount_udr_le (C : Submodule F (ι → F)) (u₀ u₁ : ι → F) (d t : ℕ)
    (htn : t < Fintype.card ι)
    (hmd : ∀ a ∈ C, ∀ b ∈ C, (univ.filter (fun i => a i ≠ b i)).card < d → a = b)
    (hreg : 3 * (Fintype.card ι - t) < d)
    (G : Finset F) (S : F → Finset ι) (w : F → ι → F)
    (hSt : ∀ γ ∈ G, t ≤ (S γ).card)
    (hwC : ∀ γ ∈ G, w γ ∈ C)
    (hwS : ∀ γ ∈ G, ∀ i ∈ S γ, w γ i = u₀ i + γ • u₁ i)
    (hno : ∀ γ ∈ G, ¬ pairJointAgreesOn (C : Set (ι → F)) (S γ) u₀ u₁) :
    G.card ≤ 2 * (Fintype.card ι - t) := by
  classical
  by_cases hG : ∃ γa ∈ G, ∃ γb ∈ G, γa ≠ γb
  · obtain ⟨γa, haG, γb, hbG, hab⟩ := hG
    set T : Finset ι := S γa ∩ S γb with hTdef
    have hd_ab : γa - γb ≠ 0 := sub_ne_zero.mpr hab
    set c₁ : ι → F := (γa - γb)⁻¹ • (w γa - w γb) with hc₁def
    have hc₁C : c₁ ∈ C := C.smul_mem _ (C.sub_mem (hwC γa haG) (hwC γb hbG))
    have hc₁T : ∀ i ∈ T, c₁ i = u₁ i := by
      intro i hi
      rw [hTdef, mem_inter] at hi
      have ea := hwS γa haG i hi.1
      have eb := hwS γb hbG i hi.2
      have hwi : (w γa - w γb) i = (γa - γb) • u₁ i := by
        simp only [Pi.sub_apply, ea, eb, sub_smul]; abel
      simp only [hc₁def, Pi.smul_apply, hwi, inv_smul_smul₀ hd_ab]
    set c₀ : ι → F := w γa - γa • c₁ with hc₀def
    have hc₀C : c₀ ∈ C := C.sub_mem (hwC γa haG) (C.smul_mem _ hc₁C)
    have hc₀T : ∀ i ∈ T, c₀ i = u₀ i := by
      intro i hi
      have hci := hc₁T i hi
      have hmem := hi; rw [hTdef, mem_inter] at hmem
      have ea := hwS γa haG i hmem.1
      simp only [hc₀def, Pi.sub_apply, Pi.smul_apply, hci, ea, smul_eq_mul]; ring
    have hTcard : 2 * t ≤ Fintype.card ι + T.card := by
      have hun : (S γa ∪ S γb).card ≤ Fintype.card ι := by simpa using card_le_univ (S γa ∪ S γb)
      have hui : (S γa ∪ S γb).card + T.card = (S γa).card + (S γb).card :=
        card_union_add_card_inter (S γa) (S γb)
      have ha := hSt γa haG; have hb := hSt γb hbG
      omega
    set e₀ : ι → F := u₀ - c₀ with he₀def
    set e₁ : ι → F := u₁ - c₁ with he₁def
    have he₁T : ∀ i ∈ T, e₁ i = 0 := by
      intro i hi; simp only [he₁def, Pi.sub_apply, hc₁T i hi, sub_self]
    have hsupp : (univ.filter (fun i => e₁ i ≠ 0)).card ≤ 2 * (Fintype.card ι - t) := by
      have hsub : (univ.filter (fun i => e₁ i ≠ 0)) ⊆ Tᶜ := by
        intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
        simp only [mem_compl]; intro hiT; exact hi (he₁T i hiT)
      calc (univ.filter (fun i => e₁ i ≠ 0)).card ≤ Tᶜ.card := card_le_card hsub
        _ = Fintype.card ι - T.card := card_compl T
        _ ≤ 2 * (Fintype.card ι - t) := by omega
    have hGsub : G ⊆ univ.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0) := by
      intro γ hγ
      simp only [mem_filter, mem_univ, true_and]
      have hcollapse : w γ = c₀ + γ • c₁ := by
        apply hmd _ (hwC γ hγ) _ (C.add_mem hc₀C (C.smul_mem _ hc₁C))
        have hsub2 : (univ.filter (fun i => w γ i ≠ (c₀ + γ • c₁) i)) ⊆ (T ∩ S γ)ᶜ := by
          intro i hi; simp only [mem_filter, mem_univ, true_and] at hi
          simp only [mem_compl, mem_inter, not_and]; intro hiT hiS
          apply hi
          have e1 := hc₀T i hiT; have e2 := hc₁T i hiT; have e3 := hwS γ hγ i hiS
          simp only [Pi.add_apply, Pi.smul_apply, e1, e2, e3, smul_eq_mul]
        have hcardle : (univ.filter (fun i => w γ i ≠ (c₀ + γ • c₁) i)).card < d := by
          have hle := card_le_card hsub2
          rw [card_compl] at hle
          have hun : (T ∪ S γ).card ≤ Fintype.card ι := by simpa using card_le_univ (T ∪ S γ)
          have hui : (T ∪ S γ).card + (T ∩ S γ).card = T.card + (S γ).card :=
            card_union_add_card_inter T (S γ)
          have hsg := hSt γ hγ
          omega
        exact hcardle
      have hnpj := hno γ hγ
      have hexi : ∃ i ∈ S γ, ¬ (c₀ i = u₀ i ∧ c₁ i = u₁ i) := by
        by_contra hcon; push_neg at hcon
        exact hnpj ⟨c₀, hc₀C, c₁, hc₁C, fun i hi => hcon i hi⟩
      obtain ⟨i, hiS, hidis⟩ := hexi
      have hci := congrFun hcollapse i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hci
      have hsi := hwS γ hγ i hiS
      rw [smul_eq_mul] at hsi
      have hc : u₀ i + γ * u₁ i = c₀ i + γ * c₁ i := by rw [← hsi, hci]
      have haff : e₀ i + γ * e₁ i = 0 := by
        simp only [he₀def, he₁def, Pi.sub_apply]; linear_combination hc
      have he₁i : e₁ i ≠ 0 := by
        intro h0
        rw [h0, mul_zero, add_zero] at haff
        apply hidis
        refine ⟨?_, ?_⟩
        · have hz : u₀ i - c₀ i = 0 := by simpa only [he₀def, Pi.sub_apply] using haff
          exact (sub_eq_zero.mp hz).symm
        · have hz : u₁ i - c₁ i = 0 := by simpa only [he₁def, Pi.sub_apply] using h0
          exact (sub_eq_zero.mp hz).symm
      exact ⟨i, he₁i, haff⟩
    calc G.card
        ≤ (univ.filter (fun γ : F => ∃ i, e₁ i ≠ 0 ∧ e₀ i + γ * e₁ i = 0)).card := card_le_card hGsub
      _ ≤ (univ.filter (fun i => e₁ i ≠ 0)).card := badGamma_le e₀ e₁
      _ ≤ 2 * (Fintype.card ι - t) := hsupp
  · push_neg at hG
    have h1 : G.card ≤ 1 := Finset.card_le_one.mpr (fun a ha b hb => hG a ha b hb)
    omega

/-- RS minimum-distance, agreement form: degree-`<k` codewords disagreeing on `< n − k + 1`
coordinates are equal (via `ReedSolomon.code_eq_of_agree`). -/
theorem rs_min_dist (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι) :
    ∀ a ∈ (ReedSolomon.code α k : Set (ι → F)), ∀ b ∈ (ReedSolomon.code α k : Set (ι → F)),
      (univ.filter (fun i => a i ≠ b i)).card < Fintype.card ι - k + 1 → a = b := by
  intro a ha b hb hdis
  refine ReedSolomon.code_eq_of_agree hk ha hb (S := univ.filter (fun i => a i = b i))
    (fun i hi => (mem_filter.mp hi).2) ?_
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card (s := (univ : Finset ι))
    (p := fun i => a i = b i)
  simp only [Finset.card_univ] at hpart
  simp only [ne_eq] at hdis
  omega

open Classical in
/-- **Connected UDR MCA bound for Reed–Solomon (from scratch, no admit).** For `RS[F,α,k]` with
`k ≤ n` and the unique-decoding regime `3(n − ⌈(1-δ)n⌉) < n − k + 1`,
`ε_mca(RS, δ) ≤ 2(n − ⌈(1-δ)n⌉)/|F|`. -/
theorem epsMCA_rs_udr_le (α : ι ↪ F) (k : ℕ) [NeZero k] (hk : k ≤ Fintype.card ι) (δ : ℝ≥0)
    (htn : ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ < Fintype.card ι)
    (hreg : 3 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) < Fintype.card ι - k + 1) :
    epsMCA (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
      ≤ (2 * (Fintype.card ι - ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊) : ℕ) / (Fintype.card F : ℝ≥0∞) := by
  set t : ℕ := ⌈(1 - δ) * (Fintype.card ι : ℝ≥0)⌉₊ with htdef
  have hmd := rs_min_dist α k hk
  apply epsMCA_le_of_badCount_le (F := F) (A := F) (ReedSolomon.code α k : Set (ι → F)) δ
    (2 * (Fintype.card ι - t))
  intro u
  set G : Finset F :=
    univ.filter (fun γ : F => mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ) with hGdef
  set S : F → Finset ι := fun γ =>
    if h : mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ then h.choose else ∅ with hSdef
  set w : F → ι → F := fun γ =>
    if h : mcaEvent (ReedSolomon.code α k : Set (ι → F)) δ (u 0) (u 1) γ
      then (h.choose_spec.2.1).choose else 0 with hwdef
  refine badCount_udr_le (ReedSolomon.code α k) (u 0) (u 1) (Fintype.card ι - k + 1) t htn hmd hreg
    G S w ?_ ?_ ?_ ?_
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hSdef, dif_pos h]
    have hcardR : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ ((h.choose.card : ℕ) : ℝ≥0) := h.choose_spec.1
    rw [htdef]; exact Nat.ceil_le.mpr hcardR
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hwdef, dif_pos h]
    exact (h.choose_spec.2.1).choose_spec.1
  · intro γ hγ i hi
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hwdef, dif_pos h]
    simp only [hSdef, dif_pos h] at hi
    exact (h.choose_spec.2.1).choose_spec.2 i hi
  · intro γ hγ
    rw [hGdef, mem_filter] at hγ
    have h := hγ.2
    simp only [hSdef, dif_pos h]
    exact h.choose_spec.2.2

#print axioms badCount_udr_le
#print axioms epsMCA_rs_udr_le

end ProximityGap.UDRwire
