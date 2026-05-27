/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Ops
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.Ops

namespace ReedSolomon

variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]

private def subdomain_embed (i : ℕ) (k : Fin (2 ^ (n - i))) :
  Fin (2 ^ n) :=
  if hi : i ≥ n
  then 0  
  else ⟨2 ^ i * k.val, match k with
    | ⟨k, hk⟩ => by
      simp only at hk ⊢
      by_cases hk_zero : k = 0 <;> try (subst hk_zero; simp)
      calc 2 ^ i * k < 2 ^ i * 2 ^ (n - i) :=
              Nat.mul_lt_mul_of_pos_left hk (by positivity)
          _ = 2 ^ n := by rw [←pow_add, Nat.add_sub_of_le (by omega)]⟩

private lemma subdomain_embed_add (i : ℕ) (a b : Fin (2 ^ (n - i))) :
  subdomain_embed i (a + b) = subdomain_embed i a + subdomain_embed i b := by
  unfold subdomain_embed
  simp +decide [Fin.val_add]
  ring_nf
  norm_num [Fin.ext_iff, Fin.val_add, Fin.val_mul]
  by_cases hi : n ≤ i
  · simp [hi]
  · simp only [hi, ↓reduceDIte]
    rw [←add_mul, ←Nat.mul_mod_mul_right, ←pow_add,
      Nat.sub_add_cancel (by omega)]

private lemma subdomain_embed_zero (i : ℕ) : 
  subdomain_embed i 0 = (0 : Fin (2 ^ n)) := by
  unfold subdomain_embed
  aesop

private lemma subdomain_embed_injective (i : ℕ) :
  Function.Injective (subdomain_embed (n := n) i) := fun a b h ↦ by
  by_cases hi : n ≤ i
  · obtain ⟨a, ha⟩ := a
    obtain ⟨b, hb⟩ := b
    have : n - i = 0 := by omega
    rw [this] at ha
    rw [this] at hb
    simp_all
  · simp_all [Fin.ext_iff, subdomain_embed]

/-- Given a smooth coset FFT domain `ω` of log-order `n`
  this function returns its subdomain of log-order `n - i`.
-/
def subdomain (ω : D) (i : ℕ) :
  SmoothCosetFftDomain (n - i) F :=
  ⟨{ toFun := fun k ↦ mkSubgroupUnit ω (subdomain_embed i (Multiplicative.toAdd k))
     map_one' := by 
      aesop (add simp [subdomain_embed_zero, mkSubgroupUnit])
     map_mul' := by 
      aesop 
        (add simp [toAdd_mul, subdomain_embed_add,
                   mkSubgroupUnit, CosetFftDomainClass.map_add])
        (add safe (by field_simp)) },
   by
     intro a b h
     have h2 := CosetFftDomainClass.injective ω (by simpa [mkSubgroupUnit] using h)
     have h3 := Multiplicative.ofAdd.injective h2
     exact Multiplicative.ofAdd.injective (subdomain_embed_injective i h3),
  ⟨(ω 0) ^ 2 ^ i, (ω 0)⁻¹ ^ 2 ^ i, by simp, by simp⟩⟩

variable {ω : D} {x : F}

omit [DecidableEq F] in
lemma mem_subdomain_of_eq_vals
  {i j : ℕ}
  (hij : i = j) :
  x ∈ subdomain ω i ↔ x ∈ subdomain ω j := by rw [hij]

omit [DecidableEq F] in
@[simp]
lemma subdomain_generator_pow_generator (i : ℕ) :
  (subdomain ω i).cosetGenerator = ω 0 ^ 2 ^ i := rfl

omit [DecidableEq F] in
@[simp]
lemma mem_subdomain_0_iff_mem :
  x ∈ subdomain ω 0 ↔ x ∈ ω := by
  by_cases hn : n = 0
    <;> aesop 
          (add simp 
            [subdomain, 
             subdomain_embed, 
             mkSubgroupUnit, 
             mem_def, 
             CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

omit [DecidableEq F] in
lemma mem_subdomain_n_iff_eq_pow_generator : 
  x ∈ subdomain ω n ↔ x = ω 0 ^ 2 ^ n := by
  aesop
    (add simp [subdomain
    , subdomain_embed
    , mkSubgroupUnit
    , mem_def
    , CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain])

omit [DecidableEq F] in
private lemma mkSubgroupUnit_pow (ω : D) (a : Fin (2 ^ n)) (k : ℕ) :
    (mkSubgroupUnit ω a : F) ^ k = mkSubgroupUnit ω (k • a) := by
  induction k 
  · aesop (add simp [pow_zero, zero_nsmul, mkSubgroupUnit])
  · have := CosetFftDomainClass.map_add ω (‹_› • a) a
    aesop 
      (add simp 
        [pow_succ', 
         add_smul, 
         mkSubgroupUnit, 
         mul_add, 
         add_mul, 
         mul_assoc, 
         mul_comm, 
         mul_left_comm])

private lemma nat_mul_pow_mod {i j m n : ℕ} (hsum : j + i ≤ n) :
  (2 ^ i * (2 ^ j * m)) % 2 ^ n = (2 ^ (j + i) * (m % 2 ^ (n - (j + i)))) % 2 ^ n := by
  rw [←Nat.mod_add_div m (2 ^ (n - (j + i)))] 
  ring_nf 
  simp [mul_assoc, ←pow_add, add_tsub_cancel_of_le (by linarith : i + j ≤ n)]

private lemma fin_nsmul_val {m : ℕ} (k : ℕ) (a : Fin (2 ^ m)) :
  (k • a).val = (k * a.val) % 2 ^ m := by
  induction k <;> simp [Nat.succ_mul]
  simp_all [add_smul, Fin.val_add]

private lemma subdomain_embed_val {i : ℕ} (hi : i < n) (k : Fin (2 ^ (n - i))) :
  (subdomain_embed (n := n) i k).val = 2 ^ i * k.val := by grind +locals

omit [DecidableEq F] in
theorem pow_mem_of_mem {i j : ℕ} (hsum : j + i ≤ n) (h : x ∈ subdomain ω j) :
  x ^ 2 ^ i ∈ subdomain ω (j + i) := by
  obtain ⟨k, hk⟩ : 
    ∃ k : Fin (2 ^ (n - j)), x = (mkSubgroupUnit ω (subdomain_embed j k) : F) * (ω 0) ^ 2 ^ j := by
    obtain ⟨k, rfl⟩ := h
    exact ⟨k, mul_comm _ _⟩
  have hx_pow : 
    x ^ 2 ^ i = ((ω 0) ^ 2 ^ (j + i)) * (mkSubgroupUnit ω (2 ^ i • subdomain_embed j k) : F) := by
    convert congr_arg (· ^ 2 ^ i) hk using 1 
    ring_nf
    simp [←mkSubgroupUnit_pow]
  have h_mod : 
    (2 ^ i • subdomain_embed j k).val = (2 ^ (j + i) * (k.val % 2 ^ (n - (j + i)))) % 2 ^ n := by
    have h_mod : 
      (2 ^ i • subdomain_embed j k).val = (2 ^ i * (subdomain_embed j k).val) % 2 ^ n := by 
      convert fin_nsmul_val _ _
    by_cases hj : j < n 
    · simp_all only [subdomain_embed, ge_iff_le, smul_dite, nsmul_zero]
      split_ifs 
      · simp_all only [Fin.coe_ofNat_eq_mod, Nat.zero_mod, mul_zero]
        linarith
      · simp_all only [↓reduceDIte, pow_add, mul_assoc]
        convert nat_mul_pow_mod (show j + i ≤ n from hsum) using 1 
        ring_nf
    · have : n = j := by linarith
      aesop 
        (add simp [subdomain_embed, Nat.mod_one])
  have h_subdomain : (subdomain_embed (n := n) (j + i) ⟨k.val % 2 ^ (n - (j + i)),
    Nat.mod_lt _ (by positivity)⟩).val = 2 ^ (j + i) * (k.val % 2 ^ (n - (j + i))) := by
    by_cases hi : j + i ≥ n 
      <;> aesop 
            (add simp [subdomain_embed, Nat.mod_one]) 
            (add safe (by grind))
  generalize_proofs at *
  have h_eq : 
    2 ^ i • subdomain_embed j k = 
      subdomain_embed (j + i) ⟨k.val % 2 ^ (n - (j + i)), by assumption⟩ := Fin.ext <| by 
      simpa [Nat.mod_eq_of_lt (show 2 ^ (j + i) * (k.val % 2 ^ (n - (j + i))) < 
        2 ^ n from lt_of_lt_of_le 
          (Nat.mul_lt_mul_of_pos_left ‹_› (pow_pos (by decide) _)) 
          (by rw [← pow_add, Nat.add_sub_of_le hsum]))] 
      using h_mod.trans <| h_subdomain.symm ▸ 
        Nat.mod_eq_of_lt 
          (show 2 ^ (j + i) * (k.val % 2 ^ (n - (j + i))) < 2 ^ n from 
            lt_of_lt_of_le 
              (Nat.mul_lt_mul_of_pos_left ‹_› (pow_pos (by decide) _)) 
              (by rw [← pow_add, Nat.add_sub_of_le hsum]))
  generalize_proofs at *
  use Multiplicative.ofAdd ⟨k.val % 2 ^ (n - (j + i)), by assumption⟩
  generalize_proofs at *
  convert hx_pow.symm using 1
  exact Eq.symm 
    (Mathlib.Tactic.CancelDenoms.derive_trans₂ 
      rfl (congrArg Units.val (congrArg (mkSubgroupUnit ω) h_eq)) rfl)

private lemma subdomain_embed_of_le (i j : ℕ) (h : j ≤ i)
  (k : Fin (2 ^ (n - i))) :
  ∃ (l : Fin (2 ^ (n - j))), subdomain_embed i k = subdomain_embed j l := by
  by_cases hi : n ≤ i 
  · exact ⟨0, by simp [subdomain_embed, hi]⟩ 
  · refine ⟨⟨2 ^ (i - j) * k.val, ?_⟩, ?_⟩
    · calc 2 ^ (i - j) * k.val < 2 ^ (i - j) * 2 ^ (n - i) := by
            apply Nat.mul_lt_mul_of_pos_left k.isLt (by positivity)
          _ = 2 ^ (n - j) := by 
            rw [←pow_add, ←Nat.sub_add_comm h, Nat.add_sub_of_le (by omega)]
    · have : ¬n ≤ j := by omega  
      simp only [subdomain_embed, ge_iff_le, hi, ↓reduceDIte, this, Fin.ext_iff]
      rw [←mul_assoc, ←pow_add, Nat.add_sub_of_le h]

omit [DecidableEq F] in
lemma mem_subdomain_of_le_of_mem_subdomain (i j : ℕ) (h : j ≤ i)
  (hx : x ∈ subdomain ω i) :
  ω 0 ^ 2 ^ j * (ω 0)⁻¹ ^ 2 ^ i * x ∈ subdomain ω j := by
  simp only [subdomain, inv_pow, mem_def] at hx
  obtain ⟨k, hx⟩ := hx
  simp only [mkSubgroupUnit, CosetFftDomain.eval_coset_fft_domain_eq_eval_generator_mul_domain,
    MonoidHom.coe_mk, OneHom.coe_mk] at hx 
  have ⟨l, hl⟩ := subdomain_embed_of_le _ _ h (Multiplicative.toAdd k)
  rw [hl] at hx
  rw [hx, ←mul_assoc, mul_assoc (ω 0 ^ 2 ^ j)]
  aesop (add simp [CosetFftDomain.mem_iff_exists_mul])

end CosetFftDomainClass

end ReedSolomon
