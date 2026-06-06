import Mathlib
import ArkLib.Data.CodingTheory.ListDecoding.BKR06SubspacePoly
import ArkLib.ToMathlib.LinearizedSupport

noncomputable section
open Polynomial BigOperators Finset
namespace BKR06

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [Algebra F K]

local instance instFintypeSub (W : Submodule F K) : Fintype W := Fintype.ofFinite W

/-- Base case: subFinset ⊥ = {0}. -/
example : subFinset (⊥ : Submodule F K) = {0} := by
  ext x
  simp only [mem_subFinset, Submodule.mem_bot, Finset.mem_singleton]

/-- subspacePoly {0} = X. -/
example : subspacePoly ({0} : Finset K) = X := by
  unfold subspacePoly
  simp

/-- F-homogeneity of the subspace-polynomial evaluation map.
`eval (c • y) (subspacePoly (subFinset W)) = algebraMap c * eval y (...)`
for `c ∈ F`, via reindexing the product `w ↦ c • w` on `W` and `c^{q^v}=c`. -/
example (W : Submodule F K) (c : F) (y : K) :
    (subspacePoly (subFinset W)).eval (c • y)
      = (algebraMap F K c) * (subspacePoly (subFinset W)).eval y := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · -- c = 0: LHS = eval 0 = 0 (since 0 ∈ W), RHS = 0
    rw [zero_smul, map_zero, zero_mul]
    exact subspacePoly_eval_zero _ (by simp [W.zero_mem])
  · -- c ≠ 0: reindex
    have hcdef : ∀ (a : K), c • a = algebraMap F K c * a := fun a => Algebra.smul_def c a
    have hcK_ne : algebraMap F K c ≠ 0 := by
      simpa using (FaithfulSMul.algebraMap_injective F K).ne hc
    have hcard : (subFinset W).card = Fintype.card F ^ (Module.finrank F W) := by
      rw [subFinset]; simp only [Set.toFinset_card]
      exact Module.card_eq_pow_finrank (K := F) (V := W)
    unfold subspacePoly
    rw [eval_prod, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    -- reindex ℓ = c • ℓ' over the bijection ℓ' ↦ c • ℓ' of subFinset W
    have key : ∏ ℓ ∈ subFinset W, (c • y - ℓ)
        = ∏ ℓ' ∈ subFinset W, (c • y - c • ℓ') := by
      refine (Finset.prod_nbij' (fun ℓ' => c • ℓ') (fun ℓ => c⁻¹ • ℓ) ?_ ?_ ?_ ?_ ?_).symm
      · intro ℓ' hℓ'; rw [mem_subFinset] at hℓ' ⊢; exact W.smul_mem _ hℓ'
      · intro ℓ hℓ; rw [mem_subFinset] at hℓ ⊢; exact W.smul_mem _ hℓ
      · intro ℓ' _; simp only; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      · intro ℓ _; simp only; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      · intro ℓ' _; rfl
    rw [key]
    -- c•y - c•ℓ' = c•(y - ℓ') = algebraMap c * (y - ℓ')
    have hfac : ∀ ℓ' : K, c • y - c • ℓ' = algebraMap F K c * (y - ℓ') := by
      intro ℓ'; rw [← smul_sub, hcdef]
    simp only [hfac]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    -- (algebraMap c)^{q^v} = algebraMap c since c^q = c in F
    have hpow : (algebraMap F K c) ^ (Fintype.card F ^ Module.finrank F W) = algebraMap F K c := by
      rw [← map_pow, FiniteField.pow_card_pow]
    rw [hpow]

/-- Homogeneity as a standalone (for use below). -/
theorem sphom (W : Submodule F K) (c : F) (y : K) :
    (subspacePoly (subFinset W)).eval (c • y)
      = (algebraMap F K c) * (subspacePoly (subFinset W)).eval y := by
  classical
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul, map_zero, zero_mul]
    exact subspacePoly_eval_zero _ (by simp [W.zero_mem])
  · have hcdef : ∀ (a : K), c • a = algebraMap F K c * a := fun a => Algebra.smul_def c a
    have hcard : (subFinset W).card = Fintype.card F ^ (Module.finrank F W) := by
      rw [subFinset]; simp only [Set.toFinset_card]
      exact Module.card_eq_pow_finrank (K := F) (V := W)
    unfold subspacePoly
    rw [eval_prod, eval_prod]
    simp only [eval_sub, eval_X, eval_C]
    have key : ∏ ℓ ∈ subFinset W, (c • y - ℓ)
        = ∏ ℓ' ∈ subFinset W, (c • y - c • ℓ') := by
      refine (Finset.prod_nbij' (fun ℓ' => c • ℓ') (fun ℓ => c⁻¹ • ℓ) ?_ ?_ ?_ ?_ ?_).symm
      · intro ℓ' hℓ'; rw [mem_subFinset] at hℓ' ⊢; exact W.smul_mem _ hℓ'
      · intro ℓ hℓ; rw [mem_subFinset] at hℓ ⊢; exact W.smul_mem _ hℓ
      · intro ℓ' _; simp only; rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      · intro ℓ _; simp only; rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
      · intro ℓ' _; rfl
    rw [key]
    have hfac : ∀ ℓ' : K, c • y - c • ℓ' = algebraMap F K c * (y - ℓ') := by
      intro ℓ'; rw [← smul_sub, hcdef]
    simp only [hfac]
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    rw [← map_pow, FiniteField.pow_card_pow]

/-- Roots of the recursion RHS: every `y ∈ W₀ ⊔ span{x}` is a root of
`f^q − C(a^(q-1))·f` where `f = subspacePoly (subFinset W₀)`, `a = eval x f`. -/
example (W₀ : Submodule F K) (x : K) (y : K)
    (hy : y ∈ W₀ ⊔ Submodule.span F {x}) :
    let f := subspacePoly (subFinset W₀)
    let q := Fintype.card F
    let a := f.eval x
    (f ^ q - C (a ^ (q - 1)) * f).eval y = 0 := by
  intro f q a
  rw [Submodule.mem_sup] at hy
  obtain ⟨w, hw, z, hz, rfl⟩ := hy
  rw [Submodule.mem_span_singleton] at hz
  obtain ⟨c, rfl⟩ := hz
  -- eval (w + c•x) f = eval w f + eval (c•x) f = 0 + algebraMap c * a
  have hadd : f.eval (w + c • x) = f.eval w + f.eval (c • x) :=
    subspacePoly_eval_add_submodule W₀ w (c • x)
  have hw0 : f.eval w = 0 := subspacePoly_eval_zero _ (by simp [hw])
  have hcx : f.eval (c • x) = algebraMap F K c * a := sphom W₀ c x
  have hfy : f.eval (w + c • x) = algebraMap F K c * a := by rw [hadd, hw0, hcx, zero_add]
  -- eval RHS = (eval f)^q - a^(q-1) * (eval f)
  simp only [eval_sub, eval_pow, eval_mul, eval_C]
  rw [hfy]
  -- (algebraMap c * a)^q - a^(q-1) * (algebraMap c * a) = 0
  have hq1 : 1 ≤ q := Fintype.card_pos
  have hcpow : (algebraMap F K c) ^ q = algebraMap F K c := by
    rw [← map_pow, FiniteField.pow_card]
  rw [mul_pow, hcpow]
  -- algebraMap c * a^q - a^(q-1) * (algebraMap c * a)
  -- = algebraMap c * a^q - algebraMap c * (a^(q-1) * a)
  have ha : a ^ (q - 1) * a = a ^ q := by
    rw [← pow_succ]; congr 1; omega
  ring_nf
  rw [show q - 1 + 1 = q by omega]
  ring

end BKR06
