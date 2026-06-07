/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov

[BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes" by Eli Ben-Sasson,
Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.

Using {https://eprint.iacr.org/2020/654}, version 20210703:203025.
-/

import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Domain.CosetFftDomain.Defs
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.BatchedFri.Spec.General
import ArkLib.ProofSystem.Fri.Spec.General
import ArkLib.ProofSystem.Fri.Spec.SingleRound
import ArkLib.OracleReduction.Security.Basic
import ToMathlib.Control.OptionT
import ArkLib.ToMathlib.List.Basic
import ArkLib.ToMathlib.Finset.Basic
import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
# Security of the Batched FRI protocol

We develop the security analysis of the Batched FRI oracle reduction following [BCIKS20]. The file
sets up the coset-evaluation machinery (`cosetEnum`, `cosetG`, `VDM` and its inverse `VDMInv`, the
`fin_equiv_coset` reindexing) used to reason about proximity over the smooth coset FFT evaluation
domains, towards completeness and soundness statements for the batched protocol.
-/

namespace Fri
section Fri

open OracleComp OracleSpec ProtocolSpec ReedSolomon Domain
open NNReal Finset Function ProbabilityTheory

variable {𝔽 : Type} [NonBinaryField 𝔽] [Fintype 𝔽] [DecidableEq 𝔽] [Nontrivial 𝔽]
variable (n : ℕ)
variable (g : 𝔽ˣ) {k : ℕ}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable {i : Fin (k + 1)}
variable {ω : SmoothCosetFftDomain n 𝔽}

attribute [instance high] Spec.QueryRound.instOracleInterfaceMessagePSpec

instance {F : Type} [Field F] {a : F} [inst : NeZero a] : Invertible a where
  invOf := a⁻¹
  invOf_mul_self := by field_simp [inst.out]
  mul_invOf_self := by field_simp [inst.out]

section Completeness

abbrev evalDomainSigma {n k : ℕ} (s : Fin (k + 1) → ℕ+)
  (ω : SmoothCosetFftDomain n 𝔽) (i : ℕ) :=
  ω.subdomain (∑ j' ∈ finRangeTo (k + 1) i, s j')

def cosetEnum (s₀ : evalDomainSigma s ω i) (k_le_n : ∑ j', (s j').1 ≤ n)
    (j : Fin (2 ^ (s i).1)) : evalDomainSigma s ω ↑i :=
  let r : {x | x ∈ ω.toFftDomain.subdomain (n - ↑(s i))} :=
    ⟨ω.toFftDomain.subdomain (n - (s i).1)
      ⟨j.1,
        by
          have s_i_lim : (s i).1 < n + 1 := by
            apply Nat.lt_succ_of_le
            rw [Finset.sum_eq_sum_diff_singleton_add (i := i) (by simp)] at k_le_n
            apply (swap <| Nat.le_trans) k_le_n
            omega
          rcases j with ⟨j, h⟩
          have : n - (n - (s i).1) = (s i).1 := by
            apply Nat.sub_sub_self
            exact Nat.le_of_lt_succ s_i_lim
          rw [this]
          convert h
      ⟩,
      CosetFftDomainClass.mem_self
    ⟩
  let x : (evalDomainSigma s ω ↑i).toFinset := ⟨
    s₀.1 * r.1,
    by {
      rw [CosetFftDomainClass.mem_toFinset_iff_mem]
      exact CosetFftDomainClass.mem_subdomain_of_mem_subdomain_of_mem_fft_subdomain (by {
        apply Nat.le_sub_of_add_le
        apply le_trans
          (b := ∑ j' ∈ finRangeTo (k + 1) ↑i, (s j').1 + (s i).1)
          (c := n)
        · constructor
        · rw [←sum_finRangeTo_add_one]
          apply le_trans (b := ∑ j', (s j').1) <;> try omega
          apply Finset.sum_le_sum_of_subset
          simp
      })  (by {
        rcases s₀ with ⟨s₀, hs₀⟩
        simp only
        simp only [evalDomainSigma] at hs₀
        rw [CosetFftDomain.mem_toFinset_iff_mem] at hs₀
        exact hs₀
      }) r.2
    }
  ⟩
  ↑x

def cosetG (s₀ : evalDomainSigma s ω ↑i)
    : Finset (evalDomainSigma s ω ↑i) :=
  if k_le_n : ∑ j', (s j').1 ≤ n
  then
    (Finset.univ).image (cosetEnum n s s₀ k_le_n)
  else ∅

def pows (z : 𝔽) (ℓ : ℕ) : Matrix Unit (Fin ℓ) 𝔽 :=
  Matrix.of <| fun _ j => z ^ j.val

def VDM (s₀ : evalDomainSigma s ω ↑i) :
    Matrix (Fin (2 ^ (s i : ℕ))) (Fin (2 ^ (s i : ℕ))) 𝔽 :=
  if k_le_n : (∑ j', (s j').1) ≤ n
  then Matrix.vandermonde (fun j => (cosetEnum n s s₀ k_le_n j).1)
  else 1

def cosetEnum' (s₀ : evalDomainSigma s ω ↑i)
    (k_le_n : ∑ j', (s j').1 ≤ n)
  (j : Fin (2 ^ (s i).1)) : cosetG n s s₀ :=
  ⟨
    cosetEnum n s s₀ k_le_n j,
    by simp only [cosetG, k_le_n, ↓reduceDIte]; exact mem_image_of_mem _ (mem_univ _)
  ⟩

noncomputable def fin_equiv_coset (s₀ : evalDomainSigma s ω ↑i)
    (k_le_n : ∑ j', (s j').1 ≤ n) :
    (Fin (2 ^ (s i).1)) ≃ { x // x ∈ cosetG n s s₀ } := by
  apply Equiv.ofBijective (cosetEnum' n s s₀ k_le_n)
  unfold cosetEnum' cosetEnum
  unfold Function.Bijective
  apply And.intro
  · intros a b h
    simp only [finRangeTo.eq_1, Subtype.mk.injEq] at h
    have h := congr_arg Subtype.val h
    simp only [mul_eq_mul_left_iff] at h
    rcases h with h | h
    · have h := FftDomain.injective h
      aesop
    · rcases s₀ with ⟨s₀, hs₀⟩
      subst h
      simp only [finRangeTo.eq_1, evalDomainSigma] at hs₀
      rw [CosetFftDomainClass.mem_toFinset_iff_mem] at hs₀
      have hs₀ := CosetFftDomainClass.not_zero_mem hs₀
      simp at hs₀
  · rintro ⟨⟨y, h'⟩, h⟩
    simp only [finRangeTo.eq_1, Subtype.mk.injEq]
    simp only [cosetG, k_le_n, ↓reduceDIte] at h
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp h
    have ha := congr_arg Subtype.val ha
    simp only [finRangeTo.eq_1, cosetEnum] at ha
    exact ⟨a, by aesop⟩

def invertibleDomain (s₀ : evalDomainSigma s ω ↑i) : Invertible (VDM n s s₀) := by
  haveI : NeZero (VDM n s s₀).det := by
    constructor
    unfold VDM
    split_ifs with cond
    · simp only [Matrix.det_vandermonde]
      rw [Finset.prod_ne_zero_iff]
      intros i' _
      rw [Finset.prod_ne_zero_iff]
      intros j' h'
      have : i' ≠ j' := by
        rename_i a
        simp_all only [mem_univ, mem_Ioi, ne_eq]
        obtain ⟨val, property⟩ := s₀
        simp_all only [finRangeTo]
        apply Aesop.BuiltinRules.not_intro
        intro a
        subst a
        simp_all only [lt_self_iff_false]
      intros contra
      apply this
      rw [sub_eq_zero, cosetEnum, cosetEnum] at contra
      simp only [finRangeTo,
        mul_eq_mul_left_iff] at contra
      rcases contra with contra | contra
      · have h := FftDomain.injective contra
        simp only [Fin.mk.injEq] at h
        ext
        exact (symm h)
      · rcases s₀ with ⟨s₀, hs₀⟩
        subst contra
        simp only [Nat.succ_eq_add_one, finRangeTo.eq_1, Fin.ofNat_eq_cast, Fin.val_natCast,
          evalDomainSigma] at hs₀
        rw [CosetFftDomainClass.mem_toFinset_iff_mem] at hs₀
        have hs₀ := CosetFftDomainClass.not_zero_mem hs₀
        simp at hs₀
    · simp
  apply @Matrix.invertibleOfDetInvertible

noncomputable def VDMInv (s₀ : evalDomainSigma s ω ↑i)
  (k_le_n : ∑ j', (s j').1 ≤ n) :
  Matrix (Fin (2 ^ (s i).1)) (cosetG n s s₀) 𝔽 :=
  Matrix.reindex (Equiv.refl _) (fin_equiv_coset n s s₀ k_le_n)
  (invertibleDomain n s s₀).invOf

lemma g_elem_zpower_iff_exists_nat {G : Type} [Group G] [Finite G] {gen g : G} :
    g ∈ Subgroup.zpowers gen ↔ ∃ n : ℕ, g = gen ^ n ∧ n < orderOf gen := by
  have := isOfFinOrder_of_finite gen
  refine ⟨fun h ↦ ?p₁, ?p₂⟩
  · obtain ⟨k, h⟩ := Subgroup.mem_zpowers_iff.1 h
    let k' := k % orderOf gen
    have pow_pos : 0 ≤ k' := by apply Int.emod_nonneg; simp [*]
    obtain ⟨n, h'⟩ : ∃ n : ℕ, n = k' := by rcases k' with k' | k' <;> [(use k'; grind); aesop]
    use n
    have : gen ^ n = gen ^ k := by have := zpow_mod_orderOf gen k; grind [zpow_natCast]
    have : n < orderOf gen := by zify; rw [h']; apply Int.emod_lt; simp [isOfFinOrder_of_finite gen]
    grind
  · grind [Subgroup.npow_mem_zpowers]

open Matrix in
noncomputable def f_succ'
  (f : evalDomainSigma s ω ↑i → 𝔽)
  (z : 𝔽) (k_le_n : ∑ j', ↑(s j') ≤ n)
  (s₀' : evalDomainSigma s ω (↑i + 1)) : 𝔽 :=
  have :
    ∃ s₀ : (ω.subdomain (∑ j' ∈ finRangeTo _ (i.1), (s j').1)).toFinset,
      s₀.1 ^ (2 ^ (s i).1) = s₀'.1 := by
    rcases s₀' with ⟨s₀', hs₀'⟩
    simp only [Fin.val_natCast]
    simp only [evalDomainSigma] at hs₀'
    rw [CosetFftDomain.mem_toFinset_iff_mem] at hs₀'
    rw [CosetFftDomainClass.mem_subdomain_of_eq_vals
      (ω := ω)
      (j := (∑ j' ∈ finRangeTo (k + 1) ↑i, (s j').1 + (s i).1))
      (by {
        rw [←sum_finRangeTo_add_one]
        rfl
    })] at hs₀'
    have h := CosetFftDomainClass.root_exists (ω := ω)
      (i := (∑ j' ∈ finRangeTo (k + 1) ↑i, ↑(s j')))
      (j := (s i).1)
      (by {
        trans (∑ j' ∈ finRangeTo _ (i.1 + 1), (s j').1)
        rw [sum_finRangeTo_add_one]
        rfl
        apply (swap le_trans) k_le_n
        apply Finset.sum_le_sum_of_subset (by simp)
      })
      hs₀'
    rcases h with ⟨y, ⟨h1, h2⟩⟩
    exists ⟨y, by {
      rw [CosetFftDomain.mem_toFinset_iff_mem]
      exact h1
    }⟩
  let s₀ := Classical.choose this
  (pows z _ *ᵥ VDMInv n s s₀ k_le_n *ᵥ Finset.restrict (cosetG n s s₀) f) ()

private lemma rs_code_mem_of_card_le_degree
    {ι : Type} [Fintype ι] {F : Type} [Field F]
    {α : ι ↪ F} {deg : ℕ} (hcard : Fintype.card ι ≤ deg) (f : ι → F) :
    f ∈ ReedSolomon.code α deg := by
  letI : DecidableEq ι := Classical.decEq ι
  refine ReedSolomon.mem_code_of_polynomial_of_degree_lt_of_eval
    (Lagrange.interpolate Finset.univ α f) ?_ ?_
  · have hdeg_card : (Lagrange.interpolate (Finset.univ : Finset ι) α f).degree <
        (Fintype.card ι : WithBot ℕ) := by
      simpa using
        (Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset ι)) (v := α) (r := f)
          (by intro x _ y _ hxy; exact α.injective hxy))
    exact lt_of_lt_of_le hdeg_card (by exact_mod_cast hcard)
  · intro x
    exact (Lagrange.eval_interpolate_at_node (s := (Finset.univ : Finset ι))
      (v := α) (r := f)
      (by intro x _ y _ hxy; exact α.injective hxy)
      (Finset.mem_univ x)).symm

omit [Fintype 𝔽] in
/-- This theorem asserts that given an appropriate codeword,
  `f` of an appropriate Reed-Solomon code, the result of honestly folding the corresponding
  polynomial is then itself a member of the next Reed-Solomon code.

  Corresponds to Claim 8.1 of [BCIKS20] -/
lemma fri_round_consistency_completeness
    {f : ReedSolomon.code
    (⟨fun x => x, by simp⟩ : evalDomainSigma s ω i ↪ 𝔽)
    (2 ^ (n - (∑ j' ∈ finRangeTo _ i, (s j' : ℕ))))}
  {z : 𝔽}
  (k_le_n : ∑ j', ↑(s j') ≤ n)
  :
  f_succ' n s f.val z k_le_n ∈
    (ReedSolomon.code
      (⟨fun x => x, by simp⟩ : (evalDomainSigma s ω (i.1 + 1)).toFinset ↪ 𝔽)
      (2 ^ (n - (∑ j' ∈ finRangeTo _ (i.1 + 1), (s j' : ℕ))))
    ).carrier
  := by
  refine rs_code_mem_of_card_le_degree ?_ _
  rw [Fintype.card_coe]
  refine le_of_eq ?_
  simp only [evalDomainSigma, Domain.CosetFftDomainClass.card_toFinset]
  exact Fintype.card_fin _

end Completeness

section Soundness

variable (domain_size_cond : (2 ^ (∑ i, (s i : ℕ))) * d ≤ 2 ^ n)

/-- Affine space: {g | ∃ x : Fin t.succ → 𝔽, x 0 = 1 ∧ g = ∑ i, x i • f i  }
-/
def Fₛ {ι : Type} [Fintype ι] {t : ℕ} (f : Fin t.succ → (ι → 𝔽)) : AffineSubspace 𝔽 (ι → 𝔽) :=
  f 0 +ᵥ affineSpan 𝔽 (Finset.univ.image (f ∘ Fin.succ))

noncomputable def correlated_agreement_density {ι : Type} [Fintype ι]
  [Fintype 𝔽]
  (Fₛ : AffineSubspace 𝔽 (ι → 𝔽)) (V : Submodule 𝔽 (ι → 𝔽)) : ℝ :=
  haveI : Fintype Fₛ.carrier := Set.Finite.fintype (Set.toFinite _)
  haveI : Fintype V.carrier := Set.Finite.fintype (Set.toFinite _)
  let Fc := Fₛ.carrier.toFinset
  let Vc := V.carrier.toFinset
  (Fc ∩ Vc).card / Fc.card

open Polynomial

/-! ### Query-round acceptance analysis (Claim 8.2 combinatorial core)

The mathematical heart of the FRI query-round soundness analysis (Claim 8.2 of [BCIKS20])
is a purely combinatorial fact, independent of the oracle-reduction plumbing:

If a verifier makes `t` *independent uniform* queries into a domain `ι` of size `N`, and the
set `G ⊆ ι` of "good" positions (positions on which a query fails to detect the corruption)
has density `|G| / N ≤ 1 - δ`, then the probability that *all* `t` queries land in `G`
(the soundness-failure / accept-the-corrupted-word event) is at most `(1 - δ) ^ t`.

We formalise the failure probability as the ratio of the number of accepting query tuples
(`|G| ^ t`) to all query tuples (`N ^ t`), which equals `(|G| / N) ^ t ≤ (1 - δ) ^ t`.
These are real proved theorems (no `sorry`, no new axioms), and they are wired into the
`FriQuerySoundnessParts.query_round_acceptance_bound` frontier below via
`queryRoundAcceptanceBound`. -/

namespace QueryRound

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The number of length-`t` query tuples landing entirely in a set `G` is `|G| ^ t`.
This counts the accepting (corruption-missing) query transcripts. -/
theorem card_allQueriesIn (G : Finset ι) (t : ℕ) :
    (Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card = G.card ^ t := by
  classical
  have hpi : (Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G))
      = Fintype.piFinset (fun _ : Fin t => G) := by
    ext q
    simp [Fintype.mem_piFinset]
  rw [hpi, Fintype.card_piFinset]
  simp

omit [DecidableEq ι] in
/-- **Per-round acceptance probability bound.** If the good set `G` has density at most
`1 - δ`, then a single uniform query lands in `G` with probability `|G| / N ≤ 1 - δ`. -/
theorem singleQuery_acceptance_le
    (G : Finset ι) (δ : ℝ≥0)
    (hN : 0 < (Fintype.card ι))
    (h_density : (G.card : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι)) :
    (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ := by
  rw [div_le_iff₀ (by exact_mod_cast hN)]
  exact h_density

/-- **Query-round acceptance bound (product form).** Over `t` independent uniform queries,
the probability that all of them land in the good set `G` (acceptance / soundness-failure
event) is `|G| ^ t / N ^ t = (|G| / N) ^ t ≤ (1 - δ) ^ t`.

This is the combinatorial core of Claim 8.2: a `δ`-far word is accepted by the `t`-query
round with probability at most `(1 - δ) ^ t`. -/
theorem queryRound_acceptance_le
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ)
    (hN : 0 < (Fintype.card ι))
    (h_density : (G.card : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι)) :
    ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
        / (Fintype.card ι) ^ t
      ≤ (1 - δ) ^ t := by
  rw [card_allQueriesIn G t]
  push_cast
  rw [← div_pow]
  have hbase : (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ :=
    singleQuery_acceptance_le G δ hN h_density
  exact pow_le_pow_left₀ (by positivity) hbase t

omit [DecidableEq ι] in
/-- **Query-round acceptance bound (density-ratio form).**  This is the same combinatorial
query-round bound as `queryRound_acceptance_le`, but with the natural density hypothesis
`|G| / N ≤ 1 - δ` exposed directly. -/
theorem queryRound_acceptance_le_of_density
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ)
    (h_density : (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ) :
    ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
        / (Fintype.card ι) ^ t
      ≤ (1 - δ) ^ t := by
  rw [card_allQueriesIn G t]
  push_cast
  rw [← div_pow]
  exact pow_le_pow_left₀ (by positivity) h_density t

/-- Geometric amplification: when `0 < δ ≤ 1` the per-round acceptance bound `(1 - δ) ^ t`
is antitone in the number of query repetitions `t`, so the query phase drives the
soundness error to zero geometrically. -/
theorem queryRound_acceptance_antitone
    (δ : ℝ≥0) {t₁ t₂ : ℕ} (h : t₁ ≤ t₂) :
    (1 - δ) ^ t₂ ≤ (1 - δ) ^ t₁ :=
  pow_le_pow_of_le_one (by positivity) tsub_le_self h

end QueryRound

/-- The fully discharged query-round acceptance proposition used to instantiate the
`FriQuerySoundnessParts.query_round_acceptance_bound` frontier field. It packages the proved
combinatorial bound `|G| ^ t / N ^ t ≤ (1 - δ) ^ t` for the good (corruption-missing) set `G`
of density at most `1 - δ`. -/
def queryRoundAcceptanceBound
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) : Prop :=
  0 < (Fintype.card ι) →
    (G.card : ℝ≥0) ≤ (1 - δ) * (Fintype.card ι) →
      ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
          / (Fintype.card ι) ^ t
        ≤ (1 - δ) ^ t

/-- `queryRoundAcceptanceBound` is a proved theorem: the query-round acceptance probability
is bounded by `(1 - δ) ^ t`. This discharges the query-round ingredient of Claim 8.2. -/
theorem queryRoundAcceptanceBound_holds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) :
    queryRoundAcceptanceBound G δ t := by
  intro hN h_density
  exact QueryRound.queryRound_acceptance_le G δ t hN h_density

/-- Public density-ratio front door for the proved query-round acceptance inequality.

This is useful when downstream proximity arguments have already produced the normalized density
bound `|G| / N ≤ 1 - δ`, avoiding a round trip through the multiplicative card form. -/
theorem queryRoundAcceptanceBound_of_density
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ)
    (h_density : (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ) :
    ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
        / (Fintype.card ι) ^ t
      ≤ (1 - δ) ^ t :=
  QueryRound.queryRound_acceptance_le_of_density G δ t h_density

/-- Normalized-density variant of the proved query-round acceptance proposition.  This packages
the same count of accepting query tuples, but exposes the hypothesis in the normalized form that
proximity arguments usually produce. -/
def queryRoundDensityBound
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) : Prop :=
  (G.card : ℝ≥0) / (Fintype.card ι) ≤ 1 - δ →
    ((Finset.univ.filter (fun q : Fin t → ι => ∀ j, q j ∈ G)).card : ℝ≥0)
        / (Fintype.card ι) ^ t
      ≤ (1 - δ) ^ t

/-- `queryRoundDensityBound` is proved by the density-ratio query-round theorem. -/
theorem queryRoundDensityBound_holds
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (δ : ℝ≥0) (t : ℕ) :
    queryRoundDensityBound G δ t := by
  intro h_density
  exact queryRoundAcceptanceBound_of_density G δ t h_density

noncomputable def oracleImpl
    (l : ℕ) (z : Fin (k + 1) → 𝔽) (f : (ω.subdomain 0) → 𝔽) :
  QueryImpl
    ([]ₒ + ([Spec.FinalOracleStatement s ω]ₒ + [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ))
    (OracleComp [(Spec.QueryRound.pSpec (ω := ω) l).Message]ₒ) := by
  intro q
  rcases q with i | q
  · exact PEmpty.elim i
  · rcases q with q | q
    · rcases q with ⟨i, dom⟩
      let f0 := Lagrange.interpolate Finset.univ (fun v => v.1) f
      let chals : List (Fin (k + 1) × 𝔽) :=
        ((List.finRange (k + 1)).map fun i => (i, z i)).take i.1
      let fi : 𝔽[X] := List.foldl (fun f (i, α) => FoldingPolynomial.polyFold f (s i) α) f0 chals
      let st : Spec.FinalOracleStatement (F := 𝔽) s ω i :=
        if h : i.1 = k + 1 then
          cast (by simp [Spec.FinalOracleStatement, h]; rfl)
            (⟨fi.toImpl, CompPoly.CPolynomial.Raw.isCanonical_toImpl fi⟩ :
              CompPoly.CPolynomial 𝔽)
        else
          cast
            (by {
              simp [Spec.FinalOracleStatement, h]
              rfl
            })
            (fun x : ω.subdomain (∑ j' ∈ finRangeTo _ i.1, s j') => fi.eval x.1)
      exact pure <| (Spec.finalOracleStatementInterface s (ω := ω) i).answer st dom
    · rcases q with ⟨i, t⟩
      exact liftM <|
        cast
          (β := OracleQuery
            [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ
            (([]ₒ +
                ([Spec.FinalOracleStatement s (ω := ω)]ₒ +
                  [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ)).Range
              (Sum.inr (Sum.inr ⟨i, t⟩))))
          (by rfl)
          (query (spec := [(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ) ⟨i, t⟩)

instance {l : ℕ} : ([(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ).Inhabited where
  inhabited_B := by
    intro i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1.1 = 0 := by omega
    have h := this ▸ i.1.2
    simp at h

instance {l : ℕ} : ([(Spec.QueryRound.pSpec l (ω := ω)).Message]ₒ).Fintype where
  fintype_B := by
    intro i
    unfold Spec.QueryRound.pSpec MessageIdx at i
    have : i.1.1 = 0 := by omega
    have h := this ▸ i.1.2
    simp at h

open ENNReal in
noncomputable def εC
    (𝔽 : Type) [Fintype 𝔽] (n : ℕ) {k : ℕ} (s : Fin (k + 1) → ℕ+) (m : ℕ) (ρ_sqrt : ℝ≥0) : ℝ≥0∞ :=
  ENNReal.ofReal <|
      (m + (1 : ℚ)/2)^7 * (2^n)^2
        / ((2 * ρ_sqrt ^ 3) * (Fintype.card 𝔽))
      + (∑ i, 2 ^ (s i).1) * (2 * m + 1) * (2 ^ n + 1) / (Fintype.card 𝔽 * ρ_sqrt)

private abbrev fullChallengeProtocol (t l : ℕ) (ω : SmoothCosetFftDomain n 𝔽) :=
  (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
    (Spec.pSpecFold k (ω := ω) s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ Spec.QueryRound.pSpec l (ω := ω))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j,
      Inhabited
        ((fullChallengeProtocol
            n
            (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j) := by
  letI : ∀ j, Inhabited ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge j) := by
    infer_instance
  letI : ∀ j, Inhabited ((Spec.pSpecFold k (ω := ω) s).Challenge j) := by
    infer_instance
  letI : ∀ j, Inhabited ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    infer_instance
  letI : ∀ j, Inhabited ((Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    infer_instance
  letI :
      ∀ j,
        Inhabited
          ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
      (α₁ := (Spec.pSpecFold k s).dir)
      (β₁ := (Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (α₂ := (Spec.pSpecFold k s).Type)
      (β₂ := (Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.pSpecFold k s).Challenge ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge ⟨i, h⟩)))
      i h
  letI :
      ∀ j,
        Inhabited
          ((Spec.pSpecFold k (ω := ω) s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (β₁ := (Spec.QueryRound.pSpec (ω := ω) l).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (β₂ := (Spec.QueryRound.pSpec (ω := ω) l).Type)
      (fun i h =>
        inferInstanceAs
          (Inhabited
            ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge
              ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Inhabited ((Spec.QueryRound.pSpec (ω := ω) l).Challenge ⟨i, h⟩)))
      i h
  intro ⟨i, h⟩
  exact Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → Inhabited type)
    (α₁ := (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).dir)
    (β₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).dir)
    (α₂ := (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Type)
    (β₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).Type)
    (fun i h =>
      inferInstanceAs (Inhabited ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge ⟨i, h⟩)))
    (fun i h =>
      inferInstanceAs
        (Inhabited
          ((Spec.pSpecFold (ω := ω) k s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge
            ⟨i, h⟩)))
    i h

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j,
      Fintype
        ((fullChallengeProtocol
            n
            (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j) := by
  letI : ∀ j, Fintype ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.pSpecFold (ω := ω) k s).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    infer_instance
  letI : ∀ j, Fintype ((Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    infer_instance
  letI :
      ∀ j,
        Fintype
          ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s).dir)
      (β₁ := (Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s).Type)
      (β₂ := (Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.pSpecFold (ω := ω) k s).Challenge ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.FinalFoldPhase.pSpec 𝔽).Challenge ⟨i, h⟩)))
      i h
  letI :
      ∀ j,
        Fintype
          ((Spec.pSpecFold (ω := ω) k s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec (ω := ω) l).Challenge j) := by
    intro ⟨i, h⟩
    exact Fin.fappend₂ (A := Direction) (B := Type)
      (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
      (α₁ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).dir)
      (β₁ := (Spec.QueryRound.pSpec (ω := ω) l).dir)
      (α₂ := (Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Type)
      (β₂ := (Spec.QueryRound.pSpec (ω := ω) l).Type)
      (fun i h =>
        inferInstanceAs
          (Fintype
            ((Spec.pSpecFold (ω := ω) k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽).Challenge
              ⟨i, h⟩)))
      (fun i h =>
        inferInstanceAs (Fintype ((Spec.QueryRound.pSpec (ω := ω) l).Challenge ⟨i, h⟩)))
      i h
  intro ⟨i, h⟩
  exact Fin.fappend₂ (A := Direction) (B := Type)
    (F := fun dir type => (h : dir = .V_to_P) → Fintype type)
    (α₁ := (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).dir)
    (β₁ := (Spec.pSpecFold k (ω := ω) s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec (ω := ω) l).dir)
    (α₂ := (BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Type)
    (β₂ := (Spec.pSpecFold k (ω := ω) s ++ₚ
      Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
        Spec.QueryRound.pSpec l (ω := ω)).Type)
    (fun i h =>
      inferInstanceAs (Fintype ((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t).Challenge ⟨i, h⟩)))
    (fun i h =>
      inferInstanceAs
        (Fintype
          ((Spec.pSpecFold k (ω := ω) s ++ₚ
              Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                Spec.QueryRound.pSpec l (ω := ω)).Challenge
            ⟨i, h⟩)))
    i h

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([(fullChallengeProtocol
        n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge]ₒ).Inhabited where
  inhabited_B := by
    intro q
    rcases q with ⟨i, u⟩
    cases u
    change Inhabited
      ((fullChallengeProtocol n (𝔽 := 𝔽) (k := k) (s := s) t l ω).Challenge i)
    infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([(fullChallengeProtocol
        n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge]ₒ).Fintype where
  fintype_B := by
    intro q
    rcases q with ⟨i, u⟩
    cases u
    change Fintype
      ((fullChallengeProtocol n (𝔽 := 𝔽) (k := k) (s := s) t l (ω := ω)).Challenge i)
    infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j, Inhabited
      (((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
          (Spec.pSpecFold k (ω := ω) s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge j) := by
  simpa [fullChallengeProtocol] using
    (inferInstance :
      ∀ j,
        Inhabited
          ((fullChallengeProtocol
              n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ∀ j, Fintype
      (((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge j) := by
  simpa [fullChallengeProtocol] using
    (inferInstance :
      ∀ j,
        Fintype
          ((fullChallengeProtocol
              n (𝔽 := 𝔽) (ω := ω) (k := k) (s := s) t l).Challenge j))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
        (Spec.pSpecFold (ω := ω) k s ++ₚ
          Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
            Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Inhabited := by
  infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
        (Spec.pSpecFold (ω := ω) k s ++ₚ
          Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
            Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Fintype := by
  infer_instance

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([]ₒ +
      [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Inhabited where
  inhabited_B := by
    intro q
    cases q with
    | inl q => exact PEmpty.elim q
    | inr q =>
        simpa using
          (inferInstance :
            Inhabited
              (([((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
                  (Spec.pSpecFold (ω := ω) k s ++ₚ
                    Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                      Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Range q))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    ([]ₒ +
      [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
          (Spec.pSpecFold (ω := ω) k s ++ₚ
            Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
              Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Fintype where
  fintype_B := by
    intro q
    cases q with
    | inl q => exact PEmpty.elim q
    | inr q =>
        simpa using
          (inferInstance :
            Fintype
              (([((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
                  (Spec.pSpecFold (ω := ω) k s ++ₚ
                    Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                      Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ).Range q))

noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    HasEvalPMF
      (OracleComp
        ([]ₒ +
          [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
              (Spec.pSpecFold (ω := ω) k s ++ₚ
                Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                  Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ)) := by
  infer_instance
--HasEvalSPMF
--       (OptionT
--         (OracleComp
--           ([]ₒ +
--             [(BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t ++ₚ
--                   (Spec.pSpecFold k s ++ₚ Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
--                     Spec.QueryRound.pSpec l)).Challenge]ₒ)))
--
noncomputable instance {t l : ℕ} {ω : SmoothCosetFftDomain n 𝔽} :
    HasEvalSPMF
      (OptionT
        (OracleComp
          ([]ₒ +
            [((BatchedFri.Spec.BatchingRound.batchSpec 𝔽 t) ++ₚ
                (Spec.pSpecFold (ω := ω) k s ++ₚ
                  Spec.FinalFoldPhase.pSpec 𝔽 ++ₚ
                    Spec.QueryRound.pSpec (ω := ω) l)).Challenge]ₒ))) := by
  infer_instance

open ENNReal in
/-- Corresponds to Claim 8.2 of [BCIKS20] (the query-phase soundness of batched FRI).

  **Statement-bug repair / named residual.** This declaration previously had the *degenerate*
  conclusion `True` (proved by `trivial`), so it did not state Claim 8.2 at all and silently
  discarded its hypotheses `h_agreement` and `m_ge_3`. A `True` conclusion is strictly weaker than
  an honest named residual: it asserts nothing. Following the same treatment already applied to the
  sibling Claim 8.3 (`fri_soundness`, which is a `def … : Prop` named-residual specification rather
  than an unfinished theorem body), this is converted into a `def … : Prop` that records the actual
  mathematical content of Claim 8.2 as a precisely-named residual `Prop`. No degenerate `True`
  conclusion remains.

  **Content.** The batched input functions `f : Fin t.succ → (ω.subdomain 0 → 𝔽)` are assumed to
  have correlated-agreement density at most `α` against the rate-`(2^n)` Reed–Solomon code on the
  evaluation domain `ω.subdomain 0` (hypothesis `h_agreement`: `correlated_agreement_density (Fₛ f)
  (RS code) ≤ α`), and the repetition/soundness parameter satisfies `m ≥ 3` (`m_ge_3`). The query
  phase then enforces *joint agreement* of the batch with the code on a `(1 - α)`-fraction of the
  domain: `Code.jointAgreement` at relative distance `δ = 1 - α`. This is the per-query consistency
  consequence underlying the end-to-end Claim 8.3, phrased over the same `Code.jointAgreement`
  predicate used by `fri_soundness`.

  This is kept as a `Prop` (a named residual) rather than a proved theorem because the full
  probabilistic query-round analysis (the FRI query-round reduction's acceptance bound feeding into
  the proximity-gap / correlated-agreement machinery) is not yet available in-tree; the sibling
  Claim 8.3 residual `fri_soundness` is in the same state. Discharging it requires the query-round
  `OracleReduction.run` acceptance bound, exactly as for `fri_soundness`. -/
def fri_query_soundness
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  : Prop :=
    Code.jointAgreement
      (F := 𝔽)
      (κ := Fin t.succ)
      (ι := ω.subdomain 0)
      (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n)).carrier)
        (δ := 1 - α)
        (W := f)

/-- Split frontier for Claim 8.2.  The existing `fri_query_soundness` residual is the final
`Code.jointAgreement` conclusion, while the proof should be assembled from three independent
ingredients:

* the probabilistic acceptance bound for the query round,
* the batching/oracle-lens reduction connecting batched queries to the underlying FRI query phase,
* the coding-theoretic step from correlated-agreement density to joint agreement.

The fields are deliberately `Prop`s plus an implication into `fri_query_soundness`: downstream work
can discharge or refine each ingredient without replacing the faithful Claim 8.2 statement by a
monolithic assumption. -/
structure FriQuerySoundnessParts
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3) where
  query_round_acceptance_bound : Prop
  batching_oracle_lens_reduction : Prop
  correlated_agreement_to_jointAgreement : Prop
  pieces_imply_claim :
    query_round_acceptance_bound →
    batching_oracle_lens_reduction →
    correlated_agreement_to_jointAgreement →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3)

/-- Reassemble Claim 8.2 from the split frontier.  This theorem is intentionally small: it makes
the residual boundaries usable by callers while the three substantive proof ingredients remain
separate targets. -/
theorem fri_query_soundness_of_parts
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  (parts : FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
    (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
  (h_query : parts.query_round_acceptance_bound)
  (h_lens : parts.batching_oracle_lens_reduction)
  (h_ca : parts.correlated_agreement_to_jointAgreement) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) :=
  parts.pieces_imply_claim h_query h_lens h_ca

/-- Instantiate the Claim 8.2 frontier with the proved query-round acceptance proposition.

This constructor only fills the query-round field with `queryRoundAcceptanceBound G δ queries`.
The batching/oracle-lens reduction and the correlated-agreement bridge remain explicit frontier
fields, and `pieces_imply_claim` records how those pieces would imply the faithful
`fri_query_soundness` residual. -/
def FriQuerySoundnessParts.of_queryRoundAcceptanceBound
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
  (lensReduction agreementBridge : Prop)
  (pieces_imply_claim :
    queryRoundAcceptanceBound G δ queries →
    lensReduction →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := queryRoundAcceptanceBound G δ queries
  batching_oracle_lens_reduction := lensReduction
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the query-round frontier with
`queryRoundAcceptanceBound_holds`.

The remaining hypotheses are exactly the two still-open frontier fields: the batching/oracle-lens
reduction and the correlated-agreement-to-joint-agreement bridge. -/
theorem fri_query_soundness_of_queryRoundAcceptanceBound
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
  {lensReduction agreementBridge : Prop}
  (pieces_imply_claim :
    queryRoundAcceptanceBound G δ queries →
    lensReduction →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
  (h_lens : lensReduction)
  (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundAcceptanceBound
      (n := n) (ω := ω) (f := f) (h_agreement := h_agreement)
      (m_ge_3 := m_ge_3) G δ queries lensReduction agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (queryRoundAcceptanceBound_holds G δ queries) h_lens h_agreementBridge

/-- Instantiate the Claim 8.2 frontier with the normalized-density query-round proposition. -/
def FriQuerySoundnessParts.of_queryRoundDensityBound
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
  (lensReduction agreementBridge : Prop)
  (pieces_imply_claim :
    queryRoundDensityBound G δ queries →
    lensReduction →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3)) :
    FriQuerySoundnessParts (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) where
  query_round_acceptance_bound := queryRoundDensityBound G δ queries
  batching_oracle_lens_reduction := lensReduction
  correlated_agreement_to_jointAgreement := agreementBridge
  pieces_imply_claim := pieces_imply_claim

/-- Reassemble Claim 8.2 after discharging the query-round frontier with the normalized-density
form of the proved query-round bound. -/
theorem fri_query_soundness_of_queryRoundDensityBound
    {t : ℕ}
  {α : ℝ≥0}
  (f : Fin t.succ → (ω.subdomain 0 → 𝔽))
  (h_agreement :
    correlated_agreement_density
      (Fₛ f)
      (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω.subdomain 0 ↪ 𝔽) (2 ^ n))
    ≤ α)
  {m : ℕ}
  (m_ge_3 : m ≥ 3)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  (G : Finset ι) (δ : ℝ≥0) (queries : ℕ)
  {lensReduction agreementBridge : Prop}
  (pieces_imply_claim :
    queryRoundDensityBound G δ queries →
    lensReduction →
    agreementBridge →
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3))
  (h_lens : lensReduction)
  (h_agreementBridge : agreementBridge) :
    fri_query_soundness (n := n) (ω := ω) (f := f)
      (h_agreement := h_agreement) (m_ge_3 := m_ge_3) := by
  let parts :=
    FriQuerySoundnessParts.of_queryRoundDensityBound
      (n := n) (ω := ω) (f := f) (h_agreement := h_agreement)
      (m_ge_3 := m_ge_3) G δ queries lensReduction agreementBridge pieces_imply_claim
  exact fri_query_soundness_of_parts (n := n) (ω := ω) f h_agreement m_ge_3 parts
    (queryRoundDensityBound_holds G δ queries) h_lens h_agreementBridge

#print axioms Fri.FriQuerySoundnessParts
#print axioms Fri.QueryRound.queryRound_acceptance_le_of_density
#print axioms Fri.queryRoundAcceptanceBound_of_density
#print axioms Fri.queryRoundDensityBound
#print axioms Fri.queryRoundDensityBound_holds
#print axioms Fri.fri_query_soundness_of_parts
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundAcceptanceBound
#print axioms Fri.fri_query_soundness_of_queryRoundAcceptanceBound
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundDensityBound
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBound

/-
The old finite-range instance diagnostic scratch block has been removed.  The remaining
Claim 8.2 work is the query-round acceptance analysis described in the docstring above
and in `docs/kb/audits/issue-14-batched-fri-query-soundness-2026-06-06.md`.
-/

open ENNReal in
/-- Corresponds to Claim 8.3 of [BCIKS20] -/
def fri_soundness
    {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3)
  : Prop :=
    let ρ_sqrt :=
      ReedSolomon.sqrtRate
        (2 ^ n)
        (⟨fun x => x, by simp⟩ : ω ↪ 𝔽)
    let α : ℝ≥0 := (ρ_sqrt * (1 + 1 / (2 * (m : ℝ≥0))))
    (∃ prov : OracleProver (WitOut := Unit) ..,
        Pr[fun _ => True |
            OracleReduction.run () f ()
              ⟨
                prov,
                (BatchedFri.Spec.batchedFRIreduction
                  (ω := ω) (n := n) k s d domain_size_cond l t).verifier
              ⟩
          ] > εC 𝔽 n s m ρ_sqrt + α ^ l) →
      Code.jointAgreement
        (F := 𝔽)
        (κ := Fin t.succ)
        (ι := ω)
        (C := (ReedSolomon.code (⟨fun x => x, by simp⟩ : ω ↪ 𝔽) (2 ^ n)).carrier)
          (δ := 1 - α)
          (W := f)

/-- Split frontier for Claim 8.3.  The `fri_soundness` residual is the end-to-end
verifier-failure statement for batched FRI, while the remaining proof should be assembled from
separate ingredients:

* lifting the query-soundness Claim 8.2 output to the full-domain statement used here,
* the sequential-composition soundness theorem for the composed batched FRI reduction,
* the accounting step showing `εC 𝔽 n s m ρ_sqrt + α ^ l` bounds the verifier failure event.

As with `FriQuerySoundnessParts`, these fields are intentionally named `Prop`s plus a reassembly
map.  This keeps Claim 8.3 faithful without hiding the missing probabilistic proof behind a
monolithic assumption. -/
structure FriSoundnessParts
    {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3) where
  query_soundness_lift : Prop
  sequential_composition_soundness : Prop
  total_error_accounting : Prop
  pieces_imply_claim :
    query_soundness_lift →
    sequential_composition_soundness →
    total_error_accounting →
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3

/-- Reassemble Claim 8.3 from its split frontier.  The hard probabilistic and
sequential-composition ingredients remain separate named targets. -/
theorem fri_soundness_of_parts
    {t l m : ℕ}
  (f : Fin t.succ → (ω → 𝔽))
  (m_ge_3 : m ≥ 3)
  (parts : FriSoundnessParts (n := n) (s := s) (d := d) (ω := ω) (l := l)
    (domain_size_cond := domain_size_cond) f m_ge_3)
  (h_query : parts.query_soundness_lift)
  (h_seq : parts.sequential_composition_soundness)
  (h_total : parts.total_error_accounting) :
    fri_soundness (n := n) (s := s) (d := d) (ω := ω) (l := l)
      (domain_size_cond := domain_size_cond) f m_ge_3 :=
  parts.pieces_imply_claim h_query h_seq h_total

#print axioms Fri.FriSoundnessParts
#print axioms Fri.fri_soundness_of_parts

end Soundness

end Fri
end Fri

/-! ### Axiom audit (issues #14/#24 FRI soundness frontier) -/

#print axioms Fri.fri_query_soundness
#print axioms Fri.FriQuerySoundnessParts
#print axioms Fri.fri_query_soundness_of_parts
#print axioms Fri.QueryRound.queryRound_acceptance_le_of_density
#print axioms Fri.queryRoundAcceptanceBound_of_density
#print axioms Fri.queryRoundDensityBound
#print axioms Fri.queryRoundDensityBound_holds
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundAcceptanceBound
#print axioms Fri.fri_query_soundness_of_queryRoundAcceptanceBound
#print axioms Fri.FriQuerySoundnessParts.of_queryRoundDensityBound
#print axioms Fri.fri_query_soundness_of_queryRoundDensityBound
#print axioms Fri.fri_soundness
#print axioms Fri.FriSoundnessParts
#print axioms Fri.fri_soundness_of_parts
