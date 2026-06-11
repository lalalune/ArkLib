/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger
import ArkLib.Data.CodingTheory.ProximityGap.MCAWitnessSpread
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The first machine-checked exact `δ*` point: `mcaDeltaStar(RS[F₅,(1,2,4,3),2], 2/5) = 1/4`

The Grand MCA Challenge (#357) asks for the exact threshold
`δ*(C, ε*) = sup {δ | ε_mca(C, δ) ≤ ε*}`. The literature only ever *bounds* `ε_mca`; no exact
value of `mcaDeltaStar` has ever been certified for any code, by anyone, in any proof format.
This file produces the first one, at toy scale, for a genuine smooth-domain Reed–Solomon code:

  `mcaDeltaStar (RS[F₅, (1,2,4,3), 2]) (2/5) = 1/4`,

where the domain `(1,2,4,3)` is the multiplicative group `F₅ˣ` (a smooth, 4 = 2²-element
subgroup), `k = 2` (rate `ρ = 1/2`), and the error target is `ε* = 2/5`.

## The two halves

* **Good half (general theorem, no computation).** For *every* linear code `C ⊆ (ι → A)` over
  *every* finite field `F`, and every radius `δ` with `δ·n < 1` (`n = |ι|`): the witness set in
  `mcaEvent` is forced to be all of `ι`, and then two distinct bad scalars are algebraically
  contradictory (`unique_bad_gamma_common_witness`), so

    `ε_mca(C, δ) ≤ 1/|F|`    (`epsMCA_le_inv_card_of_subunit`).

  This generalizes `MCAZeroCode.badScalar_card_le_one_bot` (zero code, `δ = 0`) to all
  submodule codes at all sub-unit-granularity radii, and yields the universal bracket
  `1/n ≤ mcaDeltaStar(C, ε*)` whenever `1/|F| ≤ ε*` (`inv_card_le_mcaDeltaStar`).

* **Bad half (explicit stack).** At `δ = 1/4` the stack `u₀ = (0,0,0,1)`, `u₁ = (0,0,1,1)`
  has **four** of the five scalars bad: `γ ∈ {0, 2, 3, 4}`. The second row `u₁` is at distance
  `2` from the code (no codeword agrees with it on any 3 of the 4 points — `decide`), so the
  `¬ pairJointAgreesOn` clause holds for *every* witness set of size `≥ 3`; explicit
  line-codewords realize the closeness clause for each of the four scalars. Hence
  `ε_mca(C, 1/4) ≥ 4/5 > 2/5` (`epsMCA_RS5_quarter_ge`).

Combining through the bracket engine (`le_mcaDeltaStar_of_good` / `mcaDeltaStar_le_of_bad`):
`δ* = 1/4` exactly. Note `ε_mca` jumps from `≤ 1/5` to `≥ 4/5` *at* `1/4`: the supremum is not
attained, and at this scale with this `ε*`, `δ*` equals the unique-decoding radius
`(1-ρ)/2 = 1/4`.

Ground truth (pre-registered, two-engine validated): the exact probe ladder
(`scripts/probes/probe_exact_epsmca_ladder.py`) computes `ε_mca(δ) = 1/5` on `[0, 1/4)` and
`4/5` on `[1/4, 1]` for this instance.

Everything is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`), no `sorry`, no
`native_decide`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  ePrint 2026/680. Issue #357.
-/

set_option linter.unusedSectionVars false

open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap Code
open ProximityGap.MCAThresholdLedger ProximityGap.MCAWitnessSpread

namespace ProximityGap.MCADeltaStarExactPoint

/-! ## Part 1 — the general sub-unit-radius collapse (no computation, every linear code) -/

section General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- At a sub-unit radius (`δ·n < 1`), the `mcaEvent` witness-set size constraint
`|S| ≥ (1-δ)·n > n-1` forces `S = univ`. -/
theorem witness_eq_univ_of_subunit {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 1) {S : Finset ι}
    (hS : (S.card : ℝ≥0) ≥ (1 - δ) * (Fintype.card ι : ℝ≥0)) :
    S = Finset.univ := by
  apply Finset.eq_univ_of_card
  refine le_antisymm (Finset.card_le_univ S) ?_
  by_contra hlt
  push_neg at hlt
  -- `S.card + 1 ≤ n` in ℕ, hence in ℝ≥0.
  have hcast : (S.card : ℝ≥0) + 1 ≤ (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Nat.succ_le_of_lt hlt
  -- `(1-δ)·n = n - δ·n ≤ S.card` gives `n ≤ S.card + δ·n`.
  have hexp : (Fintype.card ι : ℝ≥0) - δ * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by
    calc (Fintype.card ι : ℝ≥0) - δ * (Fintype.card ι : ℝ≥0)
        = ((1 : ℝ≥0) - δ) * (Fintype.card ι : ℝ≥0) := by rw [tsub_mul, one_mul]
      _ ≤ (S.card : ℝ≥0) := hS
  have hup : (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) + δ * (Fintype.card ι : ℝ≥0) :=
    tsub_le_iff_right.mp hexp
  -- Chain: `n ≤ S.card + δn < S.card + 1 ≤ n`.
  have : (Fintype.card ι : ℝ≥0) < (Fintype.card ι : ℝ≥0) :=
    lt_of_le_of_lt hup (lt_of_lt_of_le (add_lt_add_of_le_of_lt le_rfl hδ) hcast)
  exact lt_irrefl _ this

open Classical in
/-- **At most one bad scalar per stack at sub-unit radius, for every linear code.** The witness
set is forced to `univ` (`witness_eq_univ_of_subunit`); two firing scalars then share the single
witness set, and `unique_bad_gamma_common_witness` pins them equal. Generalizes
`MCAZeroCode.badScalar_card_le_one_bot` from the zero code at `δ = 0` to every submodule code at
every radius below the `1/n` granularity. -/
theorem badScalar_card_le_one_of_subunit (C : Submodule F (ι → A)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 1) (u : WordStack A (Fin 2) ι) :
    (Finset.filter (fun γ : F => mcaEvent (F := F) (C : Set (ι → A)) δ (u 0) (u 1) γ)
      Finset.univ).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro γ hγ γ' hγ'
  rw [Finset.mem_filter] at hγ hγ'
  obtain ⟨S, hS, hline, hno⟩ := hγ.2
  obtain ⟨S', hS', hline', _⟩ := hγ'.2
  have hSu : S = Finset.univ := witness_eq_univ_of_subunit hδ hS
  have hS'u : S' = Finset.univ := witness_eq_univ_of_subunit hδ hS'
  subst hSu
  subst hS'u
  exact unique_bad_gamma_common_witness C Finset.univ (u 0) (u 1) hno hline hline'

open Classical in
/-- **The sub-unit-radius MCA collapse.** For every linear code over every finite field, at
every radius `δ` with `δ·n < 1`:  `ε_mca(C, δ) ≤ 1/|F|`. -/
theorem epsMCA_le_inv_card_of_subunit (C : Submodule F (ι → A)) {δ : ℝ≥0}
    (hδ : δ * (Fintype.card ι : ℝ≥0) < 1) :
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ ≤ 1 / (Fintype.card F : ℝ≥0∞) := by
  unfold epsMCA
  refine iSup_le fun u => ?_
  rw [prob_uniform_eq_card_filter_div_card]
  simp only [ENNReal.coe_natCast]
  gcongr
  exact_mod_cast badScalar_card_le_one_of_subunit C hδ u

/-- **Universal lower bracket: `1/n ≤ δ*` for every linear code,** as soon as the error target
clears the `1/|F|` floor. Every radius strictly below `1/n` is good, so the supremum of good
radii is at least `1/n`. -/
theorem inv_card_le_mcaDeltaStar (C : Submodule F (ι → A)) {εstar : ℝ≥0∞}
    (hε : 1 / (Fintype.card F : ℝ≥0∞) ≤ εstar) :
    ((Fintype.card ι : ℝ≥0))⁻¹ ≤ mcaDeltaStar (F := F) (A := A) (C : Set (ι → A)) εstar := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨δ, hδ1, hδ2⟩ := exists_between hcon
  have hn : (0 : ℝ≥0) < (Fintype.card ι : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hδn : δ * (Fintype.card ι : ℝ≥0) < 1 := by
    have := mul_lt_mul_of_pos_right hδ2 hn
    rwa [inv_mul_cancel₀ (ne_of_gt hn)] at this
  have hδ1' : δ ≤ 1 := by
    have hmul : δ * 1 ≤ δ * (Fintype.card ι : ℝ≥0) := by
      apply mul_le_mul_of_nonneg_left _ (zero_le δ)
      exact_mod_cast Fintype.card_pos
    have hlt1 : δ < 1 :=
      calc δ = δ * 1 := (mul_one δ).symm
        _ ≤ δ * (Fintype.card ι : ℝ≥0) := hmul
        _ < 1 := hδn
    exact hlt1.le
  have hgood := le_mcaDeltaStar_of_good (F := F) (A := A) (C : Set (ι → A)) εstar hδ1'
    (le_trans (epsMCA_le_inv_card_of_subunit C hδn) hε)
  exact absurd (lt_of_le_of_lt hgood hδ1) (lt_irrefl _)

end General

/-! ## Part 2 — the concrete instance `RS[F₅, (1,2,4,3), 2]` -/

section RS5

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The base field `F₅ = ZMod 5`. -/
abbrev F5 : Type := ZMod 5

/-- The smooth evaluation domain: the multiplicative group `F₅ˣ` enumerated as the orbit of the
generator `2`: `(2⁰, 2¹, 2², 2³) = (1, 2, 4, 3)`. A `4 = 2²`-element (smooth) subgroup. -/
def domainVec : Fin 4 → F5 := ![1, 2, 4, 3]

lemma domainVec_injective : Function.Injective domainVec := by decide

/-- The domain as an embedding. -/
def domain5 : Fin 4 ↪ F5 := ⟨domainVec, domainVec_injective⟩

/-- The Reed–Solomon code `RS[F₅, (1,2,4,3), 2]`: evaluations of polynomials of degree `< 2`
(rate `ρ = 1/2`). -/
noncomputable def RS5 : Submodule F5 (Fin 4 → F5) := ReedSolomon.code domain5 2

/-- Membership in `RS5` is evaluation of an affine polynomial: `v ∈ RS5` iff
`v i = a·xᵢ + b` for some slope/intercept `a, b ∈ F₅`. -/
lemma mem_RS5_iff {v : Fin 4 → F5} :
    v ∈ RS5 ↔ ∃ a b : F5, ∀ i, v i = a * domainVec i + b := by
  constructor
  · intro hv
    have hv' : v ∈ ReedSolomon.code domain5 2 := hv
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero] at hv'
    obtain ⟨p, hdeg, rfl⟩ := hv'
    obtain ⟨a, b, rfl⟩ :=
      Polynomial.exists_eq_X_add_C_of_natDegree_le_one (Nat.lt_succ_iff.mp hdeg)
    exact ⟨a, b, fun i => by
      simp [ReedSolomon.evalOnPoints, domain5]⟩
  · rintro ⟨a, b, hv⟩
    show v ∈ ReedSolomon.code domain5 2
    rw [ReedSolomon.mem_code_iff_exists_polynomial_of_ne_zero]
    refine ⟨Polynomial.C a * Polynomial.X + Polynomial.C b, ?_, ?_⟩
    · have h1 : (Polynomial.C a * Polynomial.X).natDegree ≤ 1 :=
        le_trans (Polynomial.natDegree_C_mul_le a Polynomial.X) Polynomial.natDegree_X_le
      have h2 : (Polynomial.C b : Polynomial F5).natDegree = 0 := Polynomial.natDegree_C b
      have h3 := Polynomial.natDegree_add_le (Polynomial.C a * Polynomial.X)
        (Polynomial.C b : Polynomial F5)
      omega
    · funext i
      rw [hv i]
      simp [ReedSolomon.evalOnPoints, domain5]

/-- First row of the extremal stack: `u₀ = (0,0,0,1)`. -/
def u0vec : Fin 4 → F5 := ![0, 0, 0, 1]

/-- Second row of the extremal stack: `u₁ = (0,0,1,1)` — at distance 2 from `RS5`. -/
def u1vec : Fin 4 → F5 := ![0, 0, 1, 1]

/-- The stack `(u₀, u₁)` as a `WordStack`. -/
def ustack : WordStack F5 (Fin 2) (Fin 4) := fun k => if k = 0 then u0vec else u1vec

@[simp] lemma ustack_zero : ustack 0 = u0vec := rfl

@[simp] lemma ustack_one : ustack 1 = u1vec := by
  show (if (1 : Fin 2) = 0 then u0vec else u1vec) = u1vec
  norm_num

/-- **`u₁` is 2-far from the code**: no affine polynomial agrees with `u₁ = (0,0,1,1)` on any
3 of the 4 domain points. Kernel-checked over all `5² · 2⁴` cases. -/
lemma u1_far : ∀ a b : F5, ∀ S : Finset (Fin 4), 3 ≤ S.card →
    ¬ (∀ i ∈ S, a * domainVec i + b = u1vec i) := by decide

/-- The `¬ pairJointAgreesOn` clause holds for **every** witness set of size `≥ 3`: a joint
pair would in particular give a codeword agreeing with `u₁` on `S`, contradicting `u1_far`. -/
lemma not_pairJoint_RS5 (S : Finset (Fin 4)) (hS : 3 ≤ S.card) :
    ¬ pairJointAgreesOn (RS5 : Set (Fin 4 → F5)) S u0vec u1vec := by
  rintro ⟨v₀, _hv₀, v₁, hv₁, hag⟩
  obtain ⟨a, b, hab⟩ := mem_RS5_iff.mp hv₁
  exact u1_far a b S hS (fun i hi => by rw [← hab i]; exact (hag i hi).2)

/-- The witness-size clause at `δ = 1/4`, `n = 4`: a 3-element set qualifies. -/
lemma card_cond {S : Finset (Fin 4)} (hS : S.card = 3) :
    (S.card : ℝ≥0) ≥ ((1 : ℝ≥0) - 1/4) * (Fintype.card (Fin 4) : ℝ≥0) := by
  have hsub : ((1 : ℝ≥0) - 1/4) ≤ 3/4 := tsub_le_iff_right.mpr (by norm_num)
  calc ((1 : ℝ≥0) - 1/4) * (Fintype.card (Fin 4) : ℝ≥0)
      ≤ (3/4) * (Fintype.card (Fin 4) : ℝ≥0) :=
        mul_le_mul_of_nonneg_right hsub (zero_le _)
    _ = 3 := by rw [Fintype.card_fin]; norm_num
    _ ≤ (S.card : ℝ≥0) := by rw [hS]; norm_num

/-- `mcaEvent` fires at `γ = 0`: the zero codeword agrees with the line
`u₀ + 0·u₁ = (0,0,0,1)` on `S = {0,1,2}`. -/
lemma mcaEvent_RS5_g0 :
    mcaEvent (F := F5) (RS5 : Set (Fin 4 → F5)) (1/4) u0vec u1vec (0 : F5) := by
  refine ⟨{0, 1, 2}, card_cond (by decide), ⟨0, RS5.zero_mem, ?_⟩,
    not_pairJoint_RS5 _ (by decide)⟩
  intro i hi
  fin_cases hi <;> decide

/-- `mcaEvent` fires at `γ = 2`: the codeword `x ↦ 4x + 1` agrees with the line
`u₀ + 2·u₁ = (0,0,2,3)` on `S = {0,2,3}`. -/
lemma mcaEvent_RS5_g2 :
    mcaEvent (F := F5) (RS5 : Set (Fin 4 → F5)) (1/4) u0vec u1vec (2 : F5) := by
  refine ⟨{0, 2, 3}, card_cond (by decide),
    ⟨fun i => 4 * domainVec i + 1, mem_RS5_iff.mpr ⟨4, 1, fun _ => rfl⟩, ?_⟩,
    not_pairJoint_RS5 _ (by decide)⟩
  intro i hi
  fin_cases hi <;> decide

/-- `mcaEvent` fires at `γ = 3`: the codeword `x ↦ 4x + 2` agrees with the line
`u₀ + 3·u₁ = (0,0,3,4)` on `S = {1,2,3}`. -/
lemma mcaEvent_RS5_g3 :
    mcaEvent (F := F5) (RS5 : Set (Fin 4 → F5)) (1/4) u0vec u1vec (3 : F5) := by
  refine ⟨{1, 2, 3}, card_cond (by decide),
    ⟨fun i => 4 * domainVec i + 2, mem_RS5_iff.mpr ⟨4, 2, fun _ => rfl⟩, ?_⟩,
    not_pairJoint_RS5 _ (by decide)⟩
  intro i hi
  fin_cases hi <;> decide

/-- `mcaEvent` fires at `γ = 4`: the zero codeword agrees with the line
`u₀ + 4·u₁ = (0,0,4,0)` on `S = {0,1,3}`. -/
lemma mcaEvent_RS5_g4 :
    mcaEvent (F := F5) (RS5 : Set (Fin 4 → F5)) (1/4) u0vec u1vec (4 : F5) := by
  refine ⟨{0, 1, 3}, card_cond (by decide), ⟨0, RS5.zero_mem, ?_⟩,
    not_pairJoint_RS5 _ (by decide)⟩
  intro i hi
  fin_cases hi <;> decide

/-- The bad-scalar set at `δ = 1/4`: four of the five field elements. -/
def badG : Finset F5 := {0, 2, 3, 4}

/-- **The bad half: `ε_mca(RS5, 1/4) ≥ 4/5`.** Four of five scalars fire `mcaEvent` on the
explicit stack `(u₀, u₁) = ((0,0,0,1), (0,0,1,1))`. -/
theorem epsMCA_RS5_quarter_ge :
    (4 : ℝ≥0∞) / 5 ≤ epsMCA (F := F5) (A := F5) (RS5 : Set (Fin 4 → F5)) (1/4) := by
  have h := epsMCA_ge_card_div_of_mcaEvent_set (F := F5) (A := F5)
    (RS5 : Set (Fin 4 → F5)) (1/4) ustack badG (by
      intro γ hγ
      fin_cases hγ
      · exact mcaEvent_RS5_g0
      · exact mcaEvent_RS5_g2
      · exact mcaEvent_RS5_g3
      · exact mcaEvent_RS5_g4)
  have hG4 : badG.card = 4 := by decide
  have hF5 : Fintype.card F5 = 5 := ZMod.card 5
  rw [hG4, hF5] at h
  simpa using h

/-- **The good half: `ε_mca(RS5, δ) ≤ 1/5` for every `δ < 1/4`,** by the general sub-unit
collapse (no computation: `4·δ < 1` forces the witness to `univ`). -/
theorem epsMCA_RS5_le_fifth {δ : ℝ≥0} (hδ : δ < 1/4) :
    epsMCA (F := F5) (A := F5) (RS5 : Set (Fin 4 → F5)) δ ≤ 1/5 := by
  have hδn : δ * (Fintype.card (Fin 4) : ℝ≥0) < 1 := by
    rw [Fintype.card_fin]
    have h4 := mul_lt_mul_of_pos_right hδ (show (0 : ℝ≥0) < 4 by norm_num)
    calc δ * ((4 : ℕ) : ℝ≥0) = δ * 4 := by norm_num
      _ < (1/4) * 4 := h4
      _ = 1 := by norm_num
  have h := epsMCA_le_inv_card_of_subunit (F := F5) (A := F5) RS5 hδn
  have hF5 : Fintype.card F5 = 5 := ZMod.card 5
  rw [hF5] at h
  simpa using h

/-- **THE FIRST MACHINE-CHECKED EXACT `δ*` VALUE FOR ANY CODE.**

For the smooth-domain Reed–Solomon code `RS[F₅, (1,2,4,3), 2]` (rate `1/2`) at error target
`ε* = 2/5`:

  `mcaDeltaStar = 1/4`  **exactly**.

Lower bracket: every `δ < 1/4` is good (`ε_mca ≤ 1/5 ≤ 2/5`, the sub-unit collapse). Upper
bracket: `δ = 1/4` is bad (`ε_mca ≥ 4/5 > 2/5`, the explicit four-scalar stack). The supremum
of good radii is therefore exactly `1/4` — and it is *not attained*: `ε_mca` jumps from `1/5`
to `4/5` at `δ* = 1/4 = (1-ρ)/2`, the unique-decoding radius. -/
theorem mcaDeltaStar_RS5_eq_quarter :
    mcaDeltaStar (F := F5) (A := F5) (RS5 : Set (Fin 4 → F5)) (2/5 : ℝ≥0∞) = 1/4 := by
  refine le_antisymm ?_ ?_
  · -- Upper bracket via the bad point at `δ = 1/4`.
    refine mcaDeltaStar_le_of_bad (F := F5) (A := F5) (RS5 : Set (Fin 4 → F5)) (2/5) ?_
    refine lt_of_lt_of_le ?_ epsMCA_RS5_quarter_ge
    rw [ENNReal.div_lt_iff (by norm_num) (by norm_num),
      ENNReal.div_mul_cancel (by norm_num) (by norm_num)]
    norm_num
  · -- Lower bracket: every `δ < 1/4` is good, so the sup is at least `1/4`.
    by_contra hcon
    push_neg at hcon
    obtain ⟨δ, hδ1, hδ2⟩ := exists_between hcon
    have hgood := le_mcaDeltaStar_of_good (F := F5) (A := F5)
      (RS5 : Set (Fin 4 → F5)) (2/5) (le_trans hδ2.le
        (by rw [div_le_one (by norm_num : (0 : ℝ≥0) < 4)]; norm_num))
      (le_trans (epsMCA_RS5_le_fifth hδ2)
        (ENNReal.div_le_div_right (by norm_num) 5))
    exact absurd (lt_of_le_of_lt hgood hδ1) (lt_irrefl _)

end RS5

/-! ## Source audit -/

#print axioms witness_eq_univ_of_subunit
#print axioms badScalar_card_le_one_of_subunit
#print axioms epsMCA_le_inv_card_of_subunit
#print axioms inv_card_le_mcaDeltaStar
#print axioms epsMCA_RS5_quarter_ge
#print axioms epsMCA_RS5_le_fifth
#print axioms mcaDeltaStar_RS5_eq_quarter

end ProximityGap.MCADeltaStarExactPoint
