import ArkLib.Data.CodingTheory.ProximityGap.MCAGS
import ArkLib.Data.CodingTheory.ProximityGap.MCAGSBounds

/-! # Core of the #141 refutation: `epsMCAgs = 1` for an adversarial (non-faithful) list family.

NOVEL FINDING: `uniformEpsMCAgsPrizeBoundConjecture` / `epsMCAgs_prizeBound_conjecture` are stated
with `∀ L` over ALL list families. That is too strong: a non-faithful `L` that holds the line
witness but *omits* the row witness makes the GS-row bad event fire for EVERY `γ`.

Witness: stack `u = (w₀, 0)` (row 0 = a nonzero codeword `w₀`, row 1 = `0`) with `L u = {w₀}`.
For every `γ`: the line is `w₀ + γ•0 = w₀`, so `w₀ ∈ C ∩ L` matches it on `S = univ`; and the only
candidate row-codeword in `L` is `w₀`, which does NOT equal row 1 = `0` (since `w₀ ≠ 0`). So the
event holds for all `γ`, `Pr_γ = 1`, hence `epsMCAgs C δ (fun _ => {w₀}) = 1`.

The genuine prize needs `L` FAITHFUL (containing the actual close codewords, in particular the row
witnesses) — exactly the clause this counterexample violates.

Verified kernel-clean: `#print axioms not_uniformEpsMCAgsPrizeBoundConjecture` reports
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`) on `v4.30.0-rc2`. -/

noncomputable section
open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAGS Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The adversarial stack: row 0 = `w₀`, row 1 = `0`. -/
def badStack (w₀ : ι → F) : WordStack F (Fin 2) ι := ![w₀, 0]

@[simp] theorem badStack_zero (w₀ : ι → F) : (badStack w₀) 0 = w₀ := rfl
@[simp] theorem badStack_one (w₀ : ι → F) : (badStack w₀) 1 = (0 : ι → F) := rfl

/-- **Key lemma.** For any nonzero codeword `w₀ ∈ C` and any `δ ≤ 1`, the GS-row bad event fires
at the bad stack for EVERY challenge `γ`. -/
theorem mcaEventGSrow_badStack
    (C : Set (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1)
    (w₀ : ι → F) (hw₀C : w₀ ∈ C) (hw₀ne : w₀ ≠ 0) (γ : F) :
    mcaEventGSrow ({w₀} : Finset (ι → F)) C δ ((badStack w₀) 0) ((badStack w₀) 1) γ := by
  classical
  refine ⟨Finset.univ, ?_, ⟨w₀, hw₀C, Finset.mem_singleton_self _, ?_⟩, ?_⟩
  · -- |univ| = card ι ≥ (1 - δ) * card ι  since (1 - δ) ≤ 1
    rw [Finset.card_univ]
    calc (1 - δ) * (Fintype.card ι : ℝ≥0)
        ≤ 1 * (Fintype.card ι : ℝ≥0) := by
          gcongr; exact tsub_le_self
      _ = (Fintype.card ι : ℝ≥0) := one_mul _
  · -- w₀ matches the line `w₀ + γ•0 = w₀` on univ
    intro i _
    simp [badStack]
  · -- no codeword in {w₀} equals row 1 = 0 on univ, since w₀ ≠ 0
    rintro ⟨c, _hcC, hcL, hc0⟩
    rw [Finset.mem_singleton] at hcL
    subst hcL
    apply hw₀ne
    funext i
    have := hc0 i (Finset.mem_univ i)
    simpa [badStack] using this

open ProbabilityTheory

/-- **The bad event has probability 1.** Since `mcaEventGSrow_badStack` holds for every `γ`, the
event is almost-surely true, so its probability under uniform `γ` is `1`. -/
theorem Pr_badStack_eq_one
    (C : Set (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1)
    (w₀ : ι → F) (hw₀C : w₀ ∈ C) (hw₀ne : w₀ ≠ 0) :
    Pr_{let γ ← $ᵖ F}[mcaEventGSrow ({w₀} : Finset (ι → F)) C δ
        ((badStack w₀) 0) ((badStack w₀) 1) γ] = 1 := by
  classical
  rw [ProbabilityTheory.Pr_eq_tsum_indicator]
  have hfun : (fun γ : F => ($ᵖ F) γ *
      (if mcaEventGSrow ({w₀} : Finset (ι → F)) C δ ((badStack w₀) 0) ((badStack w₀) 1) γ
        then (1 : ENNReal) else 0))
      = fun γ : F => ($ᵖ F) γ := by
    funext γ
    rw [if_pos (mcaEventGSrow_badStack C δ hδ w₀ hw₀C hw₀ne γ), mul_one]
  rw [hfun, PMF.tsum_coe]

/-- **`epsMCAgs = 1` for the adversarial list family.** This is the refutation kernel: a
non-faithful `L = fun _ => {w₀}` drives the GS-exposed MCA error to its ceiling, independent of the
field size — so no `poly/q` bound can hold for all `L`. -/
theorem epsMCAgs_badList_eq_one
    (C : Set (ι → F)) (δ : ℝ≥0) (hδ : δ ≤ 1)
    (w₀ : ι → F) (hw₀C : w₀ ∈ C) (hw₀ne : w₀ ≠ 0) :
    epsMCAgs (F := F) C δ (fun _ => ({w₀} : Finset (ι → F))) = 1 := by
  classical
  refine le_antisymm (epsMCAgs_le_one C δ _) ?_
  rw [← Pr_badStack_eq_one C δ hδ w₀ hw₀C hw₀ne]
  exact le_iSup (fun u => Pr_{let γ ← $ᵖ F}[mcaEventGSrow ((fun _ => ({w₀} : Finset (ι → F))) u)
      C δ (u 0) (u 1) γ]) (badStack w₀)

open scoped NNReal
open Polynomial

/-- **MAIN THEOREM (#141): the formalized uniform prize conjecture is FALSE.**

`uniformEpsMCAgsPrizeBoundConjecture` quantifies over ALL list families `L`. We refute it: choose a
prime field `ZMod p` with `p > 2^{c₂+c₃}`, the rate `ρ = prizeRates 0 = 1/2` over `ι = Fin 2` (RS
dimension `⌊1/2·2⌋ = 1`), the nonzero codeword `w₀ = const 1`, and the adversarial family
`L = fun _ => {w₀}`. Then `epsMCAgs = 1` (the GS-row event fires for every `γ`), while the prize
RHS `= 2^{c₂+c₃}/p < 1` — contradiction. The genuine prize requires `L` FAITHFUL. -/
theorem not_uniformEpsMCAgsPrizeBoundConjecture :
    ¬ uniformEpsMCAgsPrizeBoundConjecture := by
  classical
  rintro ⟨c₁, c₂, c₃, h⟩
  -- A prime `p` with `(p : ℝ) > 2^(c₂+c₃)` and `p ≥ 3`.
  obtain ⟨p, hp_ge, hp_prime⟩ :=
    Nat.exists_infinite_primes (max (⌈(2 : ℝ) ^ (c₂ + c₃)⌉₊ + 1) 3)
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp3 : 3 ≤ p := le_trans (le_max_right _ _) hp_ge
  -- `2^(c₂+c₃) < (p : ℝ)`.
  have hpow_lt : (2 : ℝ) ^ (c₂ + c₃) < (p : ℝ) := by
    have h1 : (2 : ℝ) ^ (c₂ + c₃) ≤ (⌈(2 : ℝ) ^ (c₂ + c₃)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(2 : ℝ) ^ (c₂ + c₃)⌉₊ : ℝ) < (⌈(2 : ℝ) ^ (c₂ + c₃)⌉₊ + 1 : ℝ) := by linarith
    have h3 : ((⌈(2 : ℝ) ^ (c₂ + c₃)⌉₊ + 1 : ℕ) : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast le_trans (le_max_left _ _) hp_ge
    push_cast at h3
    linarith
  -- Data: `ι = Fin 2`, `F = ZMod p`, domain `![0,1]`, codeword `w₀ = const 1`.
  have h01 : (0 : ZMod p) ≠ (1 : ZMod p) := zero_ne_one
  let domain : Fin 2 ↪ ZMod p :=
    ⟨![0, 1], by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all⟩
  set w₀ : Fin 2 → ZMod p := fun _ => (1 : ZMod p) with hw₀def
  have hcard : Fintype.card (Fin 2) = 2 := by simp
  -- `⌊prizeRates 0 · card⌋ = 1`.
  have hdeg1 : ⌊(prizeRates 0 : ℝ≥0) * (Fintype.card (Fin 2) : ℝ≥0)⌋₊ = 1 := by
    rw [hcard]
    have : (prizeRates 0 : ℝ≥0) = 1 / 2 := by simp [prizeRates]
    rw [this]; norm_num
  -- `w₀ = const 1` is a nonzero codeword of `code domain 1`.
  have hw₀mem : w₀ ∈ (ReedSolomon.code (domain := domain)
      ⌊(prizeRates 0 : ℝ≥0) * (Fintype.card (Fin 2) : ℝ≥0)⌋₊ : Set (Fin 2 → ZMod p)) := by
    rw [hdeg1]
    refine ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval (Polynomial.C 1) ?_ ?_
    · simp
    · intro i; simp [hw₀def]
  have hw₀ne : w₀ ≠ 0 := by
    intro hcon
    have : (1 : ZMod p) = 0 := by have := congrFun hcon 0; simpa [hw₀def] using this
    exact h01 this.symm
  -- Apply the conjecture at `j = 0, m = 0, η = 1/2, δ = 0, L = fun _ => {w₀}`.
  have hη : (0 : ℝ≥0) < 1 / 2 := by norm_num
  have hδ : ((0 : ℝ≥0) : ℝ) ≤ 1 - (ProximityGap.prizeRates 0 : ℝ) - ((1 / 2 : ℝ≥0) : ℝ) := by
    have : (ProximityGap.prizeRates 0 : ℝ) = 1 / 2 := by
      have : (prizeRates 0 : ℝ≥0) = 1 / 2 := by simp [prizeRates]
      rw [this]; norm_num
    rw [this]; norm_num
  have key := h (ι := Fin 2) (F := ZMod p) domain 0 0 (1 / 2) 0 hη
    (fun _ => ({w₀} : Finset (Fin 2 → ZMod p))) hδ
  -- LHS = 1.
  rw [epsMCAgs_badList_eq_one _ 0 (by norm_num) w₀ hw₀mem hw₀ne] at key
  -- RHS in closed form `2^(c₂+c₃)/p`, hence `0 ≤ RHS < 1`.
  have hp_pos : (0 : ℝ) < p := by positivity
  have hcardF : Fintype.card (ZMod p) = p := ZMod.card p
  have hρ : ((ProximityGap.prizeRates 0 : ℝ≥0) : ℝ) = 1 / 2 := by
    have : (prizeRates 0 : ℝ≥0) = 1 / 2 := by simp [prizeRates]
    rw [this]; norm_num
  have hηcast : ((1 / 2 : ℝ≥0) : ℝ) = 1 / 2 := by norm_num
  have hpow_pos : (0 : ℝ) < (2 : ℝ) ^ (c₂ + c₃) := Real.rpow_pos_of_pos (by norm_num) _
  have hRHSeq : epsMCAgsPrizeBound (Fintype.card (ZMod p)) 0 (ProximityGap.prizeRates 0)
      (1 / 2) c₁ c₂ c₃ = (2 : ℝ) ^ (c₂ + c₃) / (p : ℝ) := by
    unfold epsMCAgsPrizeBound
    rw [hcardF, hρ, hηcast]
    have e1 : ((2 : ℝ) ^ (0 : ℕ)) ^ c₁ = 1 := by norm_num [Real.one_rpow]
    have e2 : (1 / 2 : ℝ) ^ c₂ * (1 / 2 : ℝ) ^ c₃ = (1 / 2 : ℝ) ^ (c₂ + c₃) :=
      (Real.rpow_add (by norm_num) c₂ c₃).symm
    have e3 : (1 / 2 : ℝ) ^ (c₂ + c₃) = ((2 : ℝ) ^ (c₂ + c₃))⁻¹ := by
      rw [one_div, Real.inv_rpow (by norm_num)]
    rw [e1, e2, e3, mul_one, div_eq_mul_inv, inv_inv, one_div_mul_eq_div]
  have hRHS_lt : epsMCAgsPrizeBound (Fintype.card (ZMod p)) 0 (ProximityGap.prizeRates 0)
      (1 / 2) c₁ c₂ c₃ < 1 := by
    rw [hRHSeq, div_lt_one hp_pos]; exact hpow_lt
  have hRHS_nonneg : (0 : ℝ) ≤ epsMCAgsPrizeBound (Fintype.card (ZMod p)) 0
      (ProximityGap.prizeRates 0) (1 / 2) c₁ c₂ c₃ := by
    rw [hRHSeq]; exact div_nonneg (le_of_lt hpow_pos) (le_of_lt hp_pos)
  -- `1 ≤ ofReal RHS` together with `0 ≤ RHS < 1` is a contradiction.
  rw [← ENNReal.ofReal_one] at key
  have hle := (ENNReal.ofReal_le_ofReal_iff hRHS_nonneg).mp key
  linarith [hRHS_lt]

#print axioms not_uniformEpsMCAgsPrizeBoundConjecture
