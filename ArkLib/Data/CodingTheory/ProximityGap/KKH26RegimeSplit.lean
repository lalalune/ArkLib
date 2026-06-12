/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DeltaStarReduction
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonDischarge

/-!
# The regime-split weld: `JohnsonDischargeStatement ⊕ RegimeIIIGoodness ⟹ the exact δ* pin` (#357)

The deployed-prize obligation `InteriorCeiling` ("`ε_mca ≤ ε*` for every radius below the KKH26
jump `1 − r/2^μ`") does **not** follow from the Johnson lane alone: `JohnsonDischargeStatement`
(`Hab25JohnsonDischarge`) quantifies only over radii `δ < gs_johnson k n m₀` — strictly below the
Johnson radius — while the jump sits strictly **above** Johnson at every parameter point where the
pin's `ε*` band is nonempty (the jump exceeds Johnson iff `r²m < 2^μ((r−2)m+1)`; for `r ≥ 4` this
always holds, and the only `r = 3` failure corner `μ = 3, m ≥ 8` has KKH26 count `32`, far below
the Hab25 numeric budget — no admissible `ε*` exists there).

This file makes that frontier **machine-checked** rather than comment-thread discipline:

* `powDomain` / `evalCode_eq_reedSolomon` — the first in-tree bridge identifying the KKH26
  ceiling family `evalCode g n d` with `ReedSolomon.code` on the `i ↦ gⁱ` domain (`k = d+1`),
  connecting the ceiling code to the entire Hab25/BCIKS20 Johnson cone;
* `RegimeIIIGoodness` — **the named open core**: `ε_mca ≤ ε*` on `[δJ, 1 − r/2^μ)`, the
  beyond-Johnson band (the 25-year explicit-RS wall);
* `interiorCeiling_of_below_and_regimeIII` — the case-split decomposition of the obligation;
* `epsMCA_evalCode_le_of_johnsonDischarge` — `JohnsonDischargeStatement` + the cryptographic
  budget arithmetic ⟹ goodness below `gs_johnson`, transported to the KKH26 code;
* `kkh26_deltaStar_pin_of_johnsonDischarge_and_regimeIII` — **the weld**: the Johnson lane's
  endpoint ⊕ `RegimeIIIGoodness` ⊕ explicit arithmetic ⟹ `mcaDeltaStar = 1 − r/2^μ` exactly;
* `gs_johnson_lt_jump` — the formal guard: under the integer inequality `r²·m < 2^μ·k`,
  regime III is **nonempty**, so the Johnson lane cannot be the whole pin.

After this file, the prize chain reads: `CellPackageSupply → JohnsonDischargeStatement`
(the active swarm lane) **⊕** `RegimeIIIGoodness` (the honest open core) `→` exact pin — with
the split enforced by types.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open scoped NNReal ENNReal
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25Johnson
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open Polynomial

namespace ProximityGap.KKH26RegimeSplit

/-! ## The domain bridge: `evalCode` is a Reed–Solomon code -/

/-- A nonzero-order element of a field is nonzero (the orderOf-zero degenerate case is
excluded by `NeZero n`). -/
theorem ne_zero_of_orderOf_eq {p : ℕ} [Fact p.Prime] {g : ZMod p} {n : ℕ} [NeZero n]
    (hg : orderOf g = n) : g ≠ 0 := by
  intro h0
  subst h0
  have h1 : ¬ IsOfFinOrder (0 : ZMod p) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    rintro ⟨t, ht, hpow⟩
    rw [zero_pow ht.ne'] at hpow
    exact zero_ne_one hpow
  exact NeZero.ne n (hg.symm.trans (orderOf_eq_zero h1))

/-- **The smooth-domain embedding** `i ↦ gⁱ : Fin n ↪ ZMod p` for `g` of multiplicative
order `n`.  Injectivity below the order is the standard cancellation argument. -/
def powDomain {p : ℕ} [Fact p.Prime] (g : ZMod p) {n : ℕ} (hg : orderOf g = n)
    (hg0 : g ≠ 0) : Fin n ↪ ZMod p where
  toFun i := g ^ (i : ℕ)
  inj' := by
    intro i j hij
    wlog hle : (i : ℕ) ≤ (j : ℕ) generalizing i j
    · exact (this j i hij.symm (le_of_not_le hle)).symm
    have hcancel : g ^ ((j : ℕ) - (i : ℕ)) = 1 := by
      have h1 : g ^ (i : ℕ) * g ^ ((j : ℕ) - (i : ℕ)) = g ^ (i : ℕ) * 1 := by
        rw [mul_one, ← pow_add, Nat.add_sub_cancel' hle]
        exact hij.symm
      exact mul_left_cancel₀ (pow_ne_zero _ hg0) h1
    have hdvd : n ∣ (j : ℕ) - (i : ℕ) := hg ▸ orderOf_dvd_of_pow_eq_one hcancel
    have hlt : (j : ℕ) - (i : ℕ) < n := lt_of_le_of_lt (Nat.sub_le _ _) j.isLt
    have hz : (j : ℕ) - (i : ℕ) = 0 := Nat.eq_zero_of_dvd_of_lt hdvd hlt
    exact Fin.ext (by omega)

/-- **The bridge:** the KKH26 ceiling family `evalCode g n d` (degree-`≤ d` evaluations on the
power domain) **is** the Reed–Solomon code `ReedSolomon.code (powDomain g) (d+1)`.  This is the
first in-tree identification connecting the ceiling construction to the Hab25/BCIKS20 cone. -/
theorem evalCode_eq_reedSolomon {p : ℕ} [Fact p.Prime] {n : ℕ} [NeZero n] (g : ZMod p)
    (hg : orderOf g = n) (hg0 : g ≠ 0) (d : ℕ) :
    evalCode g n d
      = (ReedSolomon.code (powDomain g hg hg0) (d + 1) : Set (Fin n → ZMod p)) := by
  ext w
  constructor
  · rintro ⟨q, hdeg, heval⟩
    show w ∈ (Polynomial.degreeLT (ZMod p) (d + 1)).map
      (ReedSolomon.evalOnPoints (powDomain g hg hg0))
    rw [Submodule.mem_map]
    refine ⟨q, ?_, ?_⟩
    · rw [Polynomial.mem_degreeLT]
      calc q.degree ≤ (q.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
        _ < ((d + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_of_le hdeg
    · funext i
      exact (heval i).symm
  · intro hw
    obtain ⟨q, hq, heval⟩ := Submodule.mem_map.mp hw
    rw [Polynomial.mem_degreeLT] at hq
    refine ⟨q, ?_, ?_⟩
    · by_cases h0 : q = 0
      · simp [h0]
      · have hlt : q.natDegree < d + 1 := (Polynomial.natDegree_lt_iff_degree_lt h0).mpr (by
          exact_mod_cast hq)
        omega
    · intro i
      rw [← heval]
      rfl

/-! ## The regime split -/

/-- **The named open core: regime III goodness.**  The MCA error of the KKH26 ceiling code
stays below `ε*` on the beyond-`δJ` band `[δJ, 1 − r/2^μ)`.  With `δJ = gs_johnson k n m₀`
this is exactly the strictly-above-Johnson band — the 25-year explicit-RS wall.  Every
in-tree route to the exact pin must pass through this Prop (or `InteriorCeiling` whole). -/
def RegimeIIIGoodness (p n : ℕ) [Fact p.Prime] [NeZero n] (g : ZMod p) (μ m r : ℕ)
    (εstar : ℝ≥0∞) (δJ : ℝ) : Prop :=
  ∀ δ : ℝ≥0, δJ ≤ (δ : ℝ) → δ < 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) →
    epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) δ ≤ εstar

/-- **The case-split decomposition:** goodness strictly below `δJ` plus regime III goodness
at and above `δJ` assemble into the full `InteriorCeiling` obligation. -/
theorem interiorCeiling_of_below_and_regimeIII
    {p n : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p} {μ m r : ℕ} {εstar : ℝ≥0∞} {δJ : ℝ}
    (hbelow : ∀ δ : ℝ≥0, (δ : ℝ) < δJ →
      epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n ((r - 2) * m)) δ ≤ εstar)
    (hIII : RegimeIIIGoodness p n g μ m r εstar δJ) :
    InteriorCeiling p n g μ m r εstar := by
  intro δ hδ
  rcases lt_or_le ((δ : ℝ)) δJ with h | h
  · exact hbelow δ h
  · exact hIII δ h hδ

/-! ## The below-Johnson leg from the swarm's lane -/

/-- The GS Johnson radius is at most `1`. -/
theorem gs_johnson_le_one (k n m : ℕ) : gs_johnson k n m ≤ 1 := by
  show (1 : ℝ) - Real.sqrt (((k : ℚ) / n : ℚ) : ℝ)
      - Real.sqrt (((k : ℚ) / n : ℚ) : ℝ) / (2 * m) ≤ 1
  have h1 : (0 : ℝ) ≤ Real.sqrt (((k : ℚ) / n : ℚ) : ℝ) := Real.sqrt_nonneg _
  have h2 : (0 : ℝ) ≤ Real.sqrt (((k : ℚ) / n : ℚ) : ℝ) / (2 * m) :=
    div_nonneg h1 (by positivity)
  linarith

/-- **The below-`gs_johnson` leg, transported to the KKH26 code.**  Granting the Johnson
lane's endpoint `JohnsonDischargeStatement` and the cryptographic budget inequality, the MCA
error of `evalCode g n d` is `≤ ε*` at every radius strictly below `gs_johnson (d+1) n m₀`.
This is regimes I–II of `InteriorCeiling`; it cannot reach further (the discharge statement
quantifies only below the Johnson radius). -/
theorem epsMCA_evalCode_le_of_johnsonDischarge
    (hJDS : JohnsonDischargeStatement)
    {p n : ℕ} [Fact p.Prime] [NeZero n] {g : ZMod p}
    (hg : orderOf g = n) (hg0 : g ≠ 0)
    {d : ℕ} (hd1 : 1 ≤ d) (hdn : d + 2 ≤ n)
    {m₀ : ℕ} (hm12 : 12 ≤ m₀) {η : ℝ≥0}
    (hmη : (m₀ : ℝ) ≤ max
      (⌈((((d + 1 : ℕ) : ℝ) / n + 1 / n)) ^ ((1 : ℝ) / 2) / (2 * (η : ℝ))⌉ : ℝ) 3)
    {εstar : ℝ≥0∞}
    (hbudget : ∀ (dom : Fin n ↪ ZMod p) (δ : ℝ≥0), (δ : ℝ) < gs_johnson (d + 1) n m₀ →
      ENNReal.ofReal (johnsonBoundReal dom (d + 1) η δ) ≤ εstar) :
    ∀ δ : ℝ≥0, (δ : ℝ) < gs_johnson (d + 1) n m₀ →
      epsMCA (F := ZMod p) (A := ZMod p) (evalCode g n d) δ ≤ εstar := by
  intro δ hδJ
  have hδ1R : (δ : ℝ) ≤ 1 := le_of_lt (lt_of_lt_of_le hδJ (gs_johnson_le_one _ _ _))
  have hδ1 : δ ≤ 1 := by exact_mod_cast hδ1R
  have hnum : epsMCA (F := ZMod p) (A := ZMod p)
      ((ReedSolomon.code (powDomain g hg hg0) (d + 1) : Set (Fin n → ZMod p))) δ ≤
      ENNReal.ofReal (johnsonBoundReal (powDomain g hg hg0) (d + 1) η δ) :=
    hJDS n (d + 1) m₀ ‹NeZero n› (ZMod p) inferInstance inferInstance inferInstance
      (powDomain g hg hg0) η δ (by omega) (by omega) hm12 hδ1 hδJ hmη
  rw [evalCode_eq_reedSolomon g hg hg0 d]
  exact le_trans hnum (hbudget _ δ hδJ)

/-! ## The weld -/

/-- **THE WELD: the Johnson lane's endpoint ⊕ regime III ⟹ the exact δ\* pin.**
`JohnsonDischargeStatement` (the swarm's active lane, one residual from closed) supplies
regimes I–II; `RegimeIIIGoodness` is the honest open core (the beyond-Johnson band); the
budget hypothesis is the cryptographic-field arithmetic.  Together they pin

  `mcaDeltaStar (evalCode g n ((r−2)m), ε*) = 1 − r/2^μ`  **exactly**.

No route can skip the `RegimeIIIGoodness` hypothesis: `gs_johnson_lt_jump` shows the band
`[gs_johnson, 1 − r/2^μ)` is nonempty whenever `r²m < 2^μ((r−2)m+1)` — which holds at every
parameter point admitting a nonempty `ε*` band. -/
theorem kkh26_deltaStar_pin_of_johnsonDischarge_and_regimeIII
    (hJDS : JohnsonDischargeStatement)
    {p n : ℕ} [Fact p.Prime] [NeZero n] {μ m r : ℕ}
    (hμ : 1 ≤ μ) {g : ZMod p} (hm : 1 ≤ m) (hn : n = 2 ^ μ * m)
    (hg : orderOf g = 2 ^ μ * m)
    (hp : ((2 : ℕ) ^ μ) ^ 2 ^ (μ - 1) < p)
    (hr2 : 2 ≤ r) (hr : r ≤ 2 ^ (μ - 1)) (εstar : ℝ≥0∞)
    (hεstar : εstar < ((2 ^ r * (2 ^ (μ - 1)).choose r : ℕ) : ℝ≥0∞) / (p : ℝ≥0∞))
    (hd1 : 1 ≤ (r - 2) * m) (hdn : (r - 2) * m + 2 ≤ n)
    {m₀ : ℕ} (hm12 : 12 ≤ m₀) {η : ℝ≥0}
    (hmη : (m₀ : ℝ) ≤ max
      (⌈(((((r - 2) * m + 1 : ℕ) : ℝ) / n + 1 / n)) ^ ((1 : ℝ) / 2) / (2 * (η : ℝ))⌉ : ℝ) 3)
    (hbudget : ∀ (dom : Fin n ↪ ZMod p) (δ : ℝ≥0),
      (δ : ℝ) < gs_johnson ((r - 2) * m + 1) n m₀ →
      ENNReal.ofReal (johnsonBoundReal dom ((r - 2) * m + 1) η δ) ≤ εstar)
    (hIII : RegimeIIIGoodness p n g μ m r εstar (gs_johnson ((r - 2) * m + 1) n m₀)) :
    mcaDeltaStar (F := ZMod p) (A := ZMod p)
        (evalCode g n ((r - 2) * m)) εstar
      = 1 - (r : ℝ≥0) / ((2 : ℝ≥0) ^ μ) := by
  have hg' : orderOf g = n := hg.trans hn.symm
  have hg0 : g ≠ 0 := ne_zero_of_orderOf_eq hg'
  refine kkh26_deltaStar_pin_of_interior_ceiling hμ hm hn hg hp hr2 hr εstar hεstar ?_
  exact interiorCeiling_of_below_and_regimeIII
    (epsMCA_evalCode_le_of_johnsonDischarge hJDS hg' hg0 hd1 hdn hm12 hmη hbudget) hIII

/-! ## The guard: regime III is nonempty -/

/-- **The formal guard: the Johnson lane cannot be the whole pin.**  Under the integer
inequality `r²·m < 2^μ·k` (true for every `r ≥ 4`, and for `r = 3` except the single corner
`μ = 3` — where no admissible `ε*` exists), the `gs_johnson` radius lies *strictly below* the
KKH26 jump: the regime III band is nonempty, so `RegimeIIIGoodness` carries real content in
every weld instance. -/
theorem gs_johnson_lt_jump {μ m r k n : ℕ} (m₀ : ℕ)
    (hn : n = 2 ^ μ * m) (hk : k = (r - 2) * m + 1) (hm : 1 ≤ m)
    (hint : r ^ 2 * m < 2 ^ μ * k) :
    gs_johnson k n m₀ < 1 - (r : ℝ) / 2 ^ μ := by
  have hnpos : 0 < n := by
    rw [hn]
    exact Nat.mul_pos (pow_pos (by norm_num) μ) hm
  have hcast : (((k : ℚ) / n : ℚ) : ℝ) = (k : ℝ) / (n : ℝ) := by push_cast; ring
  -- the squared comparison: (r/2^μ)² < k/n
  have hsq : ((r : ℝ) / 2 ^ μ) ^ 2 < (k : ℝ) / n := by
    rw [div_pow, div_lt_div_iff (by positivity) (by exact_mod_cast hnpos)]
    have h2 : ((2 : ℝ) ^ μ) ^ 2 = (2 : ℝ) ^ μ * 2 ^ μ := by ring
    rw [h2, hn]
    push_cast
    nlinarith [(show (0 : ℝ) < 2 ^ μ by positivity),
      (show ((r : ℝ) ^ 2 * (m : ℝ)) < 2 ^ μ * (k : ℝ) by exact_mod_cast hint)]
  -- hence r/2^μ < √(k/n)
  have hlt : (r : ℝ) / 2 ^ μ < Real.sqrt ((k : ℝ) / n) :=
    (Real.lt_sqrt (by positivity)).mpr hsq
  -- and gs_johnson ≤ 1 − √(k/n) < 1 − r/2^μ
  have hbound : gs_johnson k n m₀ ≤ 1 - Real.sqrt ((k : ℝ) / n) := by
    show (1 : ℝ) - Real.sqrt (((k : ℚ) / n : ℚ) : ℝ)
        - Real.sqrt (((k : ℚ) / n : ℚ) : ℝ) / (2 * m₀) ≤ 1 - Real.sqrt ((k : ℝ) / n)
    rw [hcast]
    have : (0 : ℝ) ≤ Real.sqrt ((k : ℝ) / n) / (2 * m₀) :=
      div_nonneg (Real.sqrt_nonneg _) (by positivity)
    linarith
  linarith

end ProximityGap.KKH26RegimeSplit

/-! ## Axiom audit — kernel-clean. -/
#print axioms ProximityGap.KKH26RegimeSplit.evalCode_eq_reedSolomon
#print axioms ProximityGap.KKH26RegimeSplit.interiorCeiling_of_below_and_regimeIII
#print axioms ProximityGap.KKH26RegimeSplit.epsMCA_evalCode_le_of_johnsonDischarge
#print axioms ProximityGap.KKH26RegimeSplit.kkh26_deltaStar_pin_of_johnsonDischarge_and_regimeIII
#print axioms ProximityGap.KKH26RegimeSplit.gs_johnson_lt_jump
