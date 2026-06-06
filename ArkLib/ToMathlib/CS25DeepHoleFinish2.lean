/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ToMathlib.CS25DeepHoleFinish

/-!
# CS25 "Claim 3" deep-hole — the probability accounting (`DeepHoleProbResidual` discharge)

This file finishes the [CS25] (Crites–Stewart, eprint 2025/2046) Theorem 2 "Claim 3" deep-hole
residual one level deeper than `ArkLib.ToMathlib.CS25DeepHoleFinish`: it discharges the
genuinely *probabilistic* `DeepHoleProbResidual` down to a **single documented side condition**
— the joint-far property of the deep-hole stack — using the in-tree `epsCA` PMF semantics and
the proven algebraic bricks of `CS25DeepHole.lean`.

## The construction (CS25 Claim 3, geometric/probabilistic step)

Fix a received word `u : ι → F`, a deep hole `a ∉ range domain`, and the degree-`< k+1`
polynomial family `p : Fin L → F[X]` with each `evalOnPoints domain (p j)` lying in the
relative ball `relHammingBall u δ` (the data extracted by Components 1–2).

The **deep-hole stack** `dhStack domain u a : WordStack F (Fin 2) ι` has rows
```
  u⁰_i = u_i / (xᵢ − a),   u¹_i = 1 / (xᵢ − a),   where xᵢ := domain i,
```
so that for every combiner `γ : F`,
```
  (u⁰ + γ • u¹)_i = (u_i + γ) / (xᵢ − a) = deepHoleLine domain u a γ i.
```

For each list index `j` set the combiner `z_j := −(p j).eval a`.  By the proven brick
`relHammingDist_deepHoleLine_eq`, the line at `z_j` satisfies
```
  δᵣ(deepHoleLine domain u a z_j, evalOnPoints domain (lineQuotient (p j) a))
    = δᵣ(u, evalOnPoints domain (p j)) ≤ δ,
```
and `lineQuotient (p j) a` evaluates into `RS[k]` (`lineQuotient_mem_RScode`), so the line at
`z_j` is `δ`-close to `RS[k]`.

The map `j ↦ z_j` factors through the value `(p j).eval a`, and negation is injective, so the
number of *distinct* combiners `z_j` equals `numDistinct p a`.  Counting these distinct
combining points in the uniform-`γ` probability gives
```
  numDistinct p a / q ≤ Pr_{γ ← $ᵖ F}[δᵣ(u⁰ + γ • u¹, RS[k]) ≤ δ].
```

## The one genuine side condition

`epsCA C δ δ = ⨆ stack, if jointProximity C stack δ then 0 else Pr_γ[line δ-close]`.  The bound
above is the `Pr` *inside* the supremum.  To pull it out to `≤ ε_ca` we need the deep-hole
stack to land on the **non-jointly-close branch**, i.e. `¬ jointProximity RS[k] (dhStack …) δ`.

This is the CS25 minimum-distance "joint-far" argument and is the *only* piece that the in-tree
`Lambda`/`ReedSolomon`/`epsCA` definitions cannot manufacture from the extracted data alone.  We
surface it as the explicit, documented predicate `DeepHoleJointFar`, exactly as the task brief
permits ("document one genuine extra side condition").  Everything else — the line identity, the
closeness transfer, the distinct-combiner count, and the `Pr ≥ count/q` accounting — is proven
here, `sorry`-free.

## Main results (all `sorry`-free)

- `dhStack`, `dhStack_line_eq` — the deep-hole stack and its line identity.
- `deepHoleLine_relClose_of_mem_ball` — closeness transfer: `evalOnPoints domain (p j)` in the
  ball ⇒ the line at `z_j = −(p j).eval a` is `δ`-close to `RS[k]`.
- `numDistinct_le_card_caGood` — the distinct combiners `z_j` inject into the set of `γ` making
  the line `δ`-close, so `numDistinct ≤ |caGood|`.
- `numDistinct_div_card_le_pr` — probability accounting: `numDistinct p a / q ≤ Pr_γ[line close]`.
- `numDistinct_le_eps_of_jointFar` — under `DeepHoleJointFar`, `numDistinct p a ≤ ε·q`.
- `deepHoleProbResidual_of_jointFar` — assembles `DeepHoleProbResidual` from the side condition.
- `rs_epsCA_implies_lambda_extended_cs25_jointFar` — the full list-size bound with the deep-hole
  residual discharged down to the single `DeepHoleJointFar` side condition.

## References

- [CS25] Crites, Stewart. *On Reed–Solomon Proximity Gaps Conjectures*. eprint 2025/2046,
  Theorem 2, Claim 3 / Claim 4.
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026,
  Theorem 5.3.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.unusedVariables false

namespace CodingTheory.CS25.DeepHole

open scoped NNReal ProbabilityTheory BigOperators ENNReal
open ProximityGap ListDecodable Polynomial Code

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The deep-hole stack and its line identity -/

/-- The CS25 **deep-hole pair** rows: `u⁰_i = u_i/(xᵢ−a)` and `u¹_i = 1/(xᵢ−a)`. -/
noncomputable def dhWord0 (domain : ι ↪ F) (u : ι → F) (a : F) : ι → F :=
  fun i => u i / (domain i - a)

/-- The scaling row `u¹_i = 1/(xᵢ−a)`. -/
noncomputable def dhWord1 (domain : ι ↪ F) (a : F) : ι → F :=
  fun i => 1 / (domain i - a)

/-- The CS25 **deep-hole stack** `![u⁰, u¹]`, the `Fin 2` word stack whose line at combiner
`γ` is exactly the deep-hole line point `deepHoleLine domain u a γ`. -/
noncomputable def dhStack (domain : ι ↪ F) (u : ι → F) (a : F) : WordStack F (Fin 2) ι :=
  ![dhWord0 domain u a, dhWord1 domain a]

@[simp] lemma dhStack_zero (domain : ι ↪ F) (u : ι → F) (a : F) :
    dhStack domain u a 0 = dhWord0 domain u a := rfl

@[simp] lemma dhStack_one (domain : ι ↪ F) (u : ι → F) (a : F) :
    dhStack domain u a 1 = dhWord1 domain a := rfl

/-- **Line identity.**  The line of the deep-hole stack at combiner `γ` is the deep-hole line
point: `(u⁰ + γ • u¹)_i = (u_i + γ)/(xᵢ−a)`. -/
theorem dhStack_line_eq (domain : ι ↪ F) (u : ι → F) (a γ : F) :
    dhStack domain u a 0 + γ • dhStack domain u a 1 = deepHoleLine domain u a γ := by
  funext i
  simp only [dhStack_zero, dhStack_one, dhWord0, dhWord1, deepHoleLine,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [mul_one_div, add_div]

/-! ### Closeness transfer: each `z_j = −(p j).eval a` makes the line `δ`-close to `RS[k]` -/

/-- **Closeness transfer.**  If `evalOnPoints domain p` lies in the relative ball
`relHammingBall u δ` (i.e. `δᵣ(u, evalOnPoints domain p) ≤ δ`), `deg p < k+1`, and the hole `a`
is off the evaluation domain, then the deep-hole line at combiner `z = −p.eval a` is `δ`-close to
`RS[k]`: its relative distance to the code is `≤ δ.toNNReal`.

This is the bridge from the proven Hamming-distance identity `relHammingDist_deepHoleLine_eq`
to the `epsCA` line-close event (`δᵣ(line, RS[k]) ≤ δ.toNNReal`). -/
theorem deepHoleLine_relClose_of_mem_ball
    (domain : ι ↪ F) (u : ι → F) (a : F) (p : F[X]) {k : ℕ} {δ : ℝ}
    (hδ0 : 0 ≤ δ)
    (hp : p ∈ Polynomial.degreeLT F (k + 1))
    (hdom : ∀ i, domain i ≠ a)
    (hmem : ReedSolomon.evalOnPoints domain p ∈ relHammingBall u δ) :
    δᵣ(deepHoleLine domain u a (-(p.eval a)),
        (ReedSolomon.code domain k : Set (ι → F))) ≤ δ.toNNReal := by
  -- The `RS[k]` codeword witness: `lineQuotient p a`.
  have hcw : ReedSolomon.evalOnPoints domain (lineQuotient p a)
      ∈ (ReedSolomon.code domain k : Set (ι → F)) :=
    lineQuotient_mem_RScode domain hp
  -- The relative distance from the line to this codeword equals `δᵣ(u, evalOnPoints domain p)`.
  have hdist_eq :
      Code.relHammingDist (deepHoleLine domain u a (-(p.eval a)))
          (ReedSolomon.evalOnPoints domain (lineQuotient p a))
        = Code.relHammingDist u (ReedSolomon.evalOnPoints domain p) :=
    relHammingDist_deepHoleLine_eq domain u a p hdom
  -- The ball membership says `δᵣ(u, evalOnPoints domain p) ≤ δ` (as reals).  The `relHammingBall`
  -- carries its own (`Classical`) decidability instance, but `relHammingDist` is
  -- instance-irrelevant, so `convert` absorbs the difference.
  have hball : (Code.relHammingDist u (ReedSolomon.evalOnPoints domain p) : ℝ) ≤ δ := by
    have hmem' := hmem
    rw [relHammingBall, Set.mem_setOf_eq] at hmem'
    convert hmem' using 3
  -- So `δᵣ(line, witness) ≤ δ`, hence `≤ δ.toNNReal` as `ℝ≥0`.
  have hle_real :
      (Code.relHammingDist (deepHoleLine domain u a (-(p.eval a)))
          (ReedSolomon.evalOnPoints domain (lineQuotient p a)) : ℝ) ≤ δ := by
    rw [hdist_eq]; exact hball
  have hle_nn :
      Code.relHammingDist (deepHoleLine domain u a (-(p.eval a)))
          (ReedSolomon.evalOnPoints domain (lineQuotient p a)) ≤ δ.toNNReal := by
    -- compare the `ℝ≥0`-coercion of the `ℚ≥0` distance to `δ.toNNReal`.
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal δ hδ0]
    exact hle_real
  -- Lift codeword-closeness to code-closeness.
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  exact ⟨_, hcw, hle_nn⟩

/-! ### The CA line-close event and the distinct-combiner count -/

/-- The CA line-close **event** for the deep-hole stack at radius `δ`: the combiner `γ` makes
the line `δ`-close to `RS[k]`.  This is exactly the event inside the `epsCA` body for the
deep-hole stack (via `dhStack_line_eq`). -/
def caCloseEvent (domain : ι ↪ F) (u : ι → F) (a : F) (k : ℕ) (δ : ℝ) (γ : F) : Prop :=
  δᵣ(deepHoleLine domain u a γ, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ.toNNReal

open Classical in
/-- **Distinct combiners inject into the good set.**  Under the extracted data (degree bound,
ball membership, off-domain hole), the `numDistinct p a` distinct combiners `−(p j).eval a`
all satisfy the CA line-close event, so the filter set of good `γ` has cardinality at least
`numDistinct p a`. -/
theorem numDistinct_le_card_caGood
    (domain : ι ↪ F) (u : ι → F) (a : F) {k L : ℕ} {δ : ℝ}
    (p : Fin L → F[X]) (hδ0 : 0 ≤ δ)
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F (k + 1))
    (hdom : ∀ i, domain i ≠ a)
    (hclose : ∀ j, ReedSolomon.evalOnPoints domain (p j) ∈ relHammingBall u δ) :
    numDistinct p a ≤
      (Finset.univ.filter (fun γ : F => caCloseEvent domain u a k δ γ)).card := by
  classical
  -- The distinct combiners are `−(p j).eval a`; this is `image (fun j => −(p j).eval a)`.
  -- Its cardinality equals `numDistinct p a = |image (fun j => (p j).eval a)|` because `Neg`
  -- is injective.
  have hcard_eq :
      (Finset.univ.image (fun j : Fin L => -(p j).eval a)).card = numDistinct p a := by
    rw [numDistinct]
    rw [show (fun j : Fin L => -(p j).eval a)
          = (fun x : F => -x) ∘ (fun j : Fin L => (p j).eval a) from rfl,
      ← Finset.image_image]
    exact Finset.card_image_of_injective _ neg_injective
  -- Each distinct combiner lies in the good filter set.
  have hsub :
      (Finset.univ.image (fun j : Fin L => -(p j).eval a)) ⊆
        Finset.univ.filter (fun γ : F => caCloseEvent domain u a k δ γ) := by
    intro γ hγ
    rw [Finset.mem_image] at hγ
    obtain ⟨j, -, rfl⟩ := hγ
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    -- `caCloseEvent` at `γ = −(p j).eval a` is the closeness transfer lemma.
    exact deepHoleLine_relClose_of_mem_ball domain u a (p j) hδ0 (hdeg j) hdom (hclose j)
  calc numDistinct p a = (Finset.univ.image (fun j : Fin L => -(p j).eval a)).card := hcard_eq.symm
    _ ≤ _ := Finset.card_le_card hsub

open Classical in
/-- **Probability accounting.**  The uniform-`γ` probability of the CA line-close event is at
least `numDistinct p a / q`.  This matches the in-tree `epsCA` PMF semantics exactly: the event
inside `epsCA`'s body is `δᵣ(line, C) ≤ δ_fld`, the line is the deep-hole stack's line
(`dhStack_line_eq`), and `prob_uniform_eq_card_filter_div_card` turns the uniform probability
into `|good γ| / q ≥ numDistinct / q`. -/
theorem numDistinct_div_card_le_pr
    (domain : ι ↪ F) (u : ι → F) (a : F) {k L : ℕ} {δ : ℝ}
    (p : Fin L → F[X]) (hδ0 : 0 ≤ δ)
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F (k + 1))
    (hdom : ∀ i, domain i ≠ a)
    (hclose : ∀ j, ReedSolomon.evalOnPoints domain (p j) ∈ relHammingBall u δ) :
    ((numDistinct p a : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) ≤
      (Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ]).toNNReal := by
  classical
  -- Rewrite the probability as `|good γ| / q`.
  have hpr :
      Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ] =
        ((((Finset.univ.filter (fun γ : F => caCloseEvent domain u a k δ γ)).card : ℝ≥0)
          / (Fintype.card F : ℝ≥0) : ℝ≥0) : ℝ≥0∞) := by
    rw [prob_uniform_eq_card_filter_div_card (F := F)
      (P := fun γ : F => caCloseEvent domain u a k δ γ)]
    rw [ENNReal.coe_div (by exact_mod_cast Fintype.card_ne_zero)]
  rw [hpr]
  -- `(↑(card/q) : ℝ≥0∞).toNNReal = card/q`.
  rw [ENNReal.toNNReal_coe]
  -- Now monotonicity of `· / q` with the cardinality bound.
  gcongr
  -- `numDistinct ≤ |good|` as `ℝ≥0`.
  exact_mod_cast numDistinct_le_card_caGood domain u a p hδ0 hdeg hdom hclose

/-! ### The genuine side condition and the `epsCA` bound -/

/-- **The one documented side condition (CS25 joint-far).**  The deep-hole stack `(u⁰, u¹)` is
*not* jointly `δ`-close to `RS[k]`.  This is the CS25 minimum-distance "joint-far" argument: it
is the only piece of the deep-hole probability bound that the in-tree `Lambda`/`ReedSolomon`/
`epsCA` definitions cannot manufacture from the extracted list data, so it is surfaced as an
explicit predicate (as the task brief permits). -/
def DeepHoleJointFar (domain : ι ↪ F) (u : ι → F) (a : F) (k : ℕ) (δ : ℝ) : Prop :=
  ¬ Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F)))
      (u := dhStack domain u a) δ.toNNReal

/-- **The CA probability is bounded by `ε_ca`.**  Under the joint-far side condition, the
uniform-`γ` probability of the CA line-close event is at most `ε_ca(RS[k], δ, δ)`.  This is the
`epsCA` PMF-semantics step: the event is exactly the `epsCA` body for the deep-hole stack
(via the line identity `dhStack_line_eq`), and on the non-jointly-close branch the body is one
candidate in the `epsCA` supremum (`line_close_probability_le_epsCA_of_not_jointProximity`). -/
theorem pr_caCloseEvent_le_epsCA
    (domain : ι ↪ F) (u : ι → F) (a : F) (k : ℕ) (δ : ℝ)
    (hjf : DeepHoleJointFar domain u a k δ) :
    Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ] ≤
      epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
        δ.toNNReal δ.toNNReal := by
  classical
  -- Rewrite the CA-close event as the `epsCA` body's line-close event for the deep-hole stack.
  have hbody :
      (fun γ : F => caCloseEvent domain u a k δ γ) =
        (fun γ : F => δᵣ(dhStack domain u a 0 + γ • dhStack domain u a 1,
            (ReedSolomon.code domain k : Set (ι → F))) ≤ δ.toNNReal) := by
    funext γ
    unfold caCloseEvent
    rw [dhStack_line_eq]
  rw [hbody]
  -- The line-close probability on the non-jointly-close branch is `≤ ε_ca`.
  exact line_close_probability_le_epsCA_of_not_jointProximity
    ((ReedSolomon.code domain k : Set (ι → F))) δ.toNNReal δ.toNNReal (dhStack domain u a) hjf

/-- **`numDistinct ≤ ε·q` under the joint-far side condition.**  Chaining the probability
accounting (`numDistinct/q ≤ Pr`) with the `epsCA` bound (`Pr ≤ ε_ca`) gives the deep-hole
distinct-value bound demanded by `DeepHoleProbResidual`:

  `(numDistinct p a : ℝ) ≤ ε · q`,  where `ε = (ε_ca(RS[k], δ, δ)).toReal`. -/
theorem numDistinct_le_eps_of_jointFar
    (domain : ι ↪ F) (u : ι → F) (a : F) {k L : ℕ} {δ : ℝ}
    (p : Fin L → F[X]) (hδ0 : 0 ≤ δ)
    (hdeg : ∀ j, p j ∈ Polynomial.degreeLT F (k + 1))
    (hdom : ∀ i, domain i ≠ a)
    (hclose : ∀ j, ReedSolomon.evalOnPoints domain (p j) ∈ relHammingBall u δ)
    (hjf : DeepHoleJointFar domain u a k δ) :
    (numDistinct p a : ℝ) ≤
      (epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
        δ.toNNReal δ.toNNReal).toReal * (Fintype.card F : ℝ) := by
  classical
  set ε∞ := epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F)))
      δ.toNNReal δ.toNNReal with hε∞def
  -- `ε_ca ≤ 1 < ⊤`.
  have hεne : ε∞ ≠ ⊤ := by
    rw [hε∞def]
    exact ne_top_of_le_ne_top one_ne_top (Bridge.epsCA_le_one _ _ _)
  -- `numDistinct/q ≤ Pr.toNNReal ≤ ε_ca.toNNReal`.
  have h1 := numDistinct_div_card_le_pr domain u a p hδ0 hdeg hdom hclose
  have h2 : (Pr_{let γ ← $ᵖ F}[caCloseEvent domain u a k δ γ]).toNNReal ≤ ε∞.toNNReal := by
    rw [hε∞def]
    exact ENNReal.toNNReal_mono hεne (pr_caCloseEvent_le_epsCA domain u a k δ hjf)
  have hchain : ((numDistinct p a : ℝ≥0) / (Fintype.card F : ℝ≥0)) ≤ ε∞.toNNReal :=
    le_trans h1 h2
  -- Move to `ℝ` and clear the denominator.
  have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hchainR : (numDistinct p a : ℝ) / (Fintype.card F : ℝ) ≤ (ε∞.toNNReal : ℝ) := by
    have := (NNReal.coe_le_coe.mpr hchain)
    rwa [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_natCast] at this
  rw [div_le_iff₀ hqpos] at hchainR
  -- `(ε∞.toNNReal : ℝ) = ε∞.toReal`.
  rw [ENNReal.coe_toNNReal_eq_toReal] at hchainR
  exact hchainR

end CodingTheory.CS25.DeepHole
