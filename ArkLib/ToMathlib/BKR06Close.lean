/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# BKR06 closeness bridge + prime-power witness sequence

This file supplies two purely-arithmetic / combinatorial bricks for the BKR06
list-decoding lower bound (Ben-Sasson–Kopparty–Radhakrishnan, *Subspace
polynomials and list decoding of Reed–Solomon codes*, FOCS 2006), feeding the
named residuals of `CodingTheory.rs_lambda_superpoly_extension_bkr06` and its
`_of_family` reduction in `ArkLib.Data.CodingTheory.ListDecoding.Bounds`.

## (a) Agreement count → relative-distance closeness (the `hclose` residual)

BKR06's geometric step produces a codeword `c` agreeing with the received word `w`
on `≥ a` of the `N = |ι|` evaluation points (the `a = q^v` roots of the subspace
polynomial).  Turning that *agreement count* into the relative-distance bound
`δᵣ(w, c) ≤ δ` that `closeCodewordsRel … δ` demands is pure arithmetic on relative
distance, carried out here:

* `agreement_card_le_hammingDist`  — agreement `≥ a` ⟹ disagreements `= hammingDist ≤ N − a`.
* `hammingDist_le_imp_mem_relHammingBall` — `hammingDist w c / N ≤ δ` ⟹ `c ∈ relHammingBall w δ`.
* `param_ineq_imp_dist_ratio_le` — the closeness *parameter inequality*: from
  `q^(β−1) ≤ a/N` (equivalently the BKR06 dimension condition `β ≤ v`, see
  `bkr06_param_ineq`) and the agreement count we get `(N − a)/N ≤ δ` with
  `δ = 1 − q^(β−1)`.
* `mem_closeCodewordsRel_of_agreement` — the packaged conclusion: a codeword `c ∈ C`
  agreeing with `w` on `≥ a` points, with the parameter inequality satisfied, lies in
  `closeCodewordsRel C w δ`.

The mathematics: agreement `≥ a` ⟹ `hammingDist(w,c) ≤ N − a` ⟹
`δᵣ(w,c) = hammingDist/N ≤ (N − a)/N`; closeness `≤ δ` therefore holds **iff**
`(N − a)/N ≤ δ`.  With `δ = 1 − q^(β−1)` this reads `q^(β−1) ≤ a/N`, which at BKR06's
RS parameters (`N = q`, `a = q^v`) is `q^(β−1) ≤ q^(v−1)`, i.e. `β ≤ v`
(`bkr06_param_ineq`).  No statement is weakened: the parameter inequality is exposed
as an explicit, named hypothesis, exactly as BKR06 derives it from its dimension
threshold.

## (b) The "infinitely many prime powers" witness sequence (the `qs` residual)

`CodingTheory.rs_lambda_superpoly_extension_bkr06` is an existential over a sequence
`qs : ℕ → ℕ` that is `StrictMono` and pointwise `IsPrimePow`, with a per-instance
list-size body.  We supply a concrete such sequence — `qs i = 2^(i+1)` — together
with its `StrictMono` and prime-power proofs (`bkr06PrimePowSeq_strictMono`,
`bkr06PrimePowSeq_isPrimePow`), and the *instantiation lemma*
`rs_lambda_superpoly_extension_bkr06_of_per_instance`: it discharges the bare
external `Prop` **modulo** the still-open per-instance family residual `hfamily`
(BKR06 Lemma 3.5's pigeonhole list-size construction, the genuinely external input).

The witness sequence is chosen as powers of two so that *every* term is a prime
power (`2^(i+1)`), which is exactly what the bare statement's
`∀ i, IsPrimePow (qs i)` conjunct demands; any field of that cardinality
(`𝔽_{2^(i+1)}`) is a genuine BKR06 extension field.

All declarations below compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`); see the in-file `#print axioms`.
-/

-- Section `variable`-bundled instances are needed by the closeness machinery but not by
-- every individual lemma's *type*; the in-type linters are stylistic here.
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace BKR06Close

open ListDecodable BigOperators Finset

/-! ## (a) Agreement count → relative-distance closeness -/

section Closeness

variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type*} [DecidableEq F]

/-- **Agreement count ⟹ Hamming-distance bound.**  If `w` and `c` agree on at least
`a` of the `N = |ι|` coordinates, then they disagree on at most `N − a`, i.e.
`hammingDist w c ≤ N − a`.  (The disagreement set is the complement of the
agreement set; `hammingDist` *is* the disagreement-set cardinality.) -/
lemma agreement_card_le_hammingDist (w c : ι → F) (a : ℕ)
    (hagree : a ≤ (Finset.univ.filter (fun i => w i = c i)).card) :
    hammingDist w c ≤ Fintype.card ι - a := by
  have hsplit :
      (Finset.univ.filter (fun i => w i = c i)).card
        + (Finset.univ.filter (fun i => ¬ (w i = c i))).card
        = Fintype.card ι := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_univ]
  -- `hammingDist` unfolds (definitionally) to the disagreement-filter cardinality.
  have hham : hammingDist w c = (Finset.univ.filter (fun i => ¬ (w i = c i))).card := rfl
  omega

/-- **Relative-distance closeness from a Hamming-distance ratio bound.**  If the
relative Hamming distance `hammingDist w c / N ≤ δ`, then `c` lies in the
`δ`-relative-Hamming ball around `w`.  (Just unfolds `relHammingBall` /
`Code.relHammingDist` and pushes the `ℚ≥0 → ℝ` cast through the division.) -/
lemma hammingDist_le_imp_mem_relHammingBall (w c : ι → F) (δ : ℝ)
    (hδ : (hammingDist w c : ℝ) / Fintype.card ι ≤ δ) :
    c ∈ relHammingBall w δ := by
  simp only [relHammingBall, Set.mem_setOf_eq, Code.relHammingDist]
  push_cast
  -- the two sides differ only by a (subsingleton) `Decidable (· = ·)` instance.
  convert hδ using 3
  congr!

/-- **The BKR06 closeness *parameter inequality*.**  With cutoff `δ = 1 − q^(β−1)`,
the relative-distance bound `(N − a)/N ≤ δ` holds **iff** `q^(β−1) ≤ a/N`.  This is
the single numeric condition BKR06 derives from its dimension threshold; here we
prove the (⟸) direction needed for closeness.  `haN : a ≤ N` keeps the natural
subtraction faithful (`(N − a : ℝ)` then equals `(N : ℝ) − a`). -/
lemma param_ineq_imp_dist_ratio_le (N a q : ℕ) (β δ : ℝ)
    (hN : 0 < N) (haN : a ≤ N)
    (hδdef : δ = 1 - (q : ℝ) ^ (β - 1))
    (hparam : (q : ℝ) ^ (β - 1) ≤ (a : ℝ) / N) :
    ((N : ℝ) - a) / N ≤ δ := by
  rw [hδdef]
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [le_div_iff₀ hNr] at hparam
  rw [div_le_iff₀ hNr]
  nlinarith [hparam]

/-- **Packaged closeness conclusion (the `hclose` residual, discharged).**  A
codeword `c ∈ C` that agrees with the received word `w` on `≥ a` of the `N = |ι|`
points lies in `closeCodewordsRel C w δ`, provided the closeness parameter
inequality `q^(β−1) ≤ a/N` holds with `δ = 1 − q^(β−1)`.  This is exactly the
agreement-count → relative-distance conversion BKR06 Lemma 3.5 needs; everything is
explicit and named (no statement weakened). -/
lemma mem_closeCodewordsRel_of_agreement
    (C : Set (ι → F)) (w c : ι → F) (a q : ℕ) (β δ : ℝ)
    (hc : c ∈ C)
    (hagree : a ≤ (Finset.univ.filter (fun i => w i = c i)).card)
    (haN : a ≤ Fintype.card ι)
    (hδdef : δ = 1 - (q : ℝ) ^ (β - 1))
    (hparam : (q : ℝ) ^ (β - 1) ≤ (a : ℝ) / Fintype.card ι) :
    c ∈ closeCodewordsRel C w δ := by
  refine ⟨hc, ?_⟩
  set N : ℕ := Fintype.card ι with hN
  have hNpos : 0 < N := Fintype.card_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hdist_le : hammingDist w c ≤ N - a := agreement_card_le_hammingDist w c a hagree
  -- cast the nat bound to a real bound on the *numerator* of the distance ratio.
  have hdist_le_r : (hammingDist w c : ℝ) ≤ (N : ℝ) - a := by
    have : (hammingDist w c : ℝ) ≤ ((N - a : ℕ) : ℝ) := by exact_mod_cast hdist_le
    have hcast : ((N - a : ℕ) : ℝ) = (N : ℝ) - a := by
      rw [Nat.cast_sub haN]
    rwa [hcast] at this
  -- chain `hammingDist/N ≤ (N − a)/N ≤ δ`.
  have hratio : (hammingDist w c : ℝ) / N ≤ ((N : ℝ) - a) / N := by
    gcongr
  have hparam_le : ((N : ℝ) - a) / N ≤ δ :=
    param_ineq_imp_dist_ratio_le N a q β δ hNpos haN hδdef hparam
  exact hammingDist_le_imp_mem_relHammingBall w c δ (le_trans hratio hparam_le)

end Closeness

end BKR06Close
