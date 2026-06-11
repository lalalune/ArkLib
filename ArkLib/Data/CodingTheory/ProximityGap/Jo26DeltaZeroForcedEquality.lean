/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Jo26GeneratorMCA

/-!
# δ = 0 forces interleaving exactness for EVERY coefficient generator (issue #334, A1)

[Jo26] (ePrint 2026/891) Theorem 4.4 proves the interleaving exactness
`ε_G(C^{≡s}, δ) = ε_G(C, δ)` only for generators with seed sets of size `|Ω| ≤ q`
(the covering lemma escapes at most `q` proper subspaces of `F^s`), and Theorem 4.2 pays
the factor `1 + 1/q + ⋯ + 1/q^{s−1}` for arbitrary `Ω`.  The issue #334 probe
`probe_jo26_adversarial_generator.py` (65k+ exhaustive generators at `|Ω| > q`) found
**equality everywhere** — and discovered the structural reason at radius zero: at `δ = 0`
the witness set is forced to be the whole domain, where the no-joint-tuple clause depends
on the *stack alone*, not the seed.  A single column projection then dominates the
interleaved bad-seed set — no covering lemma, no seed-set bound, no factor.

This file proves that discovery (the first hypothesis-A1 brick):

* `genMCAEvent_zero_S_univ` — at `δ = 0` every event witness is `Finset.univ`;
* `pairJointAgreesOnP_univ_iff` — on the full domain, joint tuple agreement is exactly
  row-wise code membership;
* `epsMCAGen_interleaved_le_deltaZero` — the hard direction: one column projection
  dominates, for ARBITRARY finite seed sets `Ω` and arbitrary generators;
* **`epsMCAGen_interleaved_eq_deltaZero`** — the headline: for every coefficient
  generator `G : Ω → Fin ℓ → F` (no `|Ω| ≤ q` hypothesis), every `F`-linear `C`, every
  interleaving width `s`,

    `ε_G(C^{≡s}, 0) = ε_G(C, 0)`.

Scope honesty: this closes A1 **at the radius-zero slice only**.  Whether the [Jo26]
`|Ω| ≤ q` dichotomy is hollow at positive radii remains open (the probe found no violation
at toy scale; the candidate sharp instances need `> q` *distinct* joint-agreement
subspaces realized by one stack, which `tupleJointSubmodule`'s witness-set indexing
bounds — a finer question left to the next rung).

## References

* [Jo26] S. Jo, *Interleaving Stability for Mutual Correlated Agreement and Curve
  Decodability*, ePrint 2026/891 (Theorems 4.2/4.4).  Issue #334, hypothesis A1.
-/

namespace ProximityGap.Jo26Gen

open Finset NNReal Code
open scoped ProbabilityTheory BigOperators ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
variable {Ω : Type} [Fintype Ω] [Nonempty Ω]
variable {ℓ : ℕ}

/-- At radius `δ = 0`, the size clause of `genMCAEvent` forces the witness set to be the
whole domain. -/
lemma genMCAEvent_zero_S_univ {S : Finset ι}
    (hcard : (S.card : ℝ≥0) ≥ (1 - (0 : ℝ≥0)) * Fintype.card ι) : S = Finset.univ := by
  have hge : (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) := by simpa using hcard
  exact Finset.eq_univ_of_card S
    (le_antisymm (Finset.card_le_univ S) (by exact_mod_cast hge))

/-- On the full domain, joint tuple agreement is exactly row-wise membership: the only
candidate witness tuple is the stack itself. -/
lemma pairJointAgreesOnP_univ_iff {C : Set (ι → A)} {u : WordStack A (Fin ℓ) ι} :
    ProximityGapP.pairJointAgreesOnP C Finset.univ u ↔ ∀ j, u j ∈ C := by
  constructor
  · rintro ⟨v, hv, hag⟩ j
    have hvj : v j = u j := funext fun i => hag i (Finset.mem_univ i) j
    exact hvj ▸ hv j
  · intro h
    exact ⟨u, h, fun i _ j => rfl⟩

/-- Projecting the generator combination of an interleaved stack to column `k` gives the
generator combination of the column stack. -/
lemma genComb_column {s : ℕ} (G : Ω → Fin ℓ → F)
    (U : WordStack (Fin s → A) (Fin ℓ) ι) (ω : Ω) (i : ι) (k : Fin s) :
    genComb G U ω i k = genComb G (fun j i => U j i k) ω i := by
  simp only [genComb, Finset.sum_apply, Pi.smul_apply]

/-- **The hard direction at radius zero, for arbitrary generators.**  Every bad seed of an
interleaved stack is a bad seed of one fixed column stack: at `δ = 0` the witness is the
full domain, where the no-joint clause is seed-independent and pins a bad column
`(j₀, k₀)` once and for all; the column-`k₀` projection preserves closeness (codeword
columns are codewords) and inherits the refusal (its row `j₀` is not in `C`). -/
theorem epsMCAGen_interleaved_le_deltaZero (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (G : Ω → Fin ℓ → F) :
    epsMCAGen G ((C : Set (ι → A))^⋈ (Fin s)) 0
      ≤ epsMCAGen G (C : Set (ι → A)) 0 := by
  classical
  unfold epsMCAGen
  refine iSup_le fun U => ?_
  by_cases hP : ProximityGapP.pairJointAgreesOnP
      ((C : Set (ι → A))^⋈ (Fin s)) Finset.univ U
  · -- a joint tuple exists on the full domain: no seed can be bad
    have h_imp : ∀ ω : Ω, genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) 0 U ω →
        genMCAEvent G (C : Set (ι → A)) 0 (fun j i => U j i 0) ω := by
      rintro ω ⟨S, hcard, -, hnojoint⟩
      exact absurd (genMCAEvent_zero_S_univ hcard ▸ hP) hnojoint
    refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
    exact le_iSup (fun v : WordStack A (Fin ℓ) ι =>
      Pr_{let ω ← $ᵖ Ω}[genMCAEvent G (C : Set (ι → A)) 0 v ω]) _
  · -- the seed-independent refusal pins a bad column (j₀, k₀)
    have hex : ∃ j₀ : Fin ℓ, U j₀ ∉ ((C : Set (ι → A))^⋈ (Fin s)) := by
      by_contra h
      push_neg at h
      exact hP (pairJointAgreesOnP_univ_iff.mpr h)
    obtain ⟨j₀, hj₀⟩ := hex
    have hex2 : ∃ k₀ : Fin s, (fun i => U j₀ i k₀) ∉ (C : Set (ι → A)) := by
      by_contra h
      push_neg at h
      exact hj₀ h
    obtain ⟨k₀, hk₀⟩ := hex2
    set v : WordStack A (Fin ℓ) ι := fun j i => U j i k₀ with hv
    have h_imp : ∀ ω : Ω, genMCAEvent G ((C : Set (ι → A))^⋈ (Fin s)) 0 U ω →
        genMCAEvent G (C : Set (ι → A)) 0 v ω := by
      rintro ω ⟨S, hcard, ⟨w, hwmem, hwagree⟩, -⟩
      have hSuniv : S = Finset.univ := genMCAEvent_zero_S_univ hcard
      subst hSuniv
      refine ⟨Finset.univ, ?_, ?_, ?_⟩
      · simpa using hcard
      · -- closeness: column k₀ of the interleaved codeword
        have hwcol : (fun i => w i k₀) ∈ (C : Set (ι → A)) := hwmem k₀
        refine ⟨fun i => w i k₀, hwcol, fun i hi => ?_⟩
        have h := congrArg (fun f : Fin s → A => f k₀) (hwagree i hi)
        simpa [hv, genComb_column] using h
      · -- refusal: row j₀ of the column stack is not in C
        rw [pairJointAgreesOnP_univ_iff]
        intro h
        exact hk₀ (h j₀)
    refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
    exact le_iSup (fun v : WordStack A (Fin ℓ) ι =>
      Pr_{let ω ← $ᵖ Ω}[genMCAEvent G (C : Set (ι → A)) 0 v ω]) v

/-- **δ = 0 forces interleaving exactness for every coefficient generator** (issue #334,
hypothesis A1, radius-zero slice).  No seed-set bound: the [Jo26] Theorem 4.4 hypothesis
`|Ω| ≤ q` is unnecessary at radius zero, and the Theorem 4.2 factor is slack there. -/
theorem epsMCAGen_interleaved_eq_deltaZero (C : Submodule F (ι → A)) (s : ℕ) [NeZero s]
    (G : Ω → Fin ℓ → F) :
    epsMCAGen G ((C : Set (ι → A))^⋈ (Fin s)) 0 = epsMCAGen G (C : Set (ι → A)) 0 :=
  le_antisymm (epsMCAGen_interleaved_le_deltaZero C s G)
    (epsMCAGen_le_epsMCAGen_interleaved C s G 0)

end ProximityGap.Jo26Gen

/-! ## Axiom audit -/
#print axioms ProximityGap.Jo26Gen.genMCAEvent_zero_S_univ
#print axioms ProximityGap.Jo26Gen.pairJointAgreesOnP_univ_iff
#print axioms ProximityGap.Jo26Gen.epsMCAGen_interleaved_le_deltaZero
#print axioms ProximityGap.Jo26Gen.epsMCAGen_interleaved_eq_deltaZero
