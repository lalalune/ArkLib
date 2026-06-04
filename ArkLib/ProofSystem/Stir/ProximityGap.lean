/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound

open NNReal ProbabilityTheory ReedSolomon

namespace STIR

/-!
## References

* [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S., *Proximity Gaps
    for Reed-Solomon Codes*][BCIKS20]
* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

/-- Theorem 4.1[BCIKS20] from [ACFY24stir]
  Let `C = RS[F, ι, degree]` be a ReedSolomon code with rate `degree / |ι|`
  and let Bstar(ρ) = √ρ. For all `δ ∈ (0, 1 - Bstar(ρ))`, `f₁,...,fₘ : ι → F`, if
  `Pr_{r ← F} [ δᵣ(rⱼ * fⱼ, C) ≤ δ] > err'(degree, ρ, δ, m)`
  then ∃ S ⊆ ι, |S| ≥ (1 - δ) * |ι| and
  ∀ i : m, ∃ u : C, u(S) = fᵢ(S)

  STATUS (audit 2026-06-04, branch arklib-sorry-fixes). Open proof. Two independent,
  machine-checked blockers — this is a documented statement-vs-source mismatch, not a closure:

  1. STATEMENT DEFECT (free `GenFun`). As written, `GenFun : F → Fin m → F` is universally
     quantified with no constraint, so the statement is FALSE: instantiate `GenFun r j = 0`,
     then the combination `∑ⱼ GenFun r j * f j x ≡ 0 ∈ C`, so the hypothesis `Pr[… ≤ δ] = 1 >
     err'` holds for every `f`, yet arbitrary `fᵢ` need not agree with any codeword on a large
     set. The intended instance is the monomial / Vandermonde generator `GenFun r j = r^j`
     (cf. `RSGenerator.genRSC`, ProofSystem/Whir/ProximityGen.lean: `Gen = {r ↦ (j ↦ r^(exp j))}`,
     and `Generator.ProximityGenerator.proximity`, which is this exact statement specialised to
     that generator — itself still open). A faithful repair fixes `GenFun r j = r^j` (or adds
     a `ProximityGenerator`-style hypothesis on `GenFun`). This file has no consumers
     (`grep STIR.proximity_gap` ⇒ only its own definition), so the statement is currently inert.

  2. SOURCE open proof (Johnson/√ρ regime). Even the monomial instance reduces to BCIKS20 Thm 1.5,
     `ProximityGap.correlatedAgreement_affine_curves` (Data/.../BCIKS20/Curves.lean), via
     `proximityError F degree ρ δ m = (m-1) * errorBound δ degree domain` and the degree-`(m-1)`
     curve `∑ᵢ rⁱ • fᵢ`. But `correlatedAgreement_affine_curves` is a flat `sorry`, and the whole
     BCIKS20 CA tree (lines → spaces → curves) is proven ONLY in the unique-decoding regime
     `δ ≤ relUDR`: the affine-lines base `RS_correlatedAgreement_affineLines`
     (Data/.../BCIKS20/AffineLines/Main.lean:40) is open in the list-decoding regime
     `relUDR < δ < 1 - √ρ`. `#print axioms` confirms `correlatedAgreement_affine_spaces`,
     `correlatedAgreement_affine_curves`, `proximity_gap_RSCodes` and `Combine.combine_theorem`
     all carry `sorryAx`; only `RS_correlatedAgreement_affineLines_uniqueDecodingRegime` is clean
     (axioms ⊆ {propext, Classical.choice, Quot.sound}). The √ρ-radius hypothesis here
     (`δ < 1 - Bstar ρ`, with `Bstar ρ = √ρ = sqrtRate`) hits exactly the unproven LDR branch.

  Honest residual: close `AffineLines/Main.lean:40` (Thm 5.1, list-decoding regime), which
  lifts `correlatedAgreement_affine_curves`; then `proximity_gap` (monomial form) follows from
  the curves CA. No clean intermediate path exists today. -/
lemma proximity_gap
  {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {ι : Type} [Fintype ι] [Nonempty ι] {φ : ι ↪ F}
  {degree m : ℕ} {δ : ℝ≥0} {f : Fin m → ι → F} {GenFun : F → Fin m → F}
  (hδPos : 0 < δ)
  (hδLt : δ < 1 - Bstar (LinearCode.rate (code φ degree)))
  (hProb :
    Pr_{ let r ← $ᵖ F}[δᵣ((fun x => ∑ j : Fin m, (GenFun r j) * f j x), code φ degree) ≤ δ] >
      ENNReal.ofReal (proximityError F degree (LinearCode.rate (code φ degree)) δ m)) :
  ∃ S : Finset ι,
    S.card ≥ (1 - δ) * (Fintype.card ι) ∧
    ∀ i : Fin m, ∃ u : ι → F, u ∈ (code φ degree) ∧ ∀ x ∈ S, f i x = u x
:= by
  sorry

end STIR
