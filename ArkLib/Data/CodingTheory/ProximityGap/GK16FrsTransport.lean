/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.Data.CodingTheory.ProximityGap.GK16Claim16Transport
import ArkLib.ToMathlib.GK16Claim16Witness
import ArkLib.Data.CodingTheory.ProximityGap.GK16Lemma12

/-!
# Encoder-isomorphism transport for the FRS subspace-design budget (GK16 §4)

This file discharges the **encoder-isomorphism transport** half of GK16 Claim 16 / Theorem
2.18: it carries the abstract adapted-recombination engine
(`ArkLib.FRS.GK16.exists_adapted_recombination`) across the FRS encoder
`E := frsEvalOnPoints domain s ω` to produce, for any subspace `A ≤ frsCode` with
`finrank A ≤ s` and an **injective** encoder, the per-coordinate multiplicity lower bound

  `dim (A ⊓ ker(eval_i)) ≤ rootMultiplicity (domain i) (foldedWronskian P ω)`

for a realizing polynomial family `P` of degrees `< k`.  Summed and chained with the
verified degree-budget spine, this yields the GK16 §4 budget
`∑_i dim A_i ≤ (dim A)·(k-1)` on the `finrank A ≤ s` range — exactly the range used in the
`r ∈ [s]` branch of the subspace-design profile.

## Key construction

For `A ≤ frsCode = (degreeLT F k).map E`, with `E` injective, the **pullback**
`U := A.comap E ⊓ degreeLT F k` is a polynomial subspace with `U.map E = A` and (via the
injective-image equiv) `finrank U = finrank A`.  A basis `bU` of `U` gives the realizing
family `P j := (bU j : F[X])` (independent, degrees `< k`).  Per coordinate `i`, the
orbit-vanishing subspace `W_i ≤ U` (polynomials killed by `proj i ∘ E`) has
`finrank W_i = finrank (A ⊓ ker (proj i))` (the iso restricts), and the adapted
recombination of `bU` to `W_i` feeds the proven Claim-16 engine.

The side condition `finrank A ≤ s` is genuine: the Claim-16 engine's orbit-vanishing
hypothesis ranges over the `finrank A` dilation rows `ω^b`, which must be among the `s`
folds (`b < finrank A ≤ s`).

Everything here is `sorry`/axiom-clean.
-/

open Polynomial Module

namespace ReedSolomon.Folded

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

/-- The FRS evaluation map composed with the `i`-th coordinate projection, as a single
`F`-linear map `F[X] →ₗ[F] (Fin s → F)`. A polynomial lies in its kernel iff it vanishes
on the whole `s`-fold orbit `{domain i · ω^j : j < s}`. -/
noncomputable def evalAtCoord (domain : ι ↪ F) (s : ℕ) (ω : F) (i : ι) :
    Polynomial F →ₗ[F] (Fin s → F) :=
  (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i).comp
    (frsEvalOnPoints domain s ω)

@[simp] lemma evalAtCoord_apply (domain : ι ↪ F) (s : ℕ) (ω : F) (i : ι)
    (p : Polynomial F) (j : Fin s) :
    evalAtCoord domain s ω i p j = p.eval (domain i * ω ^ (j : ℕ)) := rfl

end ReedSolomon.Folded
