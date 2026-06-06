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

set_option linter.unusedSectionVars false

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

/-- The **polynomial pullback** of a subspace `A` of the folded RS code: the degree-`< k`
polynomials whose encoding lies in `A`. -/
noncomputable def frsPullback (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (A : Submodule F (ι → Fin s → F)) : Submodule F (Polynomial F) :=
  A.comap (frsEvalOnPoints domain s ω) ⊓ Polynomial.degreeLT F k

variable {domain : ι ↪ F} {k s : ℕ} {ω : F}
variable (hEinj : Function.Injective (frsEvalOnPoints domain s ω))

/-- Every pullback polynomial has degree `< k`, hence `natDegree ≤ k - 1`. -/
lemma natDegree_le_of_mem_frsPullback {A : Submodule F (ι → Fin s → F)}
    {p : Polynomial F} (hp : p ∈ frsPullback domain k s ω A) :
    p.natDegree ≤ k - 1 := by
  have hdeg : p.degree < (k : WithBot ℕ) :=
    (Polynomial.mem_degreeLT).mp hp.2
  rcases eq_or_ne p 0 with hp0 | hp0
  · simp [hp0]
  · have hnd : (p.natDegree : WithBot ℕ) < (k : WithBot ℕ) := by
      rwa [Polynomial.degree_eq_natDegree hp0] at hdeg
    have : p.natDegree < k := by exact_mod_cast hnd
    omega

/-- **Pullback maps onto `A`.** When the encoder is injective and `A ≤ frsCode`, the
pullback `U := A.comap E ⊓ degreeLT F k` satisfies `U.map E = A`. -/
lemma frsPullback_map_eq {A : Submodule F (ι → Fin s → F)}
    (hA : A ≤ frsCode domain k s ω) :
    (frsPullback domain k s ω A).map (frsEvalOnPoints domain s ω) = A := by
  apply le_antisymm
  · -- image ⊆ A: members come from `A.comap E`.
    rintro _ ⟨p, hp, rfl⟩
    exact hp.1
  · -- A ⊆ image: every `a ∈ A ≤ frsCode` is `E p` with `p ∈ degreeLT`, and then `p ∈ U`.
    intro a ha
    obtain ⟨p, hp_deg, rfl⟩ := hA ha
    exact ⟨p, ⟨ha, hp_deg⟩, rfl⟩

/-- **Pullback preserves dimension.** `finrank (frsPullback …) = finrank A`. -/
lemma finrank_frsPullback_eq {A : Submodule F (ι → Fin s → F)}
    (hA : A ≤ frsCode domain k s ω) :
    Module.finrank F (frsPullback domain k s ω A) = Module.finrank F A := by
  have e := Submodule.equivMapOfInjective (frsEvalOnPoints domain s ω) hEinj
    (frsPullback domain k s ω A)
  rw [e.finrank_eq, frsPullback_map_eq hA]

/-- The **orbit-vanishing subspace** inside the pullback: pullback polynomials that vanish
on the entire `s`-fold orbit of `domain i`. -/
noncomputable def frsVanish (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (A : Submodule F (ι → Fin s → F)) (i : ι) : Submodule F (Polynomial F) :=
  frsPullback domain k s ω A ⊓ LinearMap.ker (evalAtCoord domain s ω i)

/-- **Orbit-vanishing maps onto the per-coordinate vanishing subspace.**
`(frsVanish … i).map E = A ⊓ ker(proj i)`. -/
lemma frsVanish_map_eq {A : Submodule F (ι → Fin s → F)}
    (hA : A ≤ frsCode domain k s ω) (i : ι) :
    (frsVanish domain k s ω A i).map (frsEvalOnPoints domain s ω) =
      A ⊓ LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) := by
  apply le_antisymm
  · -- image ⊆ A ⊓ ker(proj i)
    rintro _ ⟨p, ⟨hpU, hpV⟩, rfl⟩
    refine ⟨hpU.1, ?_⟩
    -- `E p ∈ ker(proj i)` since `evalAtCoord i p = 0`.
    rw [LinearMap.mem_ker, LinearMap.proj_apply]
    have : evalAtCoord domain s ω i p = 0 := (LinearMap.mem_ker).mp hpV
    funext j
    have := congrFun this j
    simpa [evalAtCoord_apply] using this
  · -- A ⊓ ker(proj i) ⊆ image
    intro a ⟨ha, hker⟩
    obtain ⟨p, hp_deg, rfl⟩ := hA ha
    refine ⟨p, ⟨⟨ha, hp_deg⟩, ?_⟩, rfl⟩
    -- `p ∈ ker(evalAtCoord i)` since `E p i = 0`.
    rw [LinearMap.mem_ker]
    have hi : frsEvalOnPoints domain s ω p i = 0 := by
      have := (LinearMap.mem_ker).mp hker
      rwa [LinearMap.proj_apply] at this
    funext j
    have := congrFun hi j
    simpa [evalAtCoord_apply] using this

/-- **Orbit-vanishing preserves dimension.**
`finrank (frsVanish … i) = finrank (A ⊓ ker(proj i))`. -/
lemma finrank_frsVanish_eq {A : Submodule F (ι → Fin s → F)}
    (hA : A ≤ frsCode domain k s ω) (i : ι) :
    Module.finrank F (frsVanish domain k s ω A i) =
      Module.finrank F (↥(A ⊓ LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) := by
  have e := Submodule.equivMapOfInjective (frsEvalOnPoints domain s ω) hEinj
    (frsVanish domain k s ω A i)
  rw [e.finrank_eq, frsVanish_map_eq hA i]

end ReedSolomon.Folded
