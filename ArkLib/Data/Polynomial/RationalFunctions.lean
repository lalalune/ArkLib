/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.RationalFunctionsCore
import ArkLib.ToMathlib.BetaRecursion

/-!
# Definitions and Theorems about Function Fields and Rings of Regular Functions

We define the notions of Appendix A of [BCIKS20].

This file is the public surface of the BCIKS20 Appendix-A function-field development.  The bulk of
the machinery (`H_tilde`, `𝕃`, `𝒪`, `embeddingOf𝒪Into𝕃`, `regularElms_set`, the weight calculus
`weight_Λ`/`weight_Λ_over_𝒪`, `Lemma_A_1`, the Claim-A.2 element `ξ`, …) now lives verbatim in the
sibling `RationalFunctionsCore.lean`; this file `import`s it and re-exports every name through the
same `BCIKS20AppendixA`/`BCIKS20AppendixA.ClaimA2` namespaces, so every downstream consumer that
`import`s `RationalFunctions` continues to see the full surface unchanged.

## The `L13` architectural fix (this file)

The split exists for one reason: `BetaRecursion.lean` (the genuine App-A.4 numerator recursion
`betaRec`) needs only the `Core` machinery, so it now `import`s `RationalFunctionsCore` directly.
That breaks the historical import cycle (`BetaRecursion → RationalFunctions → …`) and lets *this*
file `import BetaRecursion`.  As a result the in-tree numerator story can finally be **strengthened
additively** so it genuinely routes through `betaRec`:

* the legacy `β_regular`/`β`/`α`/`γ`/`α'`/`γ'` are kept **verbatim** (same names, same signatures,
  documented as superseded) for downstream compatibility;
* `β_regular_strong`/`β_strong` are the honest replacements: the existence statement carries
  `betaRec` as its witness and *pins the embedding* `embeddingOf𝒪Into𝕃 H (β_strong …) =
  embeddingOf𝒪Into𝕃 H (betaRec …)`, so `beta_strong_embedEq` is `choose_spec` — the in-tree
  definition now genuinely routes through `betaRec`, no opaque `0`-witness.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

## Main Definitions

-/

set_option linter.style.longFile 3200

open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace BCIKS20AppendixA

noncomputable section

namespace ClaimA2

variable {F : Type} [Field F]
         {R : F[X][X][X]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
         [H_natDegree_pos : Fact (0 < H.natDegree)]

/-- There exist regular elements `β` with the *weight upper bound* of Claim A.2 of
Appendix A.4 of [BCIKS20].

**Honesty note (the §5 frontier).** This lemma asserts ONLY the weight upper bound
`Λ(β) ≤ (2t+1)·d_R·D`, which is satisfied vacuously by `β = 0` — and that is exactly
the witness used here (`fun _ => ⟨0, by simp⟩`). It is therefore a true but
*under-specified* statement: the `β` it produces is NOT the genuine recursive
Hensel-lift numerator of [BCIKS20] (A.1), and carries no functional relation to
`R`/`x₀`. The genuine numerator additionally satisfies the lift identity
`embeddingOf𝒪Into𝕃 (β t) = α_t · W^{t+1} · ξ^{e_t}` that Claims 5.8/5.8'/5.9 read off
(`α' t = 0 ⟺ embedding (β t) = 0` via `Lemma_A_1`).

**Status update (L13 / ingredient D).** The genuine recursive numerator *has now been
constructed*: `ArkLib.betaRec` (`ArkLib/ToMathlib/BetaRecursion.lean`) is the App-A.4
recursion (A.1), kernel-clean, defined+terminating, landing in `𝒪 H`, with the weight
bound `betaRec_weight_le_concrete ≤ (2t+1)·d_R·D` (`BetaWeightInduction` +
`BetaWeightCollapse`) and the ingredient-C vanishing `betaRec_embedding_eq_zero_of_
matchingSet_large` (`BetaMatchingVanishes`).  The end-to-end §5 capsule
`ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec` derives the front-door
per-coefficient datum from `betaRec` (β load-bearing), and
`ArkLib.KeystoneStrictResidual.correlatedAgreement_affine_curves_johnson_of_betaRec`
wires that genuine β into the keystone `ProximityGap.correlatedAgreement_affine_curves`.

**Superseded (the L13 architectural fix).** `β_regular`/`β` below are kept *verbatim* for
downstream compatibility, but are now **superseded** by `β_regular_strong`/`β_strong`
(below, this file): with `RationalFunctionsCore.lean` carrying the machinery, `BetaRecursion.lean`
imports *Core* (not this file), so the historical import cycle is gone and the strong numerator
genuinely routes through `betaRec` with the embedding pinned (`beta_strong_embedEq`).

**F1 caveat.** The in-tree `γ` below uses `PowerSeries.subst` of the shift series
`X ↦ X − x₀`, which is only a valid substitution when `x₀ = 0`
(`HasSubst (shiftSeries x₀ H) ↔ x₀ = 0`, kernel-proven in
`ArkLib/ToMathlib/SubstFieldCaveat.lean`).  The keystone wiring carries this as the
explicit hypothesis `hsubst`/`hγ` (automatic in the centred case); the off-centre fix is
to recenter via `PowerSeries.mk (α …)` rather than `subst`.

See `research/proximity-prize/dispositions/ingredient-D-{plan,result}.md` for the full
construction spec. -/
lemma β_regular (R : F[X][X][Y])
                (H : F[X][Y]) [_H_irreducible : Fact (Irreducible H)]
                [_H_natDegree_pos : Fact (0 < H.natDegree)]
                (hH : 0 < H.natDegree)
                {D : ℕ} (_hD : D ≥ Bivariate.totalDegree H) :
    ∀ t : ℕ, ∃ β : 𝒪 H,
      weight_Λ_over_𝒪 hH β D ≤ (2 * t + 1) * Bivariate.natDegreeY R * D :=
  fun _ => ⟨0, by simp⟩

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  if hH : 0 < H.natDegree then
    (β_regular R H hH (Nat.le_refl _) t).choose
  else
    0

/-- The Hensel lift coefficients `α` are of the form as given in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^ (2*t - 1))

def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp t

/-- The power series `γ = ∑ α^t (X - x₀)^t ∈ 𝕃 [[X - x₀]]` as defined in Appendix A.4
of [BCIKS20]. -/
def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y]) [φ : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H) :
    PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk (α x₀ R H hHyp))

def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hHdeg : 0 < H.natDegree) (hHyp : Hypotheses x₀ R H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩) (H_natDegree_pos := ⟨hHdeg⟩) hHyp

/-! ## The `L13` strengthening — the in-tree numerator routed through `betaRec`

The legacy `β_regular`/`β` above are weight-only with a trivial `0`-witness; `β R t = (…).choose`
is therefore opaque, and `embeddingOf𝒪Into𝕃 H (β R t) = embeddingOf𝒪Into𝕃 H (betaRec … t)` is
*unprovable* from it (route (a) of `BetaIdentify`).  Now that this file can `import BetaRecursion`,
we add the honest replacement: an existence statement that carries `betaRec` as its witness and
**pins the embedding**, so the in-tree definition genuinely routes through the App-A.4 recursion. -/

/-- **The strong numerator-existence statement (L13).**  There exists a regular element whose image
in the function field `𝕃 H` *equals* the image of the genuine App-A.4 recursion `betaRec … t`.  The
witness is `betaRec … t` itself, so this is honest: the pinning property `embeddingOf𝒪Into𝕃 H b =
embeddingOf𝒪Into𝕃 H (betaRec … t)` holds by `rfl` on the witness, and (because
`embeddingOf𝒪Into𝕃 H` is injective for `0 < H.natDegree`) it determines the element uniquely — in
sharp contrast to the weight-only `β_regular`, which `0` and infinitely many others also satisfy. -/
lemma β_regular_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    ∃ b : 𝒪 H,
      embeddingOf𝒪Into𝕃 H b
        = embeddingOf𝒪Into𝕃 H (ArkLib.betaRec x₀ R H hHyp Bcoeff t) :=
  ⟨ArkLib.betaRec x₀ R H hHyp Bcoeff t, rfl⟩

/-- **The strong in-tree numerator (L13 drop-in for `β`).**  Unlike the legacy `β`, this routes
through `betaRec`: it is `Exists.choose` of `β_regular_strong`, whose defining property *pins the
embedding* to `betaRec`'s.  This is the honest in-tree numerator the App-A.4 lift identity targets. -/
noncomputable def β_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) : 𝒪 H :=
  (β_regular_strong x₀ R H hHyp Bcoeff t).choose

/-- **The embedding of `β_strong` is pinned to `betaRec` (L13, the residual supplied by definition).**
This is `Exists.choose_spec` of `β_regular_strong`: the in-tree strong numerator's image in `𝕃 H`
*equals* the genuine recursion's image, with **no hypothesis** beyond the standing setup.  This is
exactly the embedding-level numerator-identification residual that `BetaIdentify.BetaEmbedEq` carried
as a *hypothesis* for the legacy `β`; here it is a *theorem*. -/
@[simp] theorem beta_strong_embedEq (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (β_strong x₀ R H hHyp Bcoeff t)
      = embeddingOf𝒪Into𝕃 H (ArkLib.betaRec x₀ R H hHyp Bcoeff t) :=
  (β_regular_strong x₀ R H hHyp Bcoeff t).choose_spec

/-- **`β_strong = betaRec` as `𝒪`-elements** (for `0 < H.natDegree`).  Because the embedding
`embeddingOf𝒪Into𝕃 H` is injective, the pinned embedding identity `beta_strong_embedEq` upgrades to
an element-level identity: the strong in-tree numerator *is* the App-A.4 recursion. -/
theorem beta_strong_eq_betaRec (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (hH : 0 < H.natDegree) (t : ℕ) :
    β_strong x₀ R H hHyp Bcoeff t = ArkLib.betaRec x₀ R H hHyp Bcoeff t :=
  embeddingOf𝒪Into𝕃_injective hH (beta_strong_embedEq x₀ R H hHyp Bcoeff t)

/-- **The strong Hensel-lift coefficient `α_strong`**, built from `β_strong` (the L13-honest
analogue of `α`).  Its denominators are *identical* to those of `α`/`αFromBeta`; the numerator is
the strong (betaRec-routed) one.  Because `beta_strong_embedEq` pins the numerator's embedding,
`α_strong` is definitionally the `betaRec`-built coefficient `BetaToCurveCoeffPolys.αFromBeta`. -/
noncomputable def α_strong (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [Fact (Irreducible H)] [Fact (0 < H.natDegree)] (hHyp : Hypotheses x₀ R H)
    (Bcoeff : (i₁ : ℕ) → {m : ℕ} → Nat.Partition m → 𝒪 H) (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β_strong x₀ R H hHyp Bcoeff t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hHyp)) ^ (2 * t - 1))

end ClaimA2
end
end BCIKS20AppendixA

/-! ## Axiom audit for the `L13` strengthening — every new declaration must rest only on
`[propext, Classical.choice, Quot.sound]`, no `sorry`/`admit`/`axiom`/`native_decide`. -/
#print axioms BCIKS20AppendixA.ClaimA2.β_regular_strong
#print axioms BCIKS20AppendixA.ClaimA2.β_strong
#print axioms BCIKS20AppendixA.ClaimA2.beta_strong_embedEq
#print axioms BCIKS20AppendixA.ClaimA2.beta_strong_eq_betaRec
#print axioms BCIKS20AppendixA.ClaimA2.α_strong
