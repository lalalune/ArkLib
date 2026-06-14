/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

/-!
# Ring-homomorphism merge-only monotonicity of the bad-scalar count (#407)

This Frontier file records the **characteristic-free** half of the window
characteristic-faithfulness lever for the Ethereum Proximity Prize (issue #407):
the *no-excess* direction `N(char-p) ≤ N(char-0)`.

## The mathematical content

At the boundary band the deployed object is, per genuine direction `(a,b)`, the
set of **bad scalars**
`γ_T = − h_{a−k}(ζ^T) / h_{b−k}(ζ^T)`,
a ratio of complete-homogeneous (Schur) values living in `Frac(ℤ[ζ_n])`, indexed
by the `T`'s ranging over a fixed finite index set `ι`.

Reducing `ℤ[ζ_n] → 𝔽_q` is a **ring homomorphism** `φ` (it sends `0 ↦ 0`). The
char-`p` bad-scalar value at a `T` is `φ(num T) · φ(den T)⁻¹`, and it is only
*eligible* where `φ(den T) ≠ 0` (a vanishing denominator deletes that `T`).
Hence the char-`p` bad-scalar set is the **image** of (a subset of) the char-0
data: reduction can only

* **merge** distinct `T`'s onto the same char-`p` scalar (a collision), or
* **delete** a `T` whose denominator vanishes mod `q`,

and it can **never create a new finite scalar**. Cardinality of an image is at
most the cardinality of the (eligible subset of the) source, so

> **`N(char-p) ≤ N(char-0)`** — characteristic-free, scale-independent.

This is exactly the half the prize δ* lower bound needs: char-`p` never promotes a
good band over the char-0 budget (the Kambiré edge, margin 0). The companion open
half — that the char-0 count *equals* the budget at the Kambiré edge — is
characteristic-*independent* (coset-saturation / sumset-max, in
`FactorizationRigidity.lean`) and is NOT addressed here.

## What this file proves (axiom-clean)

1. `card_image_le_index` — the bare Finset core: any per-index value map's image
   has card ≤ the index count.
2. `card_eligible_image_le_card_eligible` / `..._le_index` — with an eligibility
   predicate (denominator-nonvanishing), the char-`p` distinct-scalar count is at
   most the number of eligible indices, hence at most the total index count.
3. `ringHom_badScalar_card_le` — the **ring-hom specialization**: with `num den :
   ι → R`, `φ : R →+* S`, eligibility `φ (den t) ≠ 0`, the distinct char-`p`
   bad-scalar count `#{ φ(num t)·φ(den t)⁻¹ }` is at most `#ι`.
4. `badScalar_charP_card_le_charZero` — the headline **merge-only monotonicity**:
   when the char-`p` value *factors through* the char-0 value (a `red : K → S`
   with `charP t = red (charZero t)` on eligible `t` — i.e. *no SPLIT*: equal
   char-0 values force equal char-`p` values), the char-`p` distinct-scalar count
   is `≤` the char-0 distinct-scalar count. This is `N(char-p) ≤ N(char-0)`.

Tier 4 is the reusable brick the synthesis calls for; tiers 1–3 are the bare
mechanism it is assembled from. The wiring to the concrete `h_j` Schur ratios on
`μ_n` is described in `wiringNote` below (it only has to supply the `red`
factorization, which is the reduction map on `Frac(ℤ[ζ_n])`).
-/

namespace ProximityGap.Frontier.RingHomBadScalarMono

open Finset

/-! ## Tier 1 — the bare Finset image core (merge-only) -/

variable {ι S : Type*} [DecidableEq S]

/--
**Merge-only core.** The set of char-`p` scalar values realized over an index
finset `T` is the image of `T` under the value map `v`, so its cardinality is at
most `#T`. Distinct indices that collide onto the same scalar are *merged*; the
count can only drop.
-/
theorem card_image_le_index (T : Finset ι) (v : ι → S) :
    (T.image v).card ≤ T.card :=
  Finset.card_image_le

/-! ## Tier 2 — eligibility filter (delete-only) on top of merge-only -/

variable {ι' : Type*} [DecidableEq ι']

/--
**Delete + merge.** With an eligibility predicate `elig` (think:
`φ(denominator) ≠ 0`), the realized char-`p` scalar set is the image of the
*eligible* indices, so its cardinality is at most the number of eligible indices.
-/
theorem card_eligible_image_le_card_eligible
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig] (v : ι → S) :
    ((T.filter elig).image v).card ≤ (T.filter elig).card :=
  Finset.card_image_le

/--
**Delete + merge, against the full index count.** Dropping ineligible indices and
merging collisions, the char-`p` scalar count is at most the *total* index count.
-/
theorem card_eligible_image_le_index
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig] (v : ι → S) :
    ((T.filter elig).image v).card ≤ T.card :=
  le_trans Finset.card_image_le (Finset.card_le_card (Finset.filter_subset _ _))

/-! ## Tier 3 — the ring-homomorphism specialization -/

variable {R : Type*} [CommRing R] [CommRing S] [DecidableEq S]

/--
**Ring-hom bad-scalar count bound.** Let `num den : ι → R` be the
(numerator, denominator) ratio data, `φ : R →+* S` the reduction ring
homomorphism, and call `t` *eligible* when `φ (den t) ≠ 0`. The distinct
char-`p` bad-scalar count

`#{ φ(num t) · φ(den t)⁻¹ : t eligible }`

is at most the total index count `#T`. (Reduction is `0 ↦ 0`; vanishing
denominators delete, collisions merge — never create.)
-/
theorem ringHom_badScalar_card_le
    [Field S] (T : Finset ι) (num den : ι → R) (φ : R →+* S) :
    ((T.filter (fun t => φ (den t) ≠ 0)).image
        (fun t => φ (num t) * (φ (den t))⁻¹)).card ≤ T.card :=
  card_eligible_image_le_index T (fun t => φ (den t) ≠ 0)
    (fun t => φ (num t) * (φ (den t))⁻¹)

/-! ## Tier 4 — the headline merge-only monotonicity `N(char-p) ≤ N(char-0)` -/

variable {K : Type*} [DecidableEq K]

/--
**Merge-only monotonicity (the prize brick): `N(char-p) ≤ N(char-0)`.**

Setup. `charZero : ι → K` assigns to each index its char-0 bad scalar (e.g.
`γ_T ∈ Frac(ℤ[ζ_n])`); `charP : ι → S` assigns its char-`p` bad scalar (e.g. the
reduction `γ̄_T ∈ 𝔽_q`); `elig : ι → Prop` is char-`p` eligibility (denominator
nonvanishing mod `q`).

`red : K → S` is the reduction map on the fraction field. The hypothesis
`hfactor` says the char-`p` value *factors through* the char-0 value on eligible
indices: `charP t = red (charZero t)`. This is precisely the **no-SPLIT** content
verified in the probes — a single char-0 scalar maps to a single char-`p` scalar,
so reduction can only *merge* char-0 scalars, never split one into several.

Conclusion. The char-`p` distinct-scalar count over the eligible indices is at
most the char-0 distinct-scalar count over *all* indices:

`#{ charP t : t eligible } ≤ #{ charZero t : t }`.

That is `N(char-p) ≤ N(char-0)`, characteristic-free and scale-independent.
-/
theorem badScalar_charP_card_le_charZero
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig]
    (charZero : ι → K) (charP : ι → S) (red : K → S)
    (hfactor : ∀ t ∈ T, elig t → charP t = red (charZero t)) :
    ((T.filter elig).image charP).card ≤ (T.image charZero).card := by
  -- On the eligible indices, `charP = red ∘ charZero`, so the realized char-`p`
  -- set equals `red` applied to the char-0 image of the eligible indices.
  have hEqOn : Set.EqOn charP (red ∘ charZero) (↑(T.filter elig)) := by
    intro t ht
    rw [Finset.coe_filter, Set.mem_setOf_eq] at ht
    simpa using hfactor t ht.1 ht.2
  have hrewrite :
      (T.filter elig).image charP
        = ((T.filter elig).image charZero).image red := by
    rw [Finset.image_congr hEqOn, Finset.image_image]
  calc
    ((T.filter elig).image charP).card
        = (((T.filter elig).image charZero).image red).card := by rw [hrewrite]
    _ ≤ ((T.filter elig).image charZero).card := Finset.card_image_le
    _ ≤ (T.image charZero).card :=
          Finset.card_le_card (Finset.image_subset_image (Finset.filter_subset _ _))

/--
**Budget-consumer form.** If the char-0 distinct-scalar count is at most the
Kambiré budget `B`, then so is the char-`p` count — char-`p` never exceeds the
char-0 budget.
-/
theorem badScalar_charP_card_le_budget
    (T : Finset ι) (elig : ι → Prop) [DecidablePred elig]
    (charZero : ι → K) (charP : ι → S) (red : K → S) {B : ℕ}
    (hfactor : ∀ t ∈ T, elig t → charP t = red (charZero t))
    (hbudget : (T.image charZero).card ≤ B) :
    ((T.filter elig).image charP).card ≤ B :=
  le_trans
    (badScalar_charP_card_le_charZero T elig charZero charP red hfactor) hbudget

/-!
## Wiring to the concrete `h_j` Schur-ratio bad-scalar map

To deploy `badScalar_charP_card_le_charZero` on the prize object one instantiates:

* `ι := ` the finite index set of admissible boundary-band subsets `T` for a fixed
  genuine direction `(a,b)`;
* `K := Frac(ℤ[ζ_n])` (or its image field), `charZero t := γ_T =
  − h_{a−k}(ζ^T) / h_{b−k}(ζ^T)` (the char-0 bad scalar);
* `S := 𝔽_q`, `charP t :=` the reduction of `γ_T`;
* `elig t := φ(h_{b−k}(ζ^T)) ≠ 0` (denominator nonvanishing mod `q`);
* `red :=` the field map induced by the reduction ring homomorphism
  `φ : ℤ[ζ_n] → 𝔽_q` on the fraction field (defined on the eligible locus).

The only nontrivial hypothesis is `hfactor : charP t = red (charZero t)` on
eligible `t`, which holds because `φ` is a **ring homomorphism**: it commutes with
the numerator/denominator arithmetic defining `γ_T`, so reducing the ratio equals
the ratio of reductions wherever the denominator survives. (`ringHom_badScalar_card_le`
above is the same statement with the ratio written out explicitly via `φ`, `num`,
`den`, and `⁻¹` in a field `S`, requiring no separate `red`.) The conclusion is
`N(char-p) ≤ N(char-0)` per direction; taking the max over the finite set of
genuine directions inherits the inequality, which is the no-excess half of window
characteristic-faithfulness the prize δ* lower bound consumes.

This file proves the characteristic-FREE monotonicity only. It does NOT prove the
companion char-0 statement `N(char-0) = budget` at the Kambiré edge (coset-
saturation / sumset-max), which is the remaining, characteristic-independent open
input.
-/

/-- Documentation anchor for the wiring note above. -/
theorem wiringNote : True := trivial

end ProximityGap.Frontier.RingHomBadScalarMono

#print axioms ProximityGap.Frontier.RingHomBadScalarMono.card_image_le_index
#print axioms
  ProximityGap.Frontier.RingHomBadScalarMono.card_eligible_image_le_card_eligible
#print axioms ProximityGap.Frontier.RingHomBadScalarMono.card_eligible_image_le_index
#print axioms ProximityGap.Frontier.RingHomBadScalarMono.ringHom_badScalar_card_le
#print axioms ProximityGap.Frontier.RingHomBadScalarMono.badScalar_charP_card_le_charZero
#print axioms ProximityGap.Frontier.RingHomBadScalarMono.badScalar_charP_card_le_budget
