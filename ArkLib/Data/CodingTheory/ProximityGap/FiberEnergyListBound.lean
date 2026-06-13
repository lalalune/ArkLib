/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumFourthMoment

set_option linter.style.longLine false

/-!
# The fibre-max ≤ collision-energy bridge: Form 2 ⟹ Form 4 (Issue #389)

The unifying chain of #389 runs character sum (Form 1) → additive energy (Form 2) → list size
(Form 4) → `δ*` (Form 5). `EnergyCharacterTransport` supplies 1↔2. This file supplies the **2 → 4**
rung in its cleanest, most general form: for *any* fibre census, the **largest fibre squared is at
most the collision energy**, because every ordered pair inside the top fibre collides. So a small
energy forces a short list — exactly the input that pins `δ*`.

* `fiberMax_sq_le_collisionEnergy` (abstract):  `(max_v #{i∈S : f i = v})² ≤ #{(i,j)∈S² : f i = f j}`.
* `card_le_image_mul_fiberMax` (abstract):  `|S| ≤ |image f| · maxfibre` (averaging, the converse
  popularity direction).
* `maxRep_sq_le_addEnergy` (concrete):  on `S = H × H`, `f(a,b) = a+b`, the census fibre is the
  representation function `r(v) = #{(a,b)∈H² : a+b=v}` and the collision energy is **exactly** the
  in-tree `addEnergy H`. Hence `(max_v r(v))² ≤ E(H)`: the most-popular sum (the linear/`r=2` list
  size) is at most `√E(H)`. This composes directly with `EnergyCharacterTransport` (1→2) and
  `EnergyDilationReduction` on the *same* `addEnergy` object.

So a square-root-cancellation character bound (Form 1) ⟹ Sidon-order energy (Form 2,
`sidon_order_of_sqrt_charSum`) ⟹ `max_v r(v) ≤ √E = O(n)` (Form 4) — the list at the linear level
is pinned at its random value, hence so is `δ*`. The higher-degree list rungs (`r ≥ 3`,
`t`-subset fibres) are the same inequality one tower up, where the controlling collision energy is
the recognized open object.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #389.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumFourthMoment (addEnergy)

namespace ArkLib.ProximityGap.FiberEnergyListBound

variable {ι β : Type*} [DecidableEq β]

/-- The fibre of the census map `f` over a value `v`: `#{i ∈ S : f i = v}`. -/
def fiberCount (S : Finset ι) (f : ι → β) (v : β) : ℕ := (S.filter (fun i => f i = v)).card

/-- The largest fibre of `f` over `S` (the "list size" of the census): `max_v #{i∈S : f i = v}`. -/
def fiberMax (S : Finset ι) (f : ι → β) : ℕ := (S.image f).sup (fun v => fiberCount S f v)

/-- The collision energy of `f` over `S`: `#{(i,j)∈S² : f i = f j}` (the "additive energy" of the
census). -/
def collisionEnergy (S : Finset ι) (f : ι → β) : ℕ :=
  ((S ×ˢ S).filter (fun p => f p.1 = f p.2)).card

/-- **The bridge `(max fibre)² ≤ collision energy`.** The top fibre `A = {i∈S : f i = v*}` has its
entire `A × A` inside the collision set (any two of its members share value `v*`), so
`|A|² ≤ #{collisions}`. A small collision energy therefore forces every fibre — in particular the
largest, the list size — to be small. -/
theorem fiberMax_sq_le_collisionEnergy (S : Finset ι) (f : ι → β) :
    (fiberMax S f) ^ 2 ≤ collisionEnergy S f := by
  classical
  rcases (S.image f).eq_empty_or_nonempty with h | h
  · rw [fiberMax, h, Finset.sup_empty]; simp
  · obtain ⟨v, _, hsup⟩ := Finset.exists_mem_eq_sup (S.image f) h (fun v => fiberCount S f v)
    rw [fiberMax, hsup]
    have hsub :
        (S.filter (fun i => f i = v)) ×ˢ (S.filter (fun i => f i = v))
          ⊆ (S ×ˢ S).filter (fun p => f p.1 = f p.2) := by
      intro p hp
      rw [Finset.mem_product, Finset.mem_filter, Finset.mem_filter] at hp
      obtain ⟨⟨hp1S, hp1v⟩, hp2S, hp2v⟩ := hp
      rw [Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨hp1S, hp2S⟩, by rw [hp1v, hp2v]⟩
    calc (fiberCount S f v) ^ 2
        = ((S.filter (fun i => f i = v)) ×ˢ (S.filter (fun i => f i = v))).card := by
          rw [Finset.card_product, fiberCount]; ring
      _ ≤ collisionEnergy S f := Finset.card_le_card hsub

/-- **Averaging (the converse popularity direction): `|S| ≤ |image f| · maxfibre`.** Every element
lands in some fibre, and each value's fibre is at most the maximum, so the total is at most the
number of values times the largest fibre. Hence `maxfibre ≥ |S| / #values` — a list this short is
only possible if the census spreads near-uniformly. -/
theorem card_le_image_mul_fiberMax (S : Finset ι) (f : ι → β) :
    S.card ≤ (S.image f).card * fiberMax S f := by
  classical
  calc S.card = ∑ v ∈ S.image f, fiberCount S f v := by
        simp only [fiberCount]; exact Finset.card_eq_sum_card_image f S
      _ ≤ ∑ _v ∈ S.image f, fiberMax S f :=
        Finset.sum_le_sum (fun v hv => Finset.le_sup (f := fun v => fiberCount S f v) hv)
      _ = (S.image f).card * fiberMax S f := by rw [Finset.sum_const, smul_eq_mul]

/-- **Concrete bridge on the additive census.** With `S = H × H` and `f(a,b) = a+b`, the collision
energy is exactly the in-tree additive energy `addEnergy H`. -/
theorem collisionEnergy_add_eq_addEnergy {F : Type*} [Field F] [DecidableEq F] (H : Finset F) :
    collisionEnergy (H ×ˢ H) (fun p => p.1 + p.2) = addEnergy H := by
  unfold collisionEnergy addEnergy
  rw [Finset.card_filter]
  simp only [Finset.sum_product]

/-- The representation function `r(v) = #{(a,b)∈H² : a+b=v}` packaged as the additive census fibre
max: `maxRep H = max_v r(v)`. -/
def maxRep {F : Type*} [Field F] [DecidableEq F] (H : Finset F) : ℕ :=
  fiberMax (H ×ˢ H) (fun p => p.1 + p.2)

/-- **`(max_v r(v))² ≤ E(H)`.** The most-popular sum value (the linear/`r=2` list size) is at most
`√E(H)`. On the same `addEnergy` object as `EnergyCharacterTransport`/`EnergyDilationReduction`, so
the chain Form 1 → Form 2 → Form 4 closes: a `√n` character bound gives `E(H) = O(n²)` gives
`max_v r(v) = O(n)`. -/
theorem maxRep_sq_le_addEnergy {F : Type*} [Field F] [DecidableEq F] (H : Finset F) :
    (maxRep H) ^ 2 ≤ addEnergy H := by
  rw [maxRep, ← collisionEnergy_add_eq_addEnergy]
  exact fiberMax_sq_le_collisionEnergy _ _

end ArkLib.ProximityGap.FiberEnergyListBound

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.FiberEnergyListBound.fiberMax_sq_le_collisionEnergy
#print axioms ArkLib.ProximityGap.FiberEnergyListBound.card_le_image_mul_fiberMax
#print axioms ArkLib.ProximityGap.FiberEnergyListBound.collisionEnergy_add_eq_addEnergy
#print axioms ArkLib.ProximityGap.FiberEnergyListBound.maxRep_sq_le_addEnergy
