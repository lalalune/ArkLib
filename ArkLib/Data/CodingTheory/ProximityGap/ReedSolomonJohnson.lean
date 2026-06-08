/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound
import ArkLib.Data.CodingTheory.ProximityGap.UniqueDecodingListBound

/-!
# The explicit Reed–Solomon Johnson list-decoding bound (verified, composed)

This file composes two independently-proven bricks into the **Reed–Solomon-specific** Johnson
list-size bound — the second row of the ABF26 proximity table (Issue #232 §3, the "up to the
Johnson radius `1 − √ρ`" regime) instantiated for the *explicit* RS codes the prize fixes:

* `ArkLib.JohnsonList.johnson_list_bound_div` — the abstract second-moment/Gram Johnson bound: a list
  of words pairwise agreeing on `≤ b` coordinates, each agreeing with `f` on `≥ a`, has size
  `≤ n² / (a² − n·b)` once `n·b < a²`.
* `ArkLib.CodingTheory.UniqueDecoding.agreement_card_le` — distinct degree-`<k` polynomials on an
  injective domain agree on `≤ k − 1` coordinates (root counting).

Plugging `b = k − 1` (the RS pairwise-agreement bound) into the abstract bound gives:

`reedSolomon_johnson_list_bound` — a list `L` of Reed–Solomon codewords of degree-`<k` polynomials,
each agreeing with a received word `f` on `≥ a` of the `n = |ι|` coordinates, has size
`|L| ≤ n² / (a² − n·(k−1))` whenever `n·(k−1) < a²` (the RS Johnson gap; with `a = n − e` and
`d = n − k + 1` this is exactly the Johnson radius `e < n − √(n(k−1)) = n(1 − √((k−1)/n)) ≈ n(1 − √ρ)`).

`sorry`-free, axiom-clean, and a genuine *composition* (not a duplicate): it is the explicit-RS
instance of the proven Johnson regime. Not the open prize apex (the interior `(1−√ρ, 1−ρ)`).
-/

open Polynomial Finset

namespace ArkLib.CodingTheory.ReedSolomonJohnson

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F]

/-- **Reed–Solomon Johnson list-decoding bound.** A list `L` of words, each of which is the
evaluation `i ↦ p(D i)` of some polynomial `p` of degree `< k` on an injective domain `D`, with each
agreeing with the received word `f` on at least `a` coordinates, has size
`|L| ≤ n² / (a² − n·(k−1))` whenever `n·(k−1) < a²` (`n = |ι|`).

Proof: distinct degree-`<k` polynomials agree on `≤ k − 1` coordinates (`agreement_card_le`), so the
codewords pairwise agree on `≤ k − 1`; apply the abstract Johnson bound with `b = k − 1`. -/
theorem reedSolomon_johnson_list_bound (D : ι ↪ F) (k : ℕ) (f : ι → F)
    (L : Finset (ι → F)) (a : ℕ)
    (hpoly : ∀ c ∈ L, ∃ p : F[X], p.natDegree < k ∧ c = fun i => p.eval (D i))
    (hclose : ∀ c ∈ L, a ≤ (Finset.univ.filter (fun x => c x = f x)).card)
    (hgap : Fintype.card ι * (k - 1) < a ^ 2) :
    L.card ≤ (Fintype.card ι) ^ 2 / (a ^ 2 - Fintype.card ι * (k - 1)) := by
  refine ArkLib.JohnsonList.johnson_list_bound_div f L a (k - 1) hclose ?_ hgap
  intro c hc c' hc' hne
  obtain ⟨p, hp, rfl⟩ := hpoly c hc
  obtain ⟨q, hq, rfl⟩ := hpoly c' hc'
  have hpq : p ≠ q := fun h => hne (by rw [h])
  exact ArkLib.CodingTheory.UniqueDecoding.agreement_card_le hp hq hpq

end ArkLib.CodingTheory.ReedSolomonJohnson
