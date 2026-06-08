/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CandidateCarvingLoop10
import Mathlib.Data.Fintype.Card

/-!
# Loop 21 — a single smooth symmetry orbit is too small to disprove the prize

Loop 20 showed that the smooth-domain multiplicative symmetry acts on the Reed--Solomon code. The
tempting disproof route is then: find a received word stabilized by a large subgroup and a close
codeword with a free orbit, forcing a large list.

This file records the first self-refutation of that route. The image of any finite symmetry group
has cardinality at most the group, so one orbit inside the smooth domain has size at most the
domain-scale group (`N = 2^m`). But Loop 10 showed that a fixed-gap disproof must beat **every**
polynomial in the domain parameter once the prize's `(2^m)^c₁` numerator is respected. Linear orbit
growth is therefore absorbed by the prize shape; a symmetry-orbit disproof would need many orbits or
some other mechanism producing super-polynomial list growth.

Sorry-free and axiom-clean. See `DISPROOF_LOG.md` (Loop21).
-/

namespace ArkLib.ProximityGap.StructureLoop21

open ArkLib.ProximityGap.CarvingLoop10

variable {G α : Type*}

/-- Pick one preimage for each point in the range of `f`. This embeds the finite image back into the
domain, so the image cardinality is at most the domain cardinality. -/
noncomputable def rangePreimageEmbedding [Fintype G] (f : G → α) :
    Set.range f ↪ G where
  toFun y := Classical.choose y.property
  inj' := by
    intro y z h
    apply Subtype.ext
    have hy : f (Classical.choose y.property) = y.1 := Classical.choose_spec y.property
    have hz : f (Classical.choose z.property) = z.1 := Classical.choose_spec z.property
    calc
      y.1 = f (Classical.choose y.property) := hy.symm
      _ = f (Classical.choose z.property) := congrArg f h
      _ = z.1 := hz

/-- **Finite-orbit cap.** The image of a finite group action, or any finite family of symmetries, has
cardinality at most the number of acting symmetries. In Loop 20 language, one smooth-domain symmetry
orbit cannot be larger than the smooth group itself. -/
theorem range_card_le_domain [Fintype G] (f : G → α) [Fintype (Set.range f)] :
    Fintype.card (Set.range f) ≤ Fintype.card G :=
  Fintype.card_le_of_embedding (rangePreimageEmbedding f)

/-- **Linear-orbit growth is not enough for a fixed-gap prize disproof.** If a candidate list-size
family is bounded by one symmetry orbit of size at most `n`, it cannot beat every polynomial in the
domain parameter. Thus the Loop 20 orbit idea alone is absorbed by the prize numerator. -/
theorem linear_orbit_bound_blocks_fixed_gap_refutation
    {L : ℕ → ℝ} (hupper : ∀ n : ℕ, L n ≤ (n : ℝ)) :
    ¬ BeatsEveryPolynomial L := by
  refine not_beatsEveryPolynomial_of_polynomial_upper (d := 1) (C := 1) zero_lt_one ?_
  intro n
  simpa using hupper n

end ArkLib.ProximityGap.StructureLoop21

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.StructureLoop21.range_card_le_domain
#print axioms ArkLib.ProximityGap.StructureLoop21.linear_orbit_bound_blocks_fixed_gap_refutation
