/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.HigherOrderMDSFrame
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Higher-order MDS and list decoding: the dual-annihilator entry (#389, layer 3)

The Brakensiek–Gopi–Makam list-decoding argument, set up over the frame model of
layer 2.  Messages are dual functionals `m : Module.Dual K V`; the codeword value at
coordinate `ζ` is `m (v ζ)` (for RS, `m` is the message polynomial's coefficient
functional and `m (v ζ) = p(ζ)`).  A received word is `y : ι → K`, and the agreement
set of a message is `{ζ : m (v ζ) = y ζ}`.

**The entry lemma** (`diff_mem_dualAnnihilator`): if two messages `m, m'` agree with `y`
on a common set `J`, their difference `m − m'` lies in the **dual annihilator** of the
column-span `frameSpan K v J`.  Under an MDS frame that annihilator has dimension
`k − |J|` (`finrank_dualAnnihilator_frameSpan`), so a *large* common agreement set forces
the difference into a *small* subspace — the dimension squeeze that, iterated over `L+1`
codewords against higher-order genericity, yields the BGM list bound.

This is the entry point; the full bound (MDS(L+1) ⟹ list ≤ L past Johnson) chains these
squeezes against `IsHigherMDS`.

Issue #389.
-/

open Finset Module ArkLib.HigherOrderMDS

namespace ArkLib.HigherOrderMDS

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq K]

/-- The agreement set of a message functional `m` with a received word `y`. -/
noncomputable def agreeFinset (v : ι → V) (y : ι → K) (m : Module.Dual K V) : Finset ι :=
  Finset.univ.filter (fun ζ => m (v ζ) = y ζ)

@[simp] theorem mem_agreeFinset {v : ι → V} {y : ι → K} {m : Module.Dual K V} {ζ : ι} :
    ζ ∈ agreeFinset v y m ↔ m (v ζ) = y ζ := by
  simp [agreeFinset]

/-- **The dual-annihilator entry lemma.**  If messages `m, m'` both agree with `y` on
every coordinate of `J`, their difference annihilates the column-span `frameSpan K v J`. -/
theorem diff_mem_dualAnnihilator (K : Type*) [Field K] [Module K V] (v : ι → V)
    {y : ι → K} {m m' : Module.Dual K V} {J : Finset ι}
    (hm : ∀ ζ ∈ J, m (v ζ) = y ζ) (hm' : ∀ ζ ∈ J, m' (v ζ) = y ζ) :
    (m - m') ∈ (frameSpan K v J).dualAnnihilator := by
  rw [Submodule.mem_dualAnnihilator]
  intro w hw
  -- vanish on the spanning set, then on the span
  refine Submodule.span_induction (p := fun w _ => (m - m') w = 0) ?_ ?_ ?_ ?_ hw
  · rintro x ⟨ζ, hζ, rfl⟩
    have : (m - m') (v ζ) = m (v ζ) - m' (v ζ) := by simp
    rw [this, hm ζ hζ, hm' ζ hζ, sub_self]
  · simp
  · intro x z _ _ hx hz; simp [map_add, hx, hz]
  · intro a x _ hx; simp [map_smul, hx]

/-- Under an MDS frame, the difference annihilator from a `≤ k` agreement set has the
*small* dimension `k − |J|`: a large agreement set squeezes the difference. -/
theorem finrank_dualAnnihilator_frameSpan {v : ι → V} (hv : IsMDSFrame K v)
    {J : Finset ι} (hJ : J.card ≤ finrank K V) :
    finrank K ↥(frameSpan K v J).dualAnnihilator = finrank K V - J.card := by
  have hadd := Subspace.finrank_add_finrank_dualAnnihilator_eq (frameSpan K v J)
  rw [finrank_frameSpan hv hJ] at hadd
  omega

end ArkLib.HigherOrderMDS

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ArkLib.HigherOrderMDS.diff_mem_dualAnnihilator
#print axioms ArkLib.HigherOrderMDS.finrank_dualAnnihilator_frameSpan
