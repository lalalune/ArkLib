/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G163KleinFourPrimitiveOrbits

/-!
# G164: uniform finite-orbit divisor and primitive mod-four socket

This file supplies the global bookkeeping missing from G163.  A finite type partitioned by orbit
finsets of constant cardinality `k` has total cardinality divisible by `k`.  The proof maps every
element to its orbit finset and applies the exact fiberwise cardinality identity; it requires no
quotient construction or group-action instance.

The four-element specialization is the consumer needed for the generic primitive packet sector.

Issue #466.
-/

set_option autoImplicit false

namespace ArkLib.ProximityGap.Frontier.G164UniformOrbitDivisor

open ArkLib.ProximityGap.Frontier.G156PrimitiveSwapParity
open ArkLib.ProximityGap.Frontier.G163KleinFourPrimitiveOrbits

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A finite family of genuine constant-size orbit classes divides the carrier cardinality. -/
theorem uniformOrbit_card_dvd (orbit : X → Finset X) (k : ℕ)
    (hself : ∀ x, x ∈ orbit x)
    (hclass : ∀ x y, y ∈ orbit x ↔ orbit y = orbit x)
    (hcard : ∀ x, (orbit x).card = k) : k ∣ Fintype.card X := by
  let classes : Finset (Finset X) := Finset.univ.image orbit
  have hmaps : ∀ x ∈ (Finset.univ : Finset X), orbit x ∈ classes := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (f := orbit) (s := (Finset.univ : Finset X)) (t := classes) hmaps
  have hfiber : ∀ C ∈ classes,
      ((Finset.univ : Finset X).filter fun x => orbit x = C).card = k := by
    intro C hC
    obtain ⟨r, -, rfl⟩ := Finset.mem_image.mp hC
    calc
      ((Finset.univ : Finset X).filter fun x => orbit x = orbit r).card =
          (orbit r).card := by
        congr 1
        ext x
        simp [hclass r x]
      _ = k := hcard r
  refine ⟨classes.card, ?_⟩
  rw [← Finset.card_univ, hpartition]
  calc
    (∑ C ∈ classes,
      ((Finset.univ : Finset X).filter fun x => orbit x = C).card) =
        ∑ _C ∈ classes, k := Finset.sum_congr rfl hfiber
    _ = classes.card * k := by simp
    _ = k * classes.card := Nat.mul_comm _ _

/-- Four-element orbit classes force cardinality zero modulo four. -/
theorem uniformOrbit_card_modFour (orbit : X → Finset X)
    (hself : ∀ x, x ∈ orbit x)
    (hclass : ∀ x y, y ∈ orbit x ↔ orbit y = orbit x)
    (hcard : ∀ x, (orbit x).card = 4) : Fintype.card X % 4 = 0 := by
  exact Nat.dvd_iff_mod_eq_zero.mp (uniformOrbit_card_dvd orbit 4 hself hclass hcard)

/-- Finset-relative version: a finite invariant union of constant-size orbit classes has cardinal
divisible by the orbit size. -/
theorem uniformOrbit_finset_card_dvd (S : Finset X) (orbit : X → Finset X) (k : ℕ)
    (hclosed : ∀ x ∈ S, orbit x ⊆ S)
    (hself : ∀ x ∈ S, x ∈ orbit x)
    (hclass : ∀ x ∈ S, ∀ y ∈ orbit x, orbit y = orbit x)
    (hcard : ∀ x ∈ S, (orbit x).card = k) : k ∣ S.card := by
  let classes : Finset (Finset X) := S.image orbit
  have hmaps : ∀ x ∈ S, orbit x ∈ classes := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (f := orbit) (s := S) (t := classes) hmaps
  have hfiber : ∀ C ∈ classes, (S.filter fun x => orbit x = C).card = k := by
    intro C hC
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hC
    calc
      (S.filter fun x => orbit x = orbit r).card = (orbit r).card := by
        congr 1
        ext x
        constructor
        · intro hx
          rw [Finset.mem_filter] at hx
          exact hx.2 ▸ hself x hx.1
        · intro hx
          rw [Finset.mem_filter]
          exact ⟨hclosed r hr hx, hclass r hr x hx⟩
      _ = k := hcard r hr
  refine ⟨classes.card, ?_⟩
  rw [hpartition]
  calc
    (∑ C ∈ classes, (S.filter fun x => orbit x = C).card) =
        ∑ _C ∈ classes, k := Finset.sum_congr rfl hfiber
    _ = classes.card * k := by simp
    _ = k * classes.card := Nat.mul_comm _ _

section Klein

variable {F : Type*} [AddCommGroup F] [Fintype F] [DecidableEq F]

theorem mem_kleinOrbit_self (c : Finset F × Finset F) : c ∈ kleinOrbit c := by
  simp [kleinOrbit]

/-- Klein orbit finsets are constant along their own elements. -/
theorem kleinOrbit_eq_of_mem {c d : Finset F × Finset F} (hd : d ∈ kleinOrbit c) :
    kleinOrbit d = kleinOrbit c := by
  simp only [kleinOrbit, Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · rfl
  · ext z
    simp [kleinOrbit, signedSwapCore, negCore_swapCore] <;> aesop
  · ext z
    simp [kleinOrbit, signedSwapCore, negCore_swapCore] <;> aesop
  · ext z
    simp [kleinOrbit, signedSwapCore, negCore_swapCore] <;> aesop

/-- Any finite invariant sector consisting entirely of generic G163 packets has cardinality
divisible by four. -/
theorem four_dvd_card_of_kleinOrbit_closed
    (S : Finset (Finset F × Finset F))
    (hclosed : ∀ c ∈ S, kleinOrbit c ⊆ S)
    (hfour : ∀ c ∈ S, (kleinOrbit c).card = 4) : 4 ∣ S.card := by
  exact uniformOrbit_finset_card_dvd S kleinOrbit 4 hclosed
    (fun c _ => mem_kleinOrbit_self c)
    (fun _ _ _ hd => kleinOrbit_eq_of_mem hd) hfour

end Klein

#print axioms uniformOrbit_card_dvd
#print axioms uniformOrbit_card_modFour
#print axioms uniformOrbit_finset_card_dvd
#print axioms kleinOrbit_eq_of_mem
#print axioms four_dvd_card_of_kleinOrbit_closed

end ArkLib.ProximityGap.Frontier.G164UniformOrbitDivisor
