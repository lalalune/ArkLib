/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic

/-!
# Issue #232 — the folding-transfer NO-GO (§6 route 4, blocked in the naive direction)

The issue's §6 lists "subspace-design / folded-RS transfer" as a viable research route: folded RS
achieves list-decoding capacity (CZ25/Guruswami–Rudra, with alphabet blow-up), and the smooth
`2^m`-domain folds naturally along its subgroup ⟨ω⟩ of order `d` (orbits `{x, ωx, …, ω^{d−1}x}`).
Could a capacity bound for the FOLDED code transfer to the plain smooth-domain RS list?

**This file machine-checks why the naive transfer is blocked.**  Model the folded structure
abstractly: coordinates `Fin N × Fin d` (`N` orbits of size `d`), folding by the first coordinate.

* `foldedAgree_mul_le_plainAgree` — the only direction that holds: each fully-agreeing orbit
  contributes `d` plain agreements, so `d · foldedAgree ≤ plainAgree`.  (A plain-list bound therefore
  transfers UP to the folded code — the useless direction.)
* `folding_transfer_no_go` (the NO-GO) — the converse fails **maximally**: over any nontrivial field
  there is a word `w` with `plainAgree w 0 = N·(d−1)` — a `(1 − 1/d)` fraction of ALL coordinates,
  far above any list-decoding radius — while `foldedAgree w 0 = 0`: **not a single orbit agrees**.
  Witness: `w(o, p) = 1` if `p = 0` else `0` (one corrupted position per orbit).

Consequence: a folded-code list bound at ANY radius (even capacity) says nothing about the plain
list even at relative radius `1/d` — the agreement structure simply does not transfer downward.  The
folded-RS capacity results bound lists of words that are close IN THE FOLDED METRIC, a strictly
smaller set than plain-close words.  Closing this gap (a transfer that survives per-orbit
corruption) is precisely the open part of §6 route 4 — now isolated as such, with the naive route a
theorem-certified dead end.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open Finset

namespace ArkLib.CodingTheory.FoldingTransferNoGo

variable {F : Type*} [DecidableEq F] {N d : ℕ}

/-- Plain (unfolded) agreement count between two words on the orbit-structured domain. -/
def plainAgree (w v : Fin N × Fin d → F) : ℕ :=
  (Finset.univ.filter fun x : Fin N × Fin d => w x = v x).card

/-- Folded agreement count: the number of orbits on which the words agree at EVERY position. -/
def foldedAgree (w v : Fin N × Fin d → F) : ℕ :=
  (Finset.univ.filter fun o : Fin N => ∀ p : Fin d, w (o, p) = v (o, p)).card

/-- **The trivial (upward) transfer:** `d · foldedAgree ≤ plainAgree`.  Each fully-agreeing orbit
contributes its `d` positions to the plain count: the map `(o, p) ↦ (o, p)` injects
`(folded orbits) × Fin d` into the plain agreement set. -/
theorem foldedAgree_mul_le_plainAgree (w v : Fin N × Fin d → F) :
    d * foldedAgree w v ≤ plainAgree w v := by
  classical
  rw [foldedAgree, plainAgree]
  -- count the product set (agreeing orbits) ×ˢ univ inside the plain agreement set
  have hsub : ((Finset.univ.filter fun o : Fin N => ∀ p : Fin d, w (o, p) = v (o, p)) ×ˢ
      (Finset.univ : Finset (Fin d))) ⊆
      (Finset.univ.filter fun x : Fin N × Fin d => w x = v x) := by
    intro x hx
    rw [Finset.mem_product] at hx
    obtain ⟨ho, _⟩ := hx
    rw [Finset.mem_filter] at ho ⊢
    exact ⟨Finset.mem_univ _, ho.2 x.2⟩
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_product, Finset.card_univ, Fintype.card_fin] at hcard
  omega

/-- The adversarial word: corrupted at exactly the first position of every orbit. -/
def oneCorruptionPerOrbit (N d : ℕ) (F : Type*) [Zero F] [One F] [DecidableEq (Fin d)] :
    Fin N × Fin d → F :=
  fun x => if x.2 = (0 : Fin d) then 1 else 0

/-- **THE FOLDING-TRANSFER NO-GO.**  Over any nontrivial field-like type (`0 ≠ 1`), with `d ≥ 1`,
the word corrupted at one position per orbit has:

* plain agreement with the zero word `= N·(d−1)` — a `(1−1/d)` fraction of all coordinates
  (far above every list-decoding radius), yet
* folded agreement `= 0` — **no orbit survives**.

So folded-code list bounds (at any radius, including the capacity results for folded RS) give NO
information about plain-close words: the naive §6-route-4 transfer is a certified dead end. -/
theorem folding_transfer_no_go (N d : ℕ) (hd : 0 < d) (F : Type*) [Zero F] [One F]
    [DecidableEq F] (h01 : (0 : F) ≠ 1) :
    plainAgree (oneCorruptionPerOrbit N d F) (0 : Fin N × Fin d → F) = N * (d - 1) ∧
    foldedAgree (oneCorruptionPerOrbit N d F) (0 : Fin N × Fin d → F) = 0 := by
  classical
  constructor
  · -- plain agreement: exactly the positions with p ≠ 0, i.e. N·(d−1) of them
    rw [plainAgree]
    have hset : (Finset.univ.filter fun x : Fin N × Fin d =>
        oneCorruptionPerOrbit N d F x = (0 : Fin N × Fin d → F) x)
        = Finset.univ.filter fun x : Fin N × Fin d => x.2 ≠ (0 : Fin d) := by
      apply Finset.filter_congr
      intro x _
      simp only [oneCorruptionPerOrbit, Pi.zero_apply]
      by_cases h : x.2 = (0 : Fin d)
      · simp only [h, if_pos rfl]
        constructor
        · intro h1; exact absurd h1.symm h01
        · intro hne; exact absurd h hne
      · simp only [if_neg h]
        constructor
        · intro _; exact h
        · intro _; rfl
    rw [hset]
    -- count pairs (o, p) with p ≠ 0: N · (d−1)
    have : (Finset.univ.filter fun x : Fin N × Fin d => x.2 ≠ (0 : Fin d))
        = (Finset.univ : Finset (Fin N)) ×ˢ (Finset.univ.filter fun p : Fin d => p ≠ 0) := by
      ext x
      simp [Finset.mem_product, Finset.mem_filter]
    rw [this, Finset.card_product, Finset.card_univ, Fintype.card_fin,
        Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ, Fintype.card_fin]
  · -- folded agreement: every orbit fails at position 0 (where the word is 1 ≠ 0)
    rw [foldedAgree, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro o _
    intro hall
    have h := hall ⟨0, hd⟩
    simp only [oneCorruptionPerOrbit, Pi.zero_apply] at h
    rw [if_pos rfl] at h
    exact h01 h.symm

/-- Non-vacuity at concrete scale: `N = 8` orbits of size `d = 4` over `ZMod 5` — plain agreement
`24` of `32` coordinates (relative `3/4`), folded agreement `0`. -/
theorem no_go_concrete :
    plainAgree (oneCorruptionPerOrbit 8 4 (ZMod 5)) 0 = 24 ∧
    foldedAgree (oneCorruptionPerOrbit 8 4 (ZMod 5)) 0 = 0 := by
  have h := folding_transfer_no_go 8 4 (by norm_num) (ZMod 5) (by decide)
  simpa using h

end ArkLib.CodingTheory.FoldingTransferNoGo

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.FoldingTransferNoGo.foldedAgree_mul_le_plainAgree
#print axioms ArkLib.CodingTheory.FoldingTransferNoGo.folding_transfer_no_go
#print axioms ArkLib.CodingTheory.FoldingTransferNoGo.no_go_concrete
