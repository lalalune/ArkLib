/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.Ops

namespace ReedSolomon

variable {F : Type} [Field F] [DecidableEq F]

namespace FftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [FftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D} {x : F}

open CosetFftDomainClass

private lemma subdomain_embed_of_le (i j : ℕ) (h : j ≤ i)
    (k : Fin (2 ^ (n - i))) :
    ∃ (l : Fin (2 ^ (j : ℕ))), subdomain_embed i k = subdomain_embed j l := by
  refine ⟨⟨2 ^ ((j : ℕ) - (i : ℕ)) * k.val, ?_⟩, ?_⟩
  · calc 2 ^ ((j : ℕ) - (i : ℕ)) * k.val < 2 ^ ((j : ℕ) - (i : ℕ)) * 2 ^ (i : ℕ) := by
          apply Nat.mul_lt_mul_of_pos_left k.isLt (by positivity)
        _ = 2 ^ (j : ℕ) := by rw [←pow_add, Nat.sub_add_cancel (by omega)]
  · simp only [subdomain_embed, Fin.ext_iff]
    rw [←mul_assoc, ←pow_add]
    have : n - ↑j + (↑j - ↑i) = n - ↑i := Nat.sub_add_sub_cancel (by omega) (by omega)
    rw [this]


lemma mem_subdomain_of_mem_subdomain_of_le {i j : ℕ}
  (h : x ∈ subdomain ω i)
  (hji : j ≤ i) :
  x ∈ subdomain ω j := by 
  simp_all [subdomain, mkSubgroupUnit, mem_def]
  obtain ⟨i, h⟩ := h

end FftDomainClass

end ReedSolomon
