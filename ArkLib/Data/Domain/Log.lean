/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Logic.Embedding.Basic
import Mathlib.Data.Fintype.Defs

namespace Domain

namespace Log

variable {ι F : Type*} [Fintype ι] [DecidableEq F]

/-- Finds a preimage of `x` under the mapping `ω`.
  If one does not exist returns `none`. -/
noncomputable def log (ω : ι ↪ F)
  (x : F) : Option ι := 
  if h : Finset.Nonempty <| (Fintype.elems (α := ι)).filter (fun i ↦ ω i = x) 
  then some <| Classical.choose h 
  else none

/-- Finds a preimage of `x` under the mapping `ω`.
  If one does not exist returns `default`. -/
noncomputable def logD (ω : ι ↪ F)
  (x : F) (default : ι) : ι := Option.getD (log ω x) default 
  
lemma logD_right_of_exists {ω : ι ↪ F} {x : F} {default : ι}
  (h : ∃ i, ω i = x) :
  ω (logD ω x default) = x := by 
  unfold logD log
  split_ifs with h' 
  · have := Classical.choose_spec h'
    aesop
  · obtain ⟨i, h⟩ := h
    have : i ∈ Fintype.elems := Finset.mem_univ i
    aesop
    
@[simp]
lemma logD_left {ω : ι ↪ F} {default i : ι} :
  logD ω (ω i) default = i := by 
  unfold logD log
  split_ifs with h₁
  · have := Classical.choose_spec h₁ 
    aesop
  · have : i ∈ Fintype.elems := Finset.mem_univ i 
    aesop
    
lemma injOn {ω : ι ↪ F} {s : Set F} (hs : ∀ x ∈ s, ∃ i, ω i = x) :
  Set.InjOn (log ω) s := fun x hx y hy h ↦ by
  unfold log at *
  have hx := Classical.choose_spec (hs x hx) 
  have hy := Classical.choose_spec (hs y hy) 
  split_ifs at h with h₁ h₂ h₂ 
  · aesop (add simp [Option.some.injEq]) (add safe (by grind))
  · simp_all only [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff]
    exfalso 
    exact (h₁ (Finset.mem_univ _) ‹_›)

end Log

end Domain
