/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Std

/-!
# Soundness of simultaneous source closure by strict slope descent

This combinatorial theorem justifies using the final child envelope in every
source's prefix table. The proof is well founded in raw slope; it does not
assume that the desired bound already holds on the parent. Any finite number
of sources is allowed, including no sources.

The polynomial source-splitting hypotheses and the numerical table obligations
still have to be supplied by a companion proof. This file contains neither
those bridges nor a ProtocolClaim, and no particular phase cap is certified.
The arithmetic C++ evaluator is not a substitute for the table obligations.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace AstraCompanionPhaseClosure

structure Flag where
  r : Nat
  v : Nat
  z : Nat

def Below (a b : Flag) : Prop := a.r ≤ b.r ∧ a.v ≤ b.v ∧ a.z ≤ b.z

theorem below_trans {a b c : Flag} (hab : Below a b) (hbc : Below b c) : Below a c := by
  rcases hab with ⟨hr, hv, hz⟩
  rcases hbc with ⟨hr', hv', hz'⟩
  exact ⟨Nat.le_trans hr hr', Nat.le_trans hv hv', Nat.le_trans hz hz'⟩

def envelope (base : Nat) (candidates : List Nat) : Nat :=
  candidates.foldr min base

theorem le_envelope (value base : Nat) (candidates : List Nat)
    (hbase : value ≤ base) (hcandidates : ∀ c ∈ candidates, value ≤ c) :
    value ≤ envelope base candidates := by
  induction candidates with
  | nil => exact hbase
  | cons c cs ih =>
    have hc : value ≤ c := hcandidates c (by simp)
    have hcs := ih (fun a ha => hcandidates a (by simp [ha]))
    change value ≤ min c (envelope base cs)
    omega

/-- Repeated strict exits reach a nonrouteable child, preserving the additive
charge balance. No bound on the number of factors or sources is assumed. -/
theorem terminal_of_strict_exits {State : Type}
    (flag : State → Flag) (count : State → Nat) (charge : Flag → Nat)
    (route : Flag → Prop) [DecidablePred route]
    (exit : ∀ x, route (flag x) → ∃ y,
      (flag y).r < (flag x).r ∧ Below (flag y) (flag x) ∧
      count x + charge (flag y) ≤ count y + charge (flag x)) :
    ∀ x, route (flag x) → ∃ y,
      (flag y).r < (flag x).r ∧ Below (flag y) (flag x) ∧
      ¬ route (flag y) ∧
      count x + charge (flag y) ≤ count y + charge (flag x) := by
  have descend : ∀ n x, (flag x).r = n → route (flag x) → ∃ y,
      (flag y).r < (flag x).r ∧ Below (flag y) (flag x) ∧
      ¬ route (flag y) ∧
      count x + charge (flag y) ≤ count y + charge (flag x) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hxn hx
      obtain ⟨y, hyr, hyb, hyc⟩ := exit x hx
      by_cases hy : route (flag y)
      · obtain ⟨z, hzr, hzb, hzt, hzc⟩ :=
          ih (flag y).r (by omega) y rfl hy
        exact ⟨z, by omega, below_trans hzb hyb, hzt, by omega⟩
      · exact ⟨y, hyr, hyb, hy, hyc⟩
  intro x hx
  exact descend (flag x).r x rfl hx

/-- A locally checked prefix certificate using the final child cap is sound.
The terminal condition only reads a child of strictly smaller slope, so the
apparent reuse of `cap` is resolved by ordinary natural-number induction.

`exit` is the source's algebraic strict-split obligation. `terminal` is the
numeric prefix-table obligation. Neither is asserted for the prize here. -/
theorem strict_source_closure_sound {State Source : Type}
    (sources : List Source) (flag : State → Flag) (count : State → Nat)
    (base cap : Flag → Nat) (charge defect : Source → Flag → Nat)
    (route : Source → Flag → Prop) [∀ i, DecidablePred (route i)]
    (hbase : ∀ x, count x ≤ base (flag x))
    (exit : ∀ i ∈ sources, ∀ x, route i (flag x) → ∃ y,
      (flag y).r < (flag x).r ∧ Below (flag y) (flag x) ∧
      count x + charge i (flag y) ≤ count y + charge i (flag x))
    (terminal : ∀ i ∈ sources, ∀ child parent,
      child.r < parent.r → Below child parent → ¬ route i child →
      cap child ≤ charge i child + defect i parent)
    (equation : ∀ p, cap p = envelope (base p) (sources.map fun i =>
      if route i p then charge i p + defect i p else base p)) :
    ∀ x, count x ≤ cap (flag x) := by
  have descend : ∀ n x, (flag x).r = n → count x ≤ cap (flag x) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro x hxn
      rw [equation]
      apply le_envelope _ _ _ (hbase x)
      intro c hc
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      by_cases hr : route i (flag x)
      · simp only [if_pos hr]
        obtain ⟨y, hyr, hyb, hyt, hyc⟩ :=
          terminal_of_strict_exits flag count (charge i) (route i) (exit i hi) x hr
        have hybound := ih (flag y).r (by omega) y rfl
        have hterm := terminal i hi (flag y) (flag x) hyr hyb hyt
        omega
      · simpa only [if_neg hr] using hbase x
  intro x
  exact descend (flag x).r x rfl

#print axioms terminal_of_strict_exits
#print axioms strict_source_closure_sound

end AstraCompanionPhaseClosure
