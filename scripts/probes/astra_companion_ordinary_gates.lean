/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Std

/-!
# Retuned ordinary-factor arithmetic for error cell 80781

These universal natural-number identities and characteristic inequalities
support the padded and C2 envelopes used by astra_companion_phases.cpp.
They import only Std and use ordinary kernel proofs. They do not prove the
polynomial, curve, or seed-count theorems that consume these inequalities.

Definitions are transcribed from LocatorFixedStage, LocatorHybridIdentityC2,
and LocatorHybridGatesC2 at official companion commit
b34c0131cfa36b51111521541d7d3e35c8791082. The retuned row has errors 80781,
agreements 181363, gap 50292, and support caps 29 / 135 / 6676.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

namespace AstraCompanionOrdinaryGates

structure Flag where
  z : Nat
  v : Nat
  r : Nat

def mixed (p q f : Flag) : Nat :=
  (q.r*f.r+q.v*f.r+q.r*f.v)*(p.z+p.v+p.r) +
  (q.z*f.r+q.r*f.z)*(p.v+p.r) +
  (q.v*f.v+q.z*f.v+q.v*f.z)*p.r

def tail (a b s d : Nat) : Flag :=
  ⟨2*a*d, 1+2*(b+1)*d, 2*(s+1)*d⟩

def paddedCost (p : Flag) (a b s : Nat) : Nat :=
  mixed p (tail a b s 131072) (tail a b s 131073)

def rational (a b s : Nat) : Flag := ⟨131074*a,131074*b+2,131074*s+3⟩
def fiber (a b s : Nat) : Flag := ⟨a,b+1,s+3⟩
def cut (a b s : Nat) : Flag := ⟨131074*a,131074*b+2+131072,131074*s+3+262144⟩

def hybridCost (p : Flag) (a b s : Nat) : Nat :=
  mixed p (tail a b s 131072) (rational a b s) +
  131076*mixed p (fiber a b s) (cut a b s)

def identityDegree (p : Flag) (a b s : Nat) : Nat :=
  p.z*(393219+262146*s) + p.v*(786438+524292*s) +
  p.r*(1048586+262146*a+524292*b+524292*s)

def paddedSlackZ (b s : Nat) : Nat :=
  6204689135031870+11048600795550156*s+3456066291499008*s*s+
  6912132582998016*b+6912132582998016*b*s

def paddedSlackV (a b s : Nat) : Nat :=
  2041153027974036+8272910057511600*s+3456066291499008*s*s+
  6912132582998016*b+6912132582998016*b*s+
  6912132582998016*a+6912132582998016*a*s

def paddedSlackR (a b s : Nat) : Nat :=
  2721533772399288+8272910057511600*s+3456066291499008*s*s+
  8272910057511600*b+6912132582998016*b*s+3456066291499008*b*b+
  11048600795550156*a+6912132582998016*a*s+6912132582998016*a*b

def paddedSlack (p : Flag) (a b s : Nat) : Nat :=
  p.z*paddedSlackZ b s + p.v*paddedSlackV a b s + p.r*paddedSlackR a b s

def hybridSlackZ (b s : Nat) : Nat :=
  11389414805699490+11913006292353180*s+2592095862137760*s*s+
  6048326951870544*b+5184191724275520*b*s

def hybridSlackV (a b s : Nat) : Nat :=
  7225878698641656+9137315554314624*s+2592095862137760*s*s+
  6048326951870544*b+5184191724275520*b*s+
  6048326951870544*a+5184191724275520*a*s

def hybridSlackR (a b s : Nat) : Nat :=
  5811135424466136+9137315554314624*s+2592095862137760*s*s+
  9137315554314624*b+5184191724275520*b*s+2592095862137760*b*b+
  11913006292353180*a+5184191724275520*a*s+5184191724275520*a*b

def hybridSlack (p : Flag) (a b s : Nat) : Nat :=
  p.z*hybridSlackZ b s + p.v*hybridSlackV a b s + p.r*hybridSlackR a b s

/-- Exact identity with a subtraction-free, hence nonnegative, slack polynomial. -/
theorem padded_identity (p : Flag) (a b s : Nat) :
    50292*paddedCost p a b s =
      131073*80782*identityDegree p a b s + paddedSlack p a b s := by
  simp only [paddedCost, mixed, tail, identityDegree, paddedSlack,
    paddedSlackZ, paddedSlackV, paddedSlackR,
    Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  simp only [Nat.reduceMul]
  simp only [← Nat.mul_assoc]
  omega

/-- The C2 branch uses b>=1; write its support coordinate as b+1 here. -/
theorem hybrid_identity (p : Flag) (a b s : Nat) :
    50292*hybridCost p a (b+1) s =
      131073*80782*identityDegree p a (b+1) s + hybridSlack p a b s := by
  simp only [hybridCost, mixed, tail, rational, fiber, cut, identityDegree,
    hybridSlack, hybridSlackZ, hybridSlackV, hybridSlackR,
    Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.mul_assoc]
  simp only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
  simp only [Nat.reduceMul]
  simp only [← Nat.mul_assoc]
  omega

theorem padded_identity_budget (p : Flag) (a b s : Nat) :
    131073*80782*identityDegree p a b s ≤ 50292*paddedCost p a b s := by
  rw [padded_identity]
  exact Nat.le_add_right _ _

theorem hybrid_identity_budget (p : Flag) (a b s : Nat) (hb : 1 ≤ b) :
    131073*80782*identityDegree p a b s ≤ 50292*hybridCost p a b s := by
  obtain ⟨b', rfl⟩ : ∃ b', b=b'+1 := ⟨b-1,by omega⟩
  rw [hybrid_identity]
  exact Nat.le_add_right _ _

/-- Covers the identity, sharp, and reduced mixed-characteristic gates.
The reduced gate uses k<=56 and the identity gate uses d<=131071, so this
single larger bound suffices for all three. -/
theorem mixed_characteristic (d y k r fY : Nat)
    (hd : d ≤ 131072) (hy : y ≤ 268) (hk : k ≤ 57)
    (hr : r ≤ 29) (hfY : fY ≤ 135) :
    (1+d*y)*r+fY*(k*d) < 2130706433 := by
  have h1 := Nat.mul_le_mul
    (Nat.add_le_add_left (Nat.mul_le_mul hd hy) 1) hr
  have h2 := Nat.mul_le_mul hfY (Nat.mul_le_mul hk hd)
  have h := Nat.add_le_add h1 h2
  exact Nat.lt_of_le_of_lt h (by decide)

theorem product_characteristic (t T : Nat) (ht : t ≤ 6676) (hT : T ≤ 6676) :
    2*t*(T+1) < 2130706433 := by
  have h := Nat.mul_le_mul (Nat.mul_le_mul_left 2 ht) (Nat.add_le_add_right hT 1)
  exact Nat.lt_of_le_of_lt h (by decide)

theorem flag_characteristic (r y t : Nat)
    (hr : r ≤ 29) (hy : y ≤ 135) (ht : t ≤ 6676) :
    r < 2130706433 ∧ y < 2130706433 ∧ t < 2130706433 := by omega

theorem rational_coordinate (b : Nat) (hb : 1 ≤ b) : 80782 ≤ 131074*b+2 := by omega
theorem padded_coordinate (b : Nat) : 80782 ≤ 1+2*(b+1)*131073 := by omega
theorem weighted_cap_characteristic : 131072 ≤ 17773574 ∧ 17773574 < 2130706433 := by decide

#print axioms padded_identity_budget
#print axioms hybrid_identity_budget
#print axioms mixed_characteristic
#print axioms product_characteristic

end AstraCompanionOrdinaryGates
