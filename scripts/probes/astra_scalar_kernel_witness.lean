import Std

/-!
Core-only finite certificate for the explicit F17 differential interpolant.
This checks a closed contact predicate and the complete quadratic list.
It does not formalize the general interpolation, carrier, or MCA theorem.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 10000000

namespace AstraScalarKernelWitness

structure Monomial where
  a : Nat
  i : Nat
  j : Nat
  c : Nat

-- BEGIN_Q_TERMS
def source : List Monomial := [
  ⟨2, 1, 0, 16⟩,
  ⟨3, 1, 0, 6⟩,
  ⟨4, 1, 0, 8⟩,
  ⟨5, 1, 0, 15⟩,
  ⟨6, 1, 0, 5⟩,
  ⟨8, 1, 0, 16⟩,
  ⟨9, 1, 0, 6⟩,
  ⟨10, 1, 0, 9⟩,
  ⟨11, 1, 0, 14⟩,
  ⟨12, 1, 0, 9⟩,
  ⟨13, 1, 0, 11⟩,
  ⟨14, 1, 0, 4⟩,
  ⟨15, 1, 0, 12⟩,
  ⟨16, 1, 0, 12⟩,
  ⟨17, 1, 0, 10⟩,
  ⟨0, 2, 0, 16⟩,
  ⟨1, 2, 0, 2⟩,
  ⟨2, 2, 0, 2⟩,
  ⟨3, 2, 0, 16⟩,
  ⟨4, 2, 0, 6⟩,
  ⟨5, 2, 0, 13⟩,
  ⟨6, 2, 0, 7⟩,
  ⟨8, 2, 0, 7⟩,
  ⟨9, 2, 0, 1⟩,
  ⟨10, 2, 0, 11⟩,
  ⟨11, 2, 0, 13⟩,
  ⟨12, 2, 0, 6⟩,
  ⟨13, 2, 0, 16⟩,
  ⟨14, 2, 0, 2⟩,
  ⟨15, 2, 0, 10⟩,
  ⟨1, 3, 0, 14⟩,
  ⟨2, 3, 0, 6⟩,
  ⟨3, 3, 0, 14⟩,
  ⟨4, 3, 0, 14⟩,
  ⟨5, 3, 0, 4⟩,
  ⟨6, 3, 0, 1⟩,
  ⟨7, 3, 0, 11⟩,
  ⟨8, 3, 0, 1⟩,
  ⟨9, 3, 0, 4⟩,
  ⟨10, 3, 0, 6⟩,
  ⟨11, 3, 0, 10⟩,
  ⟨12, 3, 0, 4⟩,
  ⟨13, 3, 0, 16⟩,
  ⟨0, 4, 0, 8⟩,
  ⟨1, 4, 0, 2⟩,
  ⟨2, 4, 0, 2⟩,
  ⟨3, 4, 0, 2⟩,
  ⟨4, 4, 0, 2⟩,
  ⟨5, 4, 0, 5⟩,
  ⟨6, 4, 0, 6⟩,
  ⟨7, 4, 0, 1⟩,
  ⟨8, 4, 0, 9⟩,
  ⟨9, 4, 0, 11⟩,
  ⟨10, 4, 0, 2⟩,
  ⟨11, 4, 0, 15⟩,
  ⟨0, 5, 0, 10⟩,
  ⟨1, 5, 0, 5⟩,
  ⟨2, 5, 0, 3⟩,
  ⟨3, 5, 0, 1⟩,
  ⟨4, 5, 0, 16⟩,
  ⟨5, 5, 0, 11⟩,
  ⟨6, 5, 0, 13⟩,
  ⟨8, 5, 0, 3⟩,
  ⟨9, 5, 0, 13⟩,
  ⟨0, 6, 0, 4⟩,
  ⟨1, 6, 0, 13⟩,
  ⟨2, 6, 0, 6⟩,
  ⟨3, 6, 0, 6⟩,
  ⟨4, 6, 0, 11⟩,
  ⟨5, 6, 0, 7⟩,
  ⟨6, 6, 0, 4⟩,
  ⟨7, 6, 0, 7⟩,
  ⟨0, 7, 0, 10⟩,
  ⟨1, 7, 0, 14⟩,
  ⟨2, 7, 0, 10⟩,
  ⟨3, 7, 0, 15⟩,
  ⟨4, 7, 0, 10⟩,
  ⟨5, 7, 0, 5⟩,
  ⟨0, 8, 0, 3⟩,
  ⟨1, 8, 0, 13⟩,
  ⟨2, 8, 0, 7⟩,
  ⟨3, 8, 0, 15⟩,
  ⟨0, 9, 0, 13⟩,
  ⟨1, 9, 0, 12⟩,
  ⟨3, 0, 1, 1⟩,
  ⟨4, 0, 1, 16⟩,
  ⟨6, 0, 1, 9⟩,
  ⟨7, 0, 1, 9⟩,
  ⟨8, 0, 1, 13⟩,
  ⟨9, 0, 1, 2⟩,
  ⟨10, 0, 1, 5⟩,
  ⟨11, 0, 1, 3⟩,
  ⟨12, 0, 1, 12⟩,
  ⟨13, 0, 1, 16⟩,
  ⟨14, 0, 1, 2⟩,
  ⟨15, 0, 1, 7⟩,
  ⟨16, 0, 1, 10⟩,
  ⟨17, 0, 1, 11⟩,
  ⟨18, 0, 1, 3⟩,
  ⟨1, 1, 1, 2⟩,
  ⟨2, 1, 1, 16⟩,
  ⟨3, 1, 1, 10⟩,
  ⟨4, 1, 1, 11⟩,
  ⟨5, 1, 1, 14⟩,
  ⟨6, 1, 1, 4⟩,
  ⟨7, 1, 1, 6⟩,
  ⟨8, 1, 1, 11⟩,
  ⟨9, 1, 1, 16⟩,
  ⟨10, 1, 1, 13⟩,
  ⟨11, 1, 1, 14⟩,
  ⟨12, 1, 1, 3⟩,
  ⟨13, 1, 1, 4⟩,
  ⟨14, 1, 1, 16⟩,
  ⟨15, 1, 1, 6⟩,
  ⟨16, 1, 1, 7⟩,
  ⟨1, 2, 1, 6⟩,
  ⟨2, 2, 1, 12⟩,
  ⟨3, 2, 1, 15⟩,
  ⟨4, 2, 1, 9⟩,
  ⟨5, 2, 1, 16⟩,
  ⟨6, 2, 1, 9⟩,
  ⟨7, 2, 1, 9⟩,
  ⟨9, 2, 1, 12⟩,
  ⟨10, 2, 1, 16⟩,
  ⟨11, 2, 1, 6⟩,
  ⟨13, 2, 1, 11⟩,
  ⟨14, 2, 1, 15⟩,
  ⟨0, 3, 1, 5⟩,
  ⟨1, 3, 1, 15⟩,
  ⟨2, 3, 1, 12⟩,
  ⟨4, 3, 1, 8⟩,
  ⟨5, 3, 1, 8⟩,
  ⟨6, 3, 1, 5⟩,
  ⟨8, 3, 1, 5⟩,
  ⟨9, 3, 1, 8⟩,
  ⟨10, 3, 1, 10⟩,
  ⟨11, 3, 1, 14⟩,
  ⟨12, 3, 1, 6⟩,
  ⟨0, 4, 1, 3⟩,
  ⟨2, 4, 1, 14⟩,
  ⟨3, 4, 1, 7⟩,
  ⟨4, 4, 1, 16⟩,
  ⟨5, 4, 1, 8⟩,
  ⟨6, 4, 1, 4⟩,
  ⟨7, 4, 1, 11⟩,
  ⟨8, 4, 1, 2⟩,
  ⟨9, 4, 1, 5⟩,
  ⟨10, 4, 1, 15⟩,
  ⟨0, 5, 1, 5⟩,
  ⟨2, 5, 1, 14⟩,
  ⟨3, 5, 1, 7⟩,
  ⟨4, 5, 1, 5⟩,
  ⟨5, 5, 1, 7⟩,
  ⟨6, 5, 1, 15⟩,
  ⟨7, 5, 1, 9⟩,
  ⟨0, 6, 1, 15⟩,
  ⟨1, 6, 1, 15⟩,
  ⟨2, 6, 1, 14⟩,
  ⟨3, 6, 1, 7⟩,
  ⟨4, 6, 1, 13⟩,
  ⟨5, 6, 1, 4⟩,
  ⟨6, 6, 1, 5⟩,
  ⟨0, 7, 1, 16⟩,
  ⟨1, 7, 1, 7⟩,
  ⟨2, 7, 1, 13⟩,
  ⟨3, 7, 1, 15⟩,
  ⟨0, 8, 1, 14⟩,
  ⟨1, 8, 1, 5⟩,
  ⟨2, 8, 1, 13⟩,
  ⟨0, 9, 1, 14⟩,
  ⟨2, 0, 2, 16⟩,
  ⟨3, 0, 2, 16⟩,
  ⟨4, 0, 2, 4⟩,
  ⟨5, 0, 2, 14⟩,
  ⟨6, 0, 2, 1⟩,
  ⟨7, 0, 2, 2⟩,
  ⟨8, 0, 2, 12⟩,
  ⟨9, 0, 2, 7⟩,
  ⟨10, 0, 2, 11⟩,
  ⟨11, 0, 2, 1⟩,
  ⟨12, 0, 2, 16⟩,
  ⟨13, 0, 2, 7⟩,
  ⟨14, 0, 2, 12⟩,
  ⟨15, 0, 2, 7⟩,
  ⟨16, 0, 2, 2⟩,
  ⟨17, 0, 2, 8⟩,
  ⟨2, 1, 2, 11⟩,
  ⟨3, 1, 2, 8⟩,
  ⟨4, 1, 2, 12⟩,
  ⟨5, 1, 2, 7⟩,
  ⟨6, 1, 2, 9⟩,
  ⟨7, 1, 2, 3⟩,
  ⟨8, 1, 2, 13⟩,
  ⟨9, 1, 2, 13⟩,
  ⟨10, 1, 2, 8⟩,
  ⟨11, 1, 2, 8⟩,
  ⟨12, 1, 2, 6⟩,
  ⟨13, 1, 2, 5⟩,
  ⟨14, 1, 2, 1⟩,
  ⟨15, 1, 2, 15⟩,
  ⟨1, 2, 2, 12⟩,
  ⟨2, 2, 2, 1⟩,
  ⟨3, 2, 2, 16⟩,
  ⟨4, 2, 2, 5⟩,
  ⟨5, 2, 2, 2⟩,
  ⟨6, 2, 2, 16⟩,
  ⟨7, 2, 2, 16⟩,
  ⟨8, 2, 2, 11⟩,
  ⟨9, 2, 2, 14⟩,
  ⟨10, 2, 2, 3⟩,
  ⟨11, 2, 2, 13⟩,
  ⟨12, 2, 2, 12⟩,
  ⟨13, 2, 2, 15⟩,
  ⟨1, 3, 2, 11⟩,
  ⟨2, 3, 2, 6⟩,
  ⟨3, 3, 2, 9⟩,
  ⟨4, 3, 2, 3⟩,
  ⟨5, 3, 2, 12⟩,
  ⟨6, 3, 2, 5⟩,
  ⟨7, 3, 2, 14⟩,
  ⟨8, 3, 2, 13⟩,
  ⟨9, 3, 2, 5⟩,
  ⟨10, 3, 2, 1⟩,
  ⟨11, 3, 2, 6⟩,
  ⟨0, 4, 2, 16⟩,
  ⟨1, 4, 2, 4⟩,
  ⟨2, 4, 2, 3⟩,
  ⟨3, 4, 2, 7⟩,
  ⟨4, 4, 2, 12⟩,
  ⟨5, 4, 2, 9⟩,
  ⟨6, 4, 2, 6⟩,
  ⟨7, 4, 2, 7⟩,
  ⟨8, 4, 2, 10⟩,
  ⟨9, 4, 2, 10⟩,
  ⟨0, 5, 2, 11⟩,
  ⟨2, 5, 2, 13⟩,
  ⟨3, 5, 2, 3⟩,
  ⟨4, 5, 2, 1⟩,
  ⟨5, 5, 2, 15⟩,
  ⟨6, 5, 2, 5⟩,
  ⟨7, 5, 2, 3⟩,
  ⟨0, 6, 2, 16⟩,
  ⟨1, 6, 2, 8⟩,
  ⟨2, 6, 2, 8⟩,
  ⟨3, 6, 2, 7⟩,
  ⟨4, 6, 2, 4⟩,
  ⟨5, 6, 2, 10⟩,
  ⟨0, 7, 2, 9⟩,
  ⟨1, 7, 2, 1⟩
]
-- END_Q_TERMS

def choose (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => if k + 1 ≤ n then choose n k * (n - k) / (k + 1) else 0

def word (x : Nat) : Nat :=
  if x < 5 then 0 else if x < 10 then x * x % 17
  else if x = 10 then 3 else if x = 11 then 7 else 11

/-- Coefficient of t^t z^b R^r in one localized source monomial. -/
def termContribution (node t b r : Nat) (v : Monomial) : Nat :=
  if r < v.j then 0 else
  let c := r - v.j
  if b + c > v.i ∨ c > t then 0 else
  let tx := t - c
  if tx > v.a then 0 else
    (choose v.a tx * node ^ (v.a - tx) * choose v.i b *
      choose (v.i - b) c * (word node) ^ (v.i - b - c)) % 17

def contactCoefficient (node t b r : Nat) : Nat :=
  source.foldl (fun total v => (total + v.c * termContribution node t b r v) % 17) 0

def supportCheck : Bool :=
  (source.foldl (fun total v =>
    if v.a = 1 ∧ v.i = 7 ∧ v.j = 2 then (total + v.c) % 17 else total) 0 == 1) &&
  source.all (fun v => decide (v.a + 2 * v.i + v.j < 20 ∧ v.j ≤ 2 ∧ v.i + v.j ≤ 10))

def nodeContactCheck (node : Nat) : Bool :=
  (List.range 4).all fun t => (List.range 2).all fun b =>
    if t + 2 * b < 4 then
      (List.range 11).all fun r => contactCoefficient node t b r == 0
    else true

def contactCheck : Bool := (List.range 13).all nodeContactCheck

def agreementCount (a b c : Nat) : Nat :=
  ((List.range 13).filter fun x => (a + b * x + c * x * x) % 17 == word x).length

def listed (a b c : Nat) : Bool :=
  (a == 0 && b == 0 && c == 0) ||
  (a == 0 && b == 0 && c == 1) ||
  (a == 7 && b == 15 && c == 12)

def completeListCheck : Bool :=
  (List.range 17).all fun a => (List.range 17).all fun b => (List.range 17).all fun c =>
    decide (5 ≤ agreementCount a b c) == listed a b c

theorem supported_nonzero : supportCheck = true := by decide

theorem all_contacts : contactCheck = true := by decide

theorem complete_quadratic_list : completeListCheck = true := by decide

theorem finite_parameters :
    5 * 5 < 13 * 2 ∧ 2 < 17 ∧ 10 < 17 ∧ 300 - 13 * 23 = 1 := by decide

#print axioms supported_nonzero
#print axioms all_contacts
#print axioms complete_quadratic_list
#print axioms finite_parameters

end AstraScalarKernelWitness
