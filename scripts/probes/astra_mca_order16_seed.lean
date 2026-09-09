/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Exact production-field order-sixteen degree-seven seed

The coefficient lists are the normalized seed from
`scripts/probes/astra_mca_order16_certificate.json`. The table is proved by
kernel reduction of finite, closed arithmetic over the actual production
modulus. The polynomial/evaluator bridge connects it to actual polynomials.

The literal root is linked to the production generator by certified iterated
squaring. The file does not lift the table to the billion-point domain or
assert an MCA threshold.

The public declarations below have explicit axiom reports for independent checking.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

namespace AstraMcaOrder16Seed
open Polynomial

/-- The production modulus, identical to `PrizeShapePrimeP30.P`. -/
abbrev P : ℕ := 365375409332725729550921208179070755120141565953

/-- The residue ring of the production modulus. No primality hypothesis is
needed for the finite arithmetic and polynomial degree facts in this file. -/
abbrev F := ZMod P

instance : Fact (1 < P) := ⟨by decide⟩

/-- The exact residue of the production generator raised to `2^26`, as
recorded by the independent certificate. The generator link is separate. -/
def eta : F := 357111556877444407914257742635116754287240874648

/-- The generator certified in `PrizeShapePrimeP30`. -/
def generator : F := 303645430271030343624574566109998498685964493478

/-- Twenty-six iterations suffice for the production root exponent. -/
def repeatedSquare {R : Type*} [Monoid R] : ℕ → R → R
  | 0, a => a
  | n + 1, a => repeatedSquare n (a * a)

/-- Iterated squaring is ordinary exponentiation by a power of two. -/
theorem repeatedSquare_eq_pow {R : Type*} [Monoid R] (n : ℕ) (a : R) :
    repeatedSquare n a = a ^ (2 ^ n) := by
  induction n generalizing a with
  | zero => simp [repeatedSquare]
  | succ n ih =>
    rw [repeatedSquare, ih, ← pow_two, ← pow_mul]
    congr 1
    simp [pow_succ, Nat.mul_comm]

/-- The literal seed root is exactly the certified generator power. -/
theorem eta_eq_generator_pow : eta = generator ^ 67108864 := by
  calc
    eta = repeatedSquare 26 generator := by decide
    _ = generator ^ (2 ^ 26) := repeatedSquare_eq_pow _ _
    _ = generator ^ 67108864 := by norm_num

/-- Low-to-high coefficients of the four explicitly normalized sources. -/
def coefficients : Fin 4 → List F
  | 0 => [0]
  | 1 => [18943363311336672863882327061011457227257409586,
      125829621549097067457234094028236226857884909488,
      346432046021389056687038881118059297892884156367,
      239545787783628662093687114150834528262256656465,
      21013949898147473983537680665153842593321561442,
      365375409332725729550921208179070755120141565952,
      344361459434578255567383527513916912526820004511,
      1]
  | 2 => [19978656604742073423710003863082649910289485513,
      245602515440911398504077651103653490989013237721,
      126864914842502468017061770830307419540916985416,
      119772893891814331046843557075417264131128328233,
      19978656604742073423710003863082649910289485514,
      98758943993666857063305876410263421537806766790,
      364340116039320328991093531376999562437109490025,
      100829530580477658182961230014405806903870918647]
  | 3 => [364340116039320328991093531376999562437109490024,
      245602515440911398504077651103653490989013237720,
      105850964944354994033524090165153576947595423974,
      119772893891814331046843557075417264131128328232,
      1035293293405400559827676802071192683032075928,
      224588565542763924520539970438499648395691676278,
      345396752727983656127211204315988105209852080439,
      226659152129574725640195324042642033761755828135]

/-- Horner realization of a coefficient list as an actual polynomial. -/
noncomputable def horner {R : Type*} [Semiring R] : List R → R[X]
  | [] => 0
  | a :: as => C a + X * horner as

/-- The same Horner operations carried out at a field element. -/
def value {R : Type*} [Semiring R] (x : R) : List R → R
  | [] => 0
  | a :: as => a + x * value x as

/-- The explicit degree-seven source polynomials, including the zero source. -/
noncomputable def seed (i : Fin 4) : F[X] := horner (coefficients i)

/-- A canonical representative for each equality class in the sixteen rows. -/
def classLabel : Fin 16 → Fin 4 → Fin 4
  | 0 => ![0, 0, 0, 3]
  | 1 => ![0, 0, 2, 0]
  | 2 => ![0, 1, 2, 3]
  | 3 => ![0, 1, 0, 0]
  | 4 => ![0, 1, 1, 1]
  | 5 => ![0, 0, 0, 3]
  | 6 => ![0, 0, 2, 3]
  | 7 => ![0, 1, 1, 1]
  | 8 => ![0, 0, 2, 0]
  | 9 => ![0, 0, 2, 0]
  | 10 => ![0, 1, 1, 0]
  | 11 => ![0, 1, 0, 0]
  | 12 => ![0, 1, 0, 0]
  | 13 => ![0, 0, 0, 3]
  | 14 => ![0, 1, 2, 2]
  | _ => ![0, 1, 1, 1]

/-- The polynomial construction and the kernel-computable evaluator coincide. -/
theorem horner_eval {R : Type*} [CommSemiring R] (as : List R) (x : R) :
    (horner as).eval x = value x as := by
  induction as with
  | nil => simp [horner, value]
  | cons a as ih => simp [horner, value, ih]

/-- Exact evaluation interface for the four source polynomials. -/
theorem seed_eval (i : Fin 4) (x : F) :
    (seed i).eval x = value x (coefficients i) := horner_eval _ _

/-- The literal root satisfies the defining order-sixteen cyclotomic equation. -/
theorem eta_pow_eight : eta ^ 8 = -1 := by decide

/-- In particular every displayed domain argument is a sixteenth root. -/
theorem eta_pow_sixteen : eta ^ 16 = 1 := by decide

/-- The sixteen powers used as table rows are pairwise distinct. -/
theorem eta_powers_injective : Function.Injective (fun j : Fin 16 => eta ^ j.val) := by
  decide

/-- Complete equality and inequality table, certified by kernel reduction.
Every source pair is tested, including the diagonal and both orientations. -/
theorem value_table : ∀ (j : Fin 16) (i k : Fin 4),
    (value (eta ^ j.val) (coefficients i) = value (eta ^ j.val) (coefficients k)) ↔
      classLabel j i = classLabel j k := by
  decide

/-- The full partition table for the actual source polynomials. -/
theorem seed_table (j : Fin 16) (i k : Fin 4) :
    (seed i).eval (eta ^ j.val) = (seed k).eval (eta ^ j.val) ↔
      classLabel j i = classLabel j k := by
  simpa only [seed_eval] using value_table j i k

/-- All four values are distinct on the uncovered fiber labelled two. -/
theorem seed_fiber_two_injective : Function.Injective
    (fun i : Fin 4 => (seed i).eval (eta ^ 2)) := by
  intro i k he
  have h := (seed_table 2 i k).mp he
  fin_cases i <;> fin_cases k <;> simp [classLabel] at h ⊢

/-- Distinct sources are distinct actual polynomials. -/
theorem seed_injective : Function.Injective seed := by
  intro i k he
  apply seed_fiber_two_injective
  exact congrArg (fun p : F[X] => p.eval (eta ^ 2)) he

/-- The zero source is exactly zero. -/
@[simp] theorem seed_zero : seed 0 = 0 := by simp [seed, coefficients, horner]

/-- A Horner list of length at most `d+1` has degree at most `d`. -/
theorem horner_natDegree_le {R : Type*} [Semiring R] [Nontrivial R]
    (as : List R) : (horner as).natDegree ≤ as.length - 1 := by
  induction as with
  | nil => simp [horner]
  | cons a as ih =>
    cases as with
    | nil => simp [horner]
    | cons b bs =>
      have hm := Polynomial.natDegree_mul_le (p := (X : R[X]))
        (q := horner (b :: bs))
      have ha := Polynomial.natDegree_add_le (C a) (X * horner (b :: bs))
      simp only [Polynomial.natDegree_X] at hm
      simp only [Polynomial.natDegree_C] at ha
      change (C a + X * horner (b :: bs)).natDegree ≤ (b :: bs).length
      simp only [List.length_cons] at ih ⊢
      omega

/-- The exact seed satisfies the degree-seven hypothesis of the carrier layer. -/
theorem seed_natDegree_le (i : Fin 4) : (seed i).natDegree ≤ 7 := by
  have h := horner_natDegree_le (coefficients i)
  have hlen : (coefficients i).length - 1 ≤ 7 := by fin_cases i <;> decide
  exact h.trans hlen

/-- Each nonzero source has a nonzero seventh coefficient. -/
theorem seed_coeff_seven_ne_zero (i : Fin 4) (hi : i ≠ 0) :
    (seed i).coeff 7 ≠ 0 := by
  fin_cases i
  · exact (hi rfl).elim
  all_goals norm_num [seed, coefficients, horner, Polynomial.coeff_X_mul]
  all_goals decide

/-- All three nonzero source polynomials have degree exactly seven. -/
theorem seed_natDegree (i : Fin 4) (hi : i ≠ 0) : (seed i).natDegree = 7 := by
  exact le_antisymm (seed_natDegree_le i)
    (Polynomial.le_natDegree_of_ne_zero (seed_coeff_seven_ne_zero i hi))

/-- There is no common zero of all four source values at any table row. -/
theorem no_common_zero_on_fibers (j : Fin 16) :
    ¬ (∀ i : Fin 4, (seed i).eval (eta ^ j.val) = 0) := by
  intro hall
  have h1 := (seed_table j 0 1).mp (by simpa using (hall 1).symm)
  have h2 := (seed_table j 0 2).mp (by simpa using (hall 2).symm)
  have h3 := (seed_table j 0 3).mp (by simpa using (hall 3).symm)
  fin_cases j <;> simp_all [classLabel]

#print axioms eta_eq_generator_pow
#print axioms eta_pow_eight
#print axioms eta_powers_injective
#print axioms value_table
#print axioms seed_table
#print axioms seed_injective
#print axioms seed_natDegree_le
#print axioms seed_natDegree
#print axioms no_common_zero_on_fibers

end AstraMcaOrder16Seed
