/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert

import ArkLib.ToMathlib.Finset.Basic
import CompPoly.Fields.Basic

/-!
  # Even and odd parts of polynomial

  The FFT-style splitting of a polynomial `f`
  of the degree `n` into two polynomials
  `fₑ` and `fₒ` of degree `< n/2`  such that `f = fₑ + X fₒ.
-/

section

open Polynomial

variable {F: Type} [NonBinaryField F]

/-- The even part of a polynomial `f`.
  Consists of the even terms of `f`.
-/
noncomputable def fₑ (f : Polynomial F) : Polynomial F :=
    C (2⁻¹ : F) * (f + f.comp (-X))

/-- The odd part of a polynomial `f`.
  Consists of the odd terms of `f` divided by `X`.
-/
noncomputable def fₒ (f : Polynomial F) : Polynomial F :=
    C (2⁻¹ : F) * (f - f.comp (-X)) /ₘ X

section

variable {f : Polynomial F}

lemma fₑ_def :
  fₑ f = C (2⁻¹ : F) * (f + f.comp (-X)) := rfl

@[simp]
lemma fₑ_by_2 :
  2 * (fₑ f) = f + f.comp (-X) := by
  simp [fₑ_def, ext_iff]

lemma fₒ_def :
  fₒ f =
  C (2⁻¹ : F) * (f - f.comp (-X)) /ₘ X
  := rfl

@[simp]
lemma fₒ_by_2 :
    2 * (fₒ f) = (f - f.comp (-X)) /ₘ X
 := by
  simp [fₒ_def, ext_iff]
  by_cases heq : f - f.comp (-X) = 0
  · simp [heq]
  · intro n
    rw [show X = X - C (0 : F) by simp
    , coeff_divByMonic_X_sub_C
    , coeff_divByMonic_X_sub_C
    , Finset.mul_sum]
    apply Finset.sum_bij (fun n _ => n) <;> aesop (add simp natDegree_mul, safe (by field_simp))
end

/-- A polynomial is even if does not contain
  odd terms.
-/
def EvenPoly (f : Polynomial F) : Prop := ∀ n, Odd n → f.coeff n = 0

/-- Given a polynomial `f`, `deevenize` removes
  all the odd terms and substitutes `X² ↦ X`.
-/
noncomputable def deevenize (f : Polynomial F) : Polynomial F :=
    match f with
      | ⟨⟨supp, g, h⟩⟩ => ⟨⟨divide_by_2 supp, fun n => g (2 * n), by
        aesop
      ⟩⟩

@[simp]
lemma deevenize_coeff {f : Polynomial F} {n : ℕ} :
    (deevenize f).coeff n = f.coeff (2 * n) := by aesop (add simp deevenize)

/-- Given a polynomial `f`, `evenize`
  substitutes `X ↦ X²`.
-/
noncomputable def evenize (f : Polynomial F) : Polynomial F :=
  match f with
  | ⟨⟨supp, g, h⟩⟩ => ⟨⟨mul_by_2 supp, fun n => if Even n then g (n / 2) else 0, by
    aesop
  ⟩⟩

@[simp]
lemma evenize_coeff {f : Polynomial F} {n : ℕ} :
    (evenize f).coeff n = if Even n then f.coeff (n / 2) else 0 := by aesop (add simp evenize)

/-- `fₑ` with the substitution `X² ↦ X` applied.
-/
noncomputable def fₑ_x (f : Polynomial F) : Polynomial F := deevenize (fₑ f)
/-- `fₒ` with the substitution `X² ↦ X` applied.
-/
noncomputable def fₒ_x (f : Polynomial F) : Polynomial F := deevenize (fₒ f)

end
