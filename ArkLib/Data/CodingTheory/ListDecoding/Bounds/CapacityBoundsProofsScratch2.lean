import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Basic

open scoped BigOperators

variable {F : Type} [LinearOrderedField F]

lemma sum_image_eq
    (points : Finset F)
    (received : F → F)
    (multiplicities : (F × F) → ℕ) :
    (points.image (fun x => (x, received x))).sum (fun p => (multiplicities p + 1) * multiplicities p / 2) =
    points.sum (fun x => (multiplicities (x, received x) + 1) * multiplicities (x, received x) / 2) := by
  rw [Finset.sum_image]
  intro x _ y _ h
  exact Prod.mk.inj h |>.1
