import ArkLib.Data.CodingTheory.ListDecoding.Bounds.GKL24
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.BCHKS25
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.CapacityBoundsProofs

open Polynomial MvPolynomial
open scoped BigOperators

namespace CodingTheory.Bounds.Capacity

variable {F : Type} [Field F]

theorem proof_test
    (points : Finset F)
    (f : F → F)
    (received : F → F)
    (multiplicities : (F × F) → ℕ)
    (deg_X deg_Y : ℕ)
    (h_dim : (points.sum (fun x => (multiplicities (x, received x) + 1) * multiplicities (x, received x) / 2)) < (deg_X + 1) * (deg_Y + 1))
    (h_agree : (points.filter (fun x => f x = received x)).sum (fun x => multiplicities (x, received x)) > deg_X + deg_Y * (points.card)) :
    ∃ Q : MvPolynomial (Fin 2) F, Q ≠ 0 ∧
      (∀ x ∈ points, f x = received x → MvPolynomial.eval (fun i => if i = 0 then x else f x) Q = 0) := by
  sorry
