import Mathlib.Algebra.Polynomial.Splits
import Mathlib.FieldTheory.Separable

/-!
# Linear-centre certificate legs from slice separability (#301/#302/#304)

At a linear centre curve `H = Y − w` (the only regime where the composed GS-surface
capstones are satisfiable, by F7), the three certificate inputs of
`gammaGenuine_eq_trunc_of_decoded_integerRep` — `hξ` (the `ξ`-nonvanishing), `hbr` (the
cofactor nonvanishing at the decoded witness) and `hxi` — all reduce to **one** fact:
the cofactor's value at the root is a *unit*, which is exactly the Bézout identity of
slice separability evaluated at the root.  These are the generic polynomial-algebra
bricks; the lane welds specialize them at `S := F[Z]`, `w := decoded value`.
-/

open Polynomial

namespace ArkLib.LinearCentreCertificates

variable {S : Type*} [CommRing S]

/-- **The certificate-legs core**: at a linear factor `X − w` of a separable polynomial over
any commutative ring, the cofactor's value at `w` is a **unit** (evaluate the Bézout identity
at `w`; the `A`-term and the `(X − w)·G′` part of the derivative both die). -/
theorem isUnit_cofactor_eval_of_separable_linear_mul {w : S} {G : S[X]}
    (hsep : ((X - C w) * G).Separable) : IsUnit (G.eval w) := by
  obtain ⟨A, B, hAB⟩ := hsep
  have hd : derivative ((X - C w) * G) = G + (X - C w) * derivative G := by
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  have h := congrArg (eval w) hAB
  rw [hd] at h
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, mul_zero,
    add_zero, zero_add, eval_one] at h
  exact isUnit_iff_exists.mpr ⟨eval w B, by rw [mul_comm]; exact h, h⟩

/-- **The `hξ` leg shape**: the derivative of the slice at the root equals the cofactor's
value there — so slice separability makes the derivative-at-root a unit (in particular
nonzero). This is the `ξ ≠ 0` certificate at a linear centre. -/
theorem isUnit_derivative_eval_of_separable_linear_mul {w : S} {G : S[X]}
    (hsep : ((X - C w) * G).Separable) :
    IsUnit ((derivative ((X - C w) * G)).eval w) := by
  have hd : derivative ((X - C w) * G) = G + (X - C w) * derivative G := by
    rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul]
  rw [hd]
  simpa [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self]
    using isUnit_cofactor_eval_of_separable_linear_mul hsep

/-- **Units survive evaluation**: the certificate nonvanishings under any further ring map
(e.g. evaluating the `F[Z]`-level unit at a point of `F`) — a unit's image is a unit, hence
nonzero in a nontrivial ring. This closes the `hbr`/`hxi` shapes from the core brick. -/
theorem map_cofactor_eval_ne_zero_of_separable_linear_mul
    {T : Type*} [CommRing T] [Nontrivial T] (f : S →+* T) {w : S} {G : S[X]}
    (hsep : ((X - C w) * G).Separable) : f (G.eval w) ≠ 0 :=
  ((isUnit_cofactor_eval_of_separable_linear_mul hsep).map f).ne_zero

end ArkLib.LinearCentreCertificates

