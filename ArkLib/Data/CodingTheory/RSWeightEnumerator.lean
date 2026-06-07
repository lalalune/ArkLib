/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.RSVanishingDim
import Mathlib.FieldTheory.Finiteness

/-!
# Reed–Solomon (MDS) support counts — toward the weight enumerator `A_d`

The MDS weight enumerator of `RS[deg]` is assembled by inclusion–exclusion from the *support
counts*: how many degree-`<deg` codewords vanish on a given coordinate set `S` (equivalently, are
supported on its complement).  Over a finite field, that count is `q^{deg − |S|}` — the cardinality
of the vanishing subspace whose dimension is `deg − |S|` (`finrank_ker_evalOnS`).  This is the
entropy-free combinatorial core feeding the CS25 second-moment bound (#82): the pairwise / weight
distribution `∑_d A_d · …` builds on these counts.
-/

namespace ArkLib.CS25

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]

/-- **MDS support count.**  Over a finite field `F` with `q = |F|`, the number of degree-`<deg`
polynomials vanishing on a coordinate set `S` with `|S| ≤ deg` is `q^{deg − |S|}` — the cardinality
of the vanishing subspace `ker (evalOnS α deg S)`, whose dimension is `deg − |S|`
(`finrank_ker_evalOnS`).  The inclusion–exclusion building block of the RS/MDS weight enumerator. -/
theorem natCard_ker_evalOnS (α : ι ↪ F) (deg : ℕ) (S : Finset ι) (hS : S.card ≤ deg) :
    Nat.card (LinearMap.ker (evalOnS α deg S)) = (Fintype.card F) ^ (deg - S.card) := by
  haveI : FiniteDimensional F (Polynomial.degreeLT F deg) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F deg).toLinearMap
      (Polynomial.degreeLTEquiv F deg).injective
  haveI : Fintype (Polynomial.degreeLT F deg) :=
    Fintype.ofEquiv (Fin deg → F) (Polynomial.degreeLTEquiv F deg).symm.toEquiv
  haveI : Fintype (LinearMap.ker (evalOnS α deg S)) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := F),
    finrank_ker_evalOnS α deg S hS]

end ArkLib.CS25

-- Axiom audit.
#print axioms ArkLib.CS25.natCard_ker_evalOnS
