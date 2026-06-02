/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ProximityGap.Folding
import ArkLib.Data.Domain.CosetFftDomain.Subdomain
import ArkLib.Data.Domain.CosetFftDomain.Log
import ArkLib.Data.MvPolynomial.EvenAndOdd
import CompPoly.Data.MvPolynomial.Notation

namespace ProximityGap

open NNReal Finset Function
open scoped ProbabilityTheory
open scoped BigOperators LinearCode
open Code Affine ReedSolomon
open Domain
open CosetFftDomain CosetFftDomainClass
open MvPolynomial LinearMvExtension 

variable {F : Type} [Field F] [DecidableEq F]
variable {n : ℕ}
variable {domain : SmoothCosetFftDomain n F} {f : Word F (Fin (2 ^ n))}
variable {k : ℕ} {x : F}

lemma multilinear_folding [NeZero n] {i : Fin (2 ^ (n - 1))} {α : F}
  {g : F⦃≤ 1⦄[X (Fin n)]}
  (hf : f = evalOnPoints domain (powAlgHom g.1)) :
  foldWord domain f 1 α = 
    evalOnPoints 
      (domain.subdomain 1) 
      (powAlgHom (g.1.aeval 
        (fun i ↦ 
          if h : i = 0 
          then C α 
          else MvPolynomial.X (⟨i.val - 1, by omega⟩ : Fin (n - 1))))) := by 
  rw [even_and_odd_eval]
  simp

end ProximityGap
