import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace ArkLib.Data.Polynomial.Multivariate

open MvPolynomial

/-- Represents a grid of points for multivariate interpolation. -/
def Grid (σ : Type*) (F : Type*) [CommRing F] :=
  σ → Finset F

/-- The total number of points in a finite grid. -/
noncomputable def Grid.size {σ : Type*} [Fintype σ] {F : Type*} [CommRing F] (S : Grid σ F) : ℕ :=
  ∏ i : σ, (S i).card

/-- Degree bounding condition: the degree of the polynomial in each variable `i`
is strictly less than the number of points in the grid along dimension `i`.
-/
def satisfies_degree_bound {σ F : Type*} [CommRing F] (S : Grid σ F) (P : MvPolynomial σ F) : Prop :=
  ∀ i : σ, MvPolynomial.degreeOf i P < (S i).card

/--
The interpolation problem: given a grid `S` and a function `f : (σ → F) → F`,
find a polynomial `P` satisfying the degree bound that evaluates to `f` on `S`.
-/
def Interpolates {σ F : Type*} [CommRing F] (S : Grid σ F) (f : (σ → F) → F) (P : MvPolynomial σ F) : Prop :=
  satisfies_degree_bound S P ∧ ∀ x : σ → F, (∀ i, x i ∈ S i) → MvPolynomial.eval x P = f x

/--
The interpolation uniqueness property: if two polynomials satisfying the degree bound
agree on all points in the grid, they must be equal.
-/
def UniquenessProperty {σ F : Type*} [CommRing F] (S : Grid σ F) : Prop :=
  ∀ (P Q : MvPolynomial σ F),
    satisfies_degree_bound S P →
    satisfies_degree_bound S Q →
    (∀ x : σ → F, (∀ i, x i ∈ S i) → MvPolynomial.eval x P = MvPolynomial.eval x Q) →
    P = Q

/--
The existence property: for any function on the grid, there exists an interpolating polynomial.
-/
def ExistenceProperty {σ F : Type*} [CommRing F] (S : Grid σ F) : Prop :=
  ∀ f : (σ → F) → F, ∃ P : MvPolynomial σ F, Interpolates S f P

end ArkLib.Data.Polynomial.Multivariate
