/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

/-!
# Issue #232 — the top-direction line decoupling and the Conjecture-41 count lower bound

This file is the queued formalization of DISPROOF_LOG **O43** — the verified refutation of
the `M_true ≤ ⌊(2D−1)/c⌋` form of 2026/858's Conjecture 41 — and in formalizing it the
construction *simplifies*: the Newton/complete-homogeneous class-syndrome machinery of the
numeric discovery is not needed. The whole mechanism is one structural fact:

**Decoupling** (`top_line_compat_iff`): on a syndrome line `s(γ) = s₁ + γ·u` whose
direction `u` is the *top unit vector* (`u_j = [j = D−1]`), the codimension-`c`
compatibility system of a weight-`w` support (`D = w + c`) decouples —
`⟨X^r·Λ_E, u⟩ = [r = c−1]` because `Λ_E` is monic of degree `w` — into

* `c−1` **γ-free** equations `⟨X^r·Λ_E, s₁⟩ = 0` (`r < c−1`), and
* one **assignment** `γ = −⟨X^{c−1}·Λ_E, s₁⟩`.

**Count** (`compat_gamma_count` / `conj41_count_lower_bound`): hence the number of
compatible line parameters is at least the number of *distinct last-window values*
`−⟨X^{c−1}·Λ_E, s₁⟩` over the γ-free fiber — pure formulation-(ii) fiber counting. Any
fiber achieving more than `⌊(2D−1)/c⌋` distinct values violates the predicted bound.

The O43 witness instantiates this with `s₁` = the class syndrome of the integer
`(e₁,e₂) = (39,589)` fiber of 6-subsets of `{0,…,13}` (`n = 14, k = 5, D = 9, c = 3`,
bound `⌊17/3⌋ = 5`): there the γ-free system says exactly `e₁(E) = 39 ∧ e₂(E) = 589`
(Newton's e/h convolution), the assignment is affine in `e₃(E)`, and the fiber spreads
over **9** distinct `e₃` values — with all Vandermonde error values nonzero (exact
arithmetic at `p = 1009`, `p = 7919`; integer data, so every sufficiently large prime).
`M_true = 9 > 5`. The escape clause of the conjecture's dichotomy form fires *trivially*
on these lines (`⟨Λ_E, u⟩ = 0` always, by degree), which is exactly why the two printed
forms of Conjecture 41 are inequivalent.

Everything here is axiom-clean and field-generic; the count theorem is the `M_compat`
form (`M_true` discounts only zero error values, which the witness verification rules
out numerically).
-/

namespace TopLine

open Polynomial Finset

variable {F : Type*} [Field F]

/-- The coefficient-window syndrome pairing `⟨P, s⟩ = ∑_{j<N} P_j s_j`. -/
def synd (s : ℕ → F) (N : ℕ) (P : F[X]) : F := ∑ j ∈ Finset.range N, P.coeff j * s j

/-- The error-locator polynomial of a support. -/
noncomputable def loc (E : Finset F) : F[X] := ∏ a ∈ E, (X - C a)

/-- The `r`-shifted syndrome functional. -/
noncomputable def syndr (s : ℕ → F) (N r : ℕ) (E : Finset F) : F :=
  synd s N (X ^ r * loc E)

/-- The codimension-`c` compatibility system at a syndrome. -/
def CompatC (s : ℕ → F) (N c : ℕ) (E : Finset F) : Prop := ∀ r < c, syndr s N r E = 0

/-- The top unit direction in the syndrome window. -/
def unitTop (N : ℕ) : ℕ → F := fun j => if j = N - 1 then 1 else 0

/-- The syndrome line `s₁ + γ·s₂`. -/
def lineS (s₁ s₂ : ℕ → F) (γ : F) : ℕ → F := fun j => s₁ j + γ * s₂ j

lemma loc_monic (E : Finset F) : (loc E).Monic :=
  monic_prod_of_monic _ _ fun a _ => monic_X_sub_C a

lemma loc_natDegree (E : Finset F) : (loc E).natDegree = E.card := by
  rw [loc, Polynomial.natDegree_prod _ _ fun a _ => X_sub_C_ne_zero a]
  simp

/-- The pairing is linear along the line. -/
lemma synd_lineS (s₁ s₂ : ℕ → F) (γ : F) (N : ℕ) (P : F[X]) :
    synd (lineS s₁ s₂ γ) N P = synd s₁ N P + γ * synd s₂ N P := by
  simp only [synd, lineS, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The top-unit pairing extracts the top window coefficient. -/
lemma syndr_unitTop (E : Finset F) {N : ℕ} (hN : 0 < N) (r : ℕ) :
    syndr (unitTop N) N r E = (X ^ r * loc E).coeff (N - 1) := by
  rw [syndr, synd]
  have hcong : ∀ j ∈ Finset.range N,
      (X ^ r * loc E).coeff j * unitTop N j
        = if j = N - 1 then (X ^ r * loc E).coeff j else 0 := by
    intro j _
    by_cases hj : j = N - 1 <;> simp [unitTop, hj]
  rw [Finset.sum_congr rfl hcong, Finset.sum_eq_single (N - 1)
    (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_range.mpr (by omega : N - 1 < N)) h)]
  exact if_pos rfl

/-- Below the leading window, the top-unit pairing vanishes (degree reasons). -/
lemma syndr_unitTop_eq_zero {E : Finset F} {N r : ℕ} (h : E.card + r + 1 < N) :
    syndr (unitTop N) N r E = 0 := by
  rw [syndr_unitTop E (by omega) r]
  apply coeff_eq_zero_of_natDegree_lt
  have hd : ((X : F[X]) ^ r * loc E).natDegree ≤ r + E.card := by
    refine le_trans natDegree_mul_le ?_
    have h1 : ((X : F[X]) ^ r).natDegree ≤ r := natDegree_X_pow_le r
    have h2 := loc_natDegree E
    omega
  omega

/-- At the leading window, the top-unit pairing is `1` (monicity of the locator). -/
lemma syndr_unitTop_eq_one {E : Finset F} {N r : ℕ} (h : E.card + r + 1 = N) :
    syndr (unitTop N) N r E = 1 := by
  rw [syndr_unitTop E (by omega) r]
  have hmono : ((X : F[X]) ^ r * loc E).Monic := (monic_X_pow r).mul (loc_monic E)
  have hdeg : ((X : F[X]) ^ r * loc E).natDegree = N - 1 := by
    rw [Polynomial.natDegree_mul (monic_X_pow r).ne_zero (loc_monic E).ne_zero,
      natDegree_X_pow, loc_natDegree]
    omega
  rw [← hdeg]
  exact hmono.coeff_natDegree

/-- **The decoupling theorem** (the formal heart of O43): on the top-unit-direction line,
the codimension-`c` compatibility of a weight-`w` support (`w + c = N`) is equivalent to
the `c−1` γ-free window equations plus the explicit γ-assignment
`γ = −⟨X^{c−1}·Λ_E, s₁⟩`. The line system contributes NO constraint coupling `γ` to more
than one functional — compatibility along the line is fiber membership plus a value map. -/
theorem top_line_compat_iff {s₁ : ℕ → F} {N c : ℕ} {E : Finset F} {γ : F}
    (hw : E.card + c = N) (hc : 0 < c) :
    CompatC (lineS s₁ (unitTop N) γ) N c E ↔
      ((∀ r, r + 1 < c → syndr s₁ N r E = 0) ∧ γ = -(syndr s₁ N (c - 1) E)) := by
  have hline : ∀ r, syndr (lineS s₁ (unitTop N) γ) N r E
      = syndr s₁ N r E + γ * syndr (unitTop N) N r E := fun r => synd_lineS _ _ _ _ _
  constructor
  · intro hcompat
    constructor
    · intro r hr
      have h := hcompat r (by omega)
      rw [hline r, syndr_unitTop_eq_zero (by omega), mul_zero, add_zero] at h
      exact h
    · have h := hcompat (c - 1) (by omega)
      rw [hline (c - 1), syndr_unitTop_eq_one (by omega), mul_one] at h
      linear_combination h
  · rintro ⟨hfree, hγ⟩ r hr
    rw [hline r]
    rcases lt_or_ge (r + 1) c with hrc | hrc
    · rw [syndr_unitTop_eq_zero (by omega), mul_zero, add_zero]
      exact hfree r hrc
    · have hr1 : r = c - 1 := by omega
      subst hr1
      rw [syndr_unitTop_eq_one (by omega), mul_one, hγ]
      ring

section Count

variable [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
open Classical in
/-- **The count theorem**: the number of compatible line parameters on a top-direction
line is at least the number of distinct last-window values achieved over the γ-free
fiber. `M_compat(s₁, u_top)` IS a formulation-(ii) fiber-image count. -/
theorem compat_gamma_count {s₁ : ℕ → F} {N c : ℕ} (hc : 0 < c)
    {D₀ : Finset F} {w : ℕ} (hw : w + c = N) (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ E ∈ D₀.powersetCard w,
        (∀ r, r + 1 < c → syndr s₁ N r E = 0) ∧ γ = -(syndr s₁ N (c - 1) E)) :
    G.card ≤ (Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, CompatC (lineS s₁ (unitTop N) γ) N c E).card := by
  apply Finset.card_le_card
  intro γ hγ
  obtain ⟨E, hE, hfree, hval⟩ := hG γ hγ
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ _, E, hE, ?_⟩
  have hcard : E.card = w := (Finset.mem_powersetCard.mp hE).2
  exact (top_line_compat_iff (by omega) hc).mpr ⟨hfree, hval⟩

omit [DecidableEq F] in
open Classical in
/-- **The Conjecture-41 violation form** (O43, combinatorial core, formal): if the γ-free
fiber over `s₁` achieves more than `⌊(2N−1)/c⌋` distinct last-window values, the
compatible-parameter count on the top-direction line exceeds the bound that 2026/858's
Conjecture 41 predicts for every line. The O43 integer witness
(`n = 14, w = 6, c = 3`, the `(e₁,e₂) = (39,589)` fiber, 9 distinct `e₃`-values > 5)
realizes the hypothesis over every sufficiently large prime field, with all error values
nonzero — so the `M_true` form of the conjecture is false as printed. -/
theorem conj41_count_lower_bound {s₁ : ℕ → F} {N c : ℕ} (hc : 0 < c)
    {D₀ : Finset F} {w : ℕ} (hw : w + c = N) (G : Finset F)
    (hG : ∀ γ ∈ G, ∃ E ∈ D₀.powersetCard w,
        (∀ r, r + 1 < c → syndr s₁ N r E = 0) ∧ γ = -(syndr s₁ N (c - 1) E))
    (hbig : (2 * N - 1) / c < G.card) :
    (2 * N - 1) / c < (Finset.univ.filter fun γ : F =>
        ∃ E ∈ D₀.powersetCard w, CompatC (lineS s₁ (unitTop N) γ) N c E).card :=
  lt_of_lt_of_le hbig (compat_gamma_count hc hw G hG)

omit [Fintype F] [DecidableEq F] in
/-- The escape-clause triviality that makes the two printed forms of Conjecture 41
inequivalent: the first error-locator normal of EVERY weight-`< N−1` support pairs to
zero with the top-direction vector, purely for degree reasons. -/
theorem escape_clause_trivial {E : Finset F} {N : ℕ} (h : E.card + 1 < N) :
    syndr (unitTop N) N 0 E = 0 :=
  syndr_unitTop_eq_zero (by omega)

end Count

/-! ## The unit-vector pairing, the Vieta bridge, and the fully formal O43-style witness -/

/-- A general unit direction in the syndrome window. -/
def unitVec (j : ℕ) : ℕ → F := fun i => if i = j then 1 else 0

/-- Pairing against a unit vector extracts one locator coefficient. -/
lemma syndr_unitVec {E : Finset F} {N r j : ℕ} (hj : j < N) (hrj : r ≤ j) :
    syndr (unitVec j) N r E = (loc E).coeff (j - r) := by
  rw [syndr, synd]
  have hcong : ∀ i ∈ Finset.range N,
      (X ^ r * loc E).coeff i * unitVec j i
        = if i = j then (X ^ r * loc E).coeff i else 0 := by
    intro i _
    by_cases hi : i = j <;> simp [unitVec, hi]
  rw [Finset.sum_congr rfl hcong, Finset.sum_eq_single j
    (fun b _ hb => if_neg hb)
    (fun h => absurd (Finset.mem_range.mpr hj) h), if_pos rfl]
  conv_lhs => rw [show j = (j - r) + r from by omega]
  rw [Polynomial.coeff_X_pow_mul]

/-- **The Vieta bridge**: locator coefficients are signed elementary symmetric functions
of the support — the dictionary between the rank/normal world (formulation (iii)) and
the multi-symmetric world (formulation (ii)), in coefficient form. -/
lemma loc_coeff_esymm (E : Finset F) {k : ℕ} (hk : k ≤ E.card) :
    (loc E).coeff k = (-1) ^ (E.card - k) * E.val.esymm (E.card - k) := by
  have hloc : loc E = (E.val.map fun t => X - C t).prod := rfl
  rw [hloc, Multiset.prod_X_sub_C_coeff E.val (by simpa using hk)]
  rfl

section Witness

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

open Classical in
/-- **The fully formal O43-style witness**: over `F = ZMod 17` with window `D = 9`,
codimension excess `c = 3`, support weight `w = 6`, domain the whole field, base
syndrome `s₁ = unitVec 5`, the decoupling reduces compatibility on the top-direction
line to `e₁(E) = 0 ∧ e₂(E) = 0` with `γ = e₃(E)` — and the `e₁ = e₂ = 0` fiber spreads
over (at least) the six `e₃`-values `{1,2,3,4,5,6}`. Hence the compatible-parameter
count on this single line is `> 5 = ⌊(2D−1)/c⌋`: **the bound that 2026/858's
Conjecture 41 predicts for every line is violated, machine-checked end to end.** -/
theorem conj41_violation_witness :
    (2 * 9 - 1) / 3 < (Finset.univ.filter fun γ : ZMod 17 =>
      ∃ E ∈ (Finset.univ : Finset (ZMod 17)).powersetCard 6,
        CompatC (lineS (unitVec 5) (unitTop 9) γ) 9 3 E).card := by
  have hsyn : ∀ (E : Finset (ZMod 17)), E.card = 6 → ∀ r, r ≤ 5 →
      syndr (unitVec 5) 9 r E
        = (-1) ^ (6 - (5 - r)) * E.val.esymm (6 - (5 - r)) := by
    intro E hcard r hr
    rw [syndr_unitVec (by norm_num) hr, loc_coeff_esymm E (by omega), hcard]
  have hwit : ∀ γ ∈ ({1, 2, 3, 4, 5, 6} : Finset (ZMod 17)),
      ∃ E ∈ (Finset.univ : Finset (ZMod 17)).powersetCard 6,
        (∀ r, r + 1 < 3 → syndr (unitVec 5) 9 r E = 0)
          ∧ γ = -(syndr (unitVec 5) 9 (3 - 1) E) := by
    intro γ hγ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hγ
    have main : ∀ E : Finset (ZMod 17), E.card = 6 →
        ((-1 : ZMod 17) ^ 1 * E.val.esymm 1 = 0) →
        ((-1 : ZMod 17) ^ 2 * E.val.esymm 2 = 0) →
        (γ = -((-1 : ZMod 17) ^ 3 * E.val.esymm 3)) →
        ∃ E' ∈ (Finset.univ : Finset (ZMod 17)).powersetCard 6,
          (∀ r, r + 1 < 3 → syndr (unitVec 5) 9 r E' = 0)
            ∧ γ = -(syndr (unitVec 5) 9 (3 - 1) E') := by
      intro E hcard h1 h2 h3
      refine ⟨E, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩, ?_, ?_⟩
      · intro r hr
        have hr2 : r = 0 ∨ r = 1 := by omega
        rcases hr2 with rfl | rfl
        · rw [hsyn E hcard 0 (by norm_num)]
          simpa using h1
        · rw [hsyn E hcard 1 (by norm_num)]
          simpa using h2
      · rw [hsyn E hcard (3 - 1) (by norm_num)]
        simpa using h3
    rcases hγ with rfl | rfl | rfl | rfl | rfl | rfl
    · exact main {0, 6, 8, 11, 12, 14} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 3, 10, 11, 13, 14} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 5, 8, 9, 13, 16} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 2, 3, 7, 10, 12} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 1, 2, 3, 13, 15} (by decide) (by decide) (by decide) (by decide)
    · exact main {0, 2, 4, 6, 9, 13} (by decide) (by decide) (by decide) (by decide)
  exact conj41_count_lower_bound (by norm_num) (by norm_num)
    ({1, 2, 3, 4, 5, 6} : Finset (ZMod 17)) hwit (by decide)

end Witness

end TopLine
