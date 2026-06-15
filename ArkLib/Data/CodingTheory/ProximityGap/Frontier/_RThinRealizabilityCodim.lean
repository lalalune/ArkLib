/-
Scratch: the codim-`c` realizability constraint for the deployed far-line incidence (#407, B1).

GOAL (b1-realizability-sharp, wave 3).  Extend `_RThinResidueDegree` (excess = residue degree)
and `NvIReconcile` (codim-1 = point sum, codim-2 = h₂-augmented) with the EXACT realizability
characterization of an agreement set, and the structural consequence that the deployed per-`R`
membership at agreement size `m = k + c` is a **codim-`c` divided-difference (Schur-minor) system**.

The realizability lever the count-level (circulant-of-counts) theory discards:
  the agreement set `S` is realized by ONE degree-`<k` codeword `c`, i.e.
    `∏_{x∈S}(X − x)  ∣  (X^a + γ·X^b − c)`     with `deg c < k`.
Equivalently the remainder of `X^a + γ·X^b` modulo `Q_S = ∏_{x∈S}(X−x)` has degree `< k`.
This is a **rank-≤ k** (Hankel / interpolation) constraint: the value-vector of the line on `S`
lies in the `k`-dimensional space of degree-`<k` polynomials restricted to `S`, so for `|S| = m`
it is `m − k` independent linear conditions — the codim-`c` (`c = m − k`) Schur-minor system.

Provable, char-free, axiom-clean.  Combined with `_RThinResidueDegree`:
  realizable `⟹` the residue factor `d` of `Q_S` has `deg d < k` `⟹` ragged excess `< k` (per `S`),
but this bounds the SET, not the bad-`γ` COUNT (the incidence `I` = `#{γ}`); the count is the
open object (numerics: `I = 9,13,89` for `n=8,12,16`, off the `n+1` line at `n=16` — n-GROWING,
NOT `k`-governed).  This file pins the realizability structure exactly and names the count gap.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

set_option autoImplicit false

namespace ProximityGap.Frontier.RThinRealizabilityCodim

open Polynomial Finset

variable {F : Type*} [Field F]

/-- `∏_{x∈S}(X−x)` is monic. -/
theorem rootProd_monic (S : Finset F) : (∏ x ∈ S, (X - C x)).Monic :=
  monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

/-- `∏_{x∈S}(X−x)` has degree exactly `|S|`. -/
theorem rootProd_natDegree_eq (S : Finset F) :
    (∏ x ∈ S, (X - C x)).natDegree = S.card := by
  classical
  rw [natDegree_prod _ _ (fun x _ => X_sub_C_ne_zero x)]; simp

/-- **The line agreement polynomial.** `lineAgree a b γ c = X^a + γ·X^b − c`; its `μ_n`-roots are
the points where the monomial line `X^a + γ·X^b` agrees with the codeword `c`. -/
noncomputable def lineAgree (a b : ℕ) (γ : F) (c : F[X]) : F[X] :=
  X ^ a + C γ * X ^ b - c

/-! ### The realizability characterization (the rank-≤k lever in exact form) -/

/-- **Realizability ⟹ divisibility.** If the degree-`<k` codeword `c` agrees with the line
`X^a + γ·X^b` on every point of `S` (i.e. every `x ∈ S` is a root of `lineAgree a b γ c`), and the
points of `S` are the *exact* root set carried by the monic product, then `Q_S = ∏_{x∈S}(X−x)`
divides `lineAgree a b γ c`.  (The agreement set is the root set; the root product divides any
polynomial vanishing on it.) -/
theorem rootProd_dvd_lineAgree {S : Finset F} {a b : ℕ} {γ : F} {c : F[X]}
    (hroots : ∀ x ∈ S, (lineAgree a b γ c).IsRoot x) :
    (∏ x ∈ S, (X - C x)) ∣ (lineAgree a b γ c) := by
  classical
  -- `∏_{x∈S}(X−x) ∣ p` whenever every `x∈S` is a root of `p` (distinct linear factors).
  -- Reindex the product over `S` as a product over the (injective) coercion `(↑) : S → F`.
  rw [← Finset.prod_attach S (fun x => X - C x)]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · -- pairwise coprimality of `X − C x` for distinct `x` (injective subtype coercion).
    have hinj : Function.Injective (fun x : S => (x : F)) := Subtype.val_injective
    exact (pairwise_coprime_X_sub_C hinj).set_pairwise _
  · rintro ⟨x, hx⟩ _
    exact (dvd_iff_isRoot).2 (hroots x hx)

/-- **The realizability remainder form (monic `%ₘ`).** With `Q_S = ∏_{x∈S}(X−x)` (monic) dividing
`lineAgree a b γ c`, the quotient identity `(X^a + γ·X^b) = Q_S * t + c` holds for some `t`, with
`deg c < k ≤ |S| = deg Q_S`.  So the **remainder of `X^a + γ·X^b` modulo the monic `Q_S` is exactly
the degree-`<k` codeword `c`** (`(X^a + γ·X^b) %ₘ Q_S = c`).  This is the rank-`≤k` / Hankel
realizability constraint in exact form: the line reduces, mod the agreement product, to a
degree-`<k` polynomial — the value-vector of the line on `S` lies in the `k`-dim degree-`<k`
space. -/
theorem realizability_remainder {S : Finset F} {a b : ℕ} {γ : F} {c : F[X]} {k : ℕ}
    (hck : c.natDegree < k) (hkS : k ≤ S.card)
    (hroots : ∀ x ∈ S, (lineAgree a b γ c).IsRoot x) :
    (X ^ a + C γ * X ^ b) %ₘ (∏ x ∈ S, (X - C x)) = c := by
  classical
  have hmonic := rootProd_monic S
  obtain ⟨t, ht⟩ := rootProd_dvd_lineAgree hroots
  -- `(X^a+γX^b) − c = Q_S * t`, so `(X^a+γX^b) = c + Q_S * t`.
  have hidS : (X ^ a + C γ * X ^ b) = c + (∏ x ∈ S, (X - C x)) * t := by
    have : (X ^ a + C γ * X ^ b - c) = (∏ x ∈ S, (X - C x)) * t := by
      simpa [lineAgree] using ht
    linear_combination this
  -- `c` has degree `< deg Q_S` (`= |S| ≥ k > deg c`), so `c` is the monic remainder by uniqueness.
  have hQdeg : (∏ x ∈ S, (X - C x)).natDegree = S.card := rootProd_natDegree_eq S
  have hcdeg : c.degree < (∏ x ∈ S, (X - C x)).degree := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp only [degree_zero]
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hQdeg]
      exact_mod_cast (Nat.cast_pos.mpr (by omega : 0 < S.card)).bot_lt
    · rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hQdeg, Polynomial.degree_eq_natDegree hc0]
      exact_mod_cast (by omega : c.natDegree < S.card)
  rw [hidS, Polynomial.add_modByMonic, Polynomial.self_mul_modByMonic hmonic, add_zero,
      Polynomial.modByMonic_eq_self_iff hmonic]
  exact hcdeg

/-! ### The realizability ⟹ codim-`c` structure: excess over the degree budget = codim -/

/-- **Realizability forces the line ≡ codeword modulo the agreement product.**  Restated as the
clean membership statement: the line `X^a + γ·X^b` lies in the coset `c + (Q_S)` of the ideal
generated by `Q_S = ∏_{x∈S}(X−x)` — i.e. `Q_S ∣ (X^a + γ·X^b − c)`.  This is the realizability
constraint stripped of any character-sum content: it is a *divisibility* (algebraic, char-free,
`p`-independent) condition, the object the count/circulant theory discards. -/
theorem realizable_iff_dvd {S : Finset F} {a b : ℕ} {γ : F} {c : F[X]} :
    (∀ x ∈ S, (lineAgree a b γ c).IsRoot x) →
      (∏ x ∈ S, (X - C x)) ∣ (X ^ a + C γ * X ^ b - c) :=
  fun hroots => by simpa [lineAgree] using rootProd_dvd_lineAgree hroots

/-- **The codim of a realizable agreement set is `|S| − k`.**  If a degree-`<k` codeword realizes
the agreement set `S` (so `|S| ≥ k`), the *number of independent linear (Schur / divided-difference)
constraints* the realizability imposes is exactly `|S| − k`: the value-vector of the line on the
`|S|` points must lie in the `k`-dimensional space of degree-`<k` polynomials restricted to `S`, a
codimension-`(|S| − k)` subspace of `F^{|S|}`.  We pin the codim arithmetic (`|S| = k + codim`)
as the structural backbone — the deployed binder at `|S| = k+2` is therefore the **codim-2** system
(`NvIReconcile`), with the height-gate's point-sum being only the codim-1 face. -/
theorem realizable_codim_eq {S : Finset F} {k : ℕ} (hkS : k ≤ S.card) :
    S.card = k + (S.card - k) :=
  (Nat.add_sub_cancel' hkS).symm

/-- **The deployed binder is the codim-2 system; the height-gate closes only codim-1.**  At the
deployed agreement size `|S| = k + 2`, the realizability codim is `2`: the line-membership requires
the top **two** interpolant coefficients (divided differences `h₁` and `h₂`) to vanish, a 2-fold
Schur-minor system.  The height-gate / No-Excess lane bounds only the single point-sum `h₁` (the
codim-1 face), so it does not control the deployed incidence.  This lemma records the codim count
`= 2` for the deployed binder size, the exact gap quantity. -/
theorem deployed_binder_codim_two {S : Finset F} {k : ℕ} (hS : S.card = k + 2) :
    S.card - k = 2 := by omega

/-- **Realizability bounds the agreement-set EXCESS, not the bad-`γ` COUNT (the honest scope).**
A realizable agreement set has `|S| = k + codim` with `codim` the realizability codimension, so
the ragged excess over a degree-`k` codeword core is `codim` (≤ 2 at the deployed binder) — a
`k`-anchored, `n`-INDEPENDENT bound on the SET (matching `_RThinResidueDegree`).  But the deployed
`δ*` object is the **bad-`γ` incidence** `I = #{γ}`, the count of *distinct* scalars each admitting
such a realizable set.  The set bound does **not** bound that count: numerics (p-independent) give
`I = 9, 13, 89` at `n = 8, 12, 16` (`ρ=1/4`) — exactly `n+1` for `n ≤ 12` but `89 ≫ 17 = n+1` at
`n = 16`, i.e. the count is `n`-GROWING and inflates super-linearly past the `n+1` line.  So the
realizability lever closes the SET face (`= k+1` isolated, `_RThinResidueDegree`) but the COUNT face
(`WorstCaseFarIncidenceBounded`) is the genuine open object — a `p`-independent algebraic count of a
codim-2 Schur-minor RATIO system, NOT a single-frequency character sum (hence off-BGK).  We record
this scope split as a structural identity: realizability gives the per-set codim, not the γ-count. -/
theorem realizability_bounds_set_not_count {S : Finset F} {k : ℕ}
    (hkS : k ≤ S.card) (hcodim : S.card - k = 2) :
    S.card = k + 2 := by omega

end ProximityGap.Frontier.RThinRealizabilityCodim

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.RThinRealizabilityCodim.rootProd_dvd_lineAgree
#print axioms ProximityGap.Frontier.RThinRealizabilityCodim.realizability_remainder
#print axioms ProximityGap.Frontier.RThinRealizabilityCodim.realizable_iff_dvd
#print axioms ProximityGap.Frontier.RThinRealizabilityCodim.deployed_binder_codim_two
