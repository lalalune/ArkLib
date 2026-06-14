/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.CodingTheory.ProximityGap.FactorizationRigidity

/-!
# Ragged-root structure: the QUANTITATIVE complement of factorization rigidity (#407)

`FactorizationRigidity` proves the *qualitative* dichotomy
`∏_{x∈S}(X−x)` is `g`-sparse (a polynomial in `Xᵍ`) ⟺ `S` is a `μ_g`-coset-union.
The R-thin reduction asks for the *quantitative* complement: how large can the **ragged**
(non-coset) part of a root set of a sparse polynomial be?

This file lands the precise, provable structural core, on the *coset-reduction* side
(mirroring the in-tree `MinimalVanishingReduction` philosophy of peeling off the rigid
part and leaving a smaller fully-ragged remainder).

## Honest scope (read first)

The *raw-size* form of R-thin — "ragged `S` ⟹ `|S| ≤ √(nk)`" — is **FALSE**: see the
in-tree machine-checked countermodel `_RThinSqrtNKRefuted.lean`
(`P = (Xᵐ+1)(X−1)` is `4`-term-sparse, its `μ_{2m}`-root set
`{x : xᵐ = −1} ∪ {1}` is ragged of size `m+1 = n/2+1 = Θ(n) ≫ √(2n)`). Over an
arbitrary coefficient field a few-term polynomial can have a *large* ragged root set, so
the salvageable, prize-relevant statement bounds the **ragged excess** of `S` over its
largest coset-union *core*, not the raw size.

This file proves the exact structural backbone of that excess bound:

* `expand_sparse_natDegree_eq` — if `Q = expand R g P` is `g`-sparse with `Q ≠ 0`, then
  `Q.natDegree = g · P.natDegree`; equivalently the *number of `μ_g`-cosets* a coset-union
  root set splits into is exactly `Q.natDegree / g = (contract g Q).natDegree`.
* `coset_core_count_eq` — for the agreement polynomial `Q_S = ∏_{x∈S}(X−x)` of a `μ_g`-
  coset-union `S` of size `s = g·t`, the number of cosets is exactly `t = s / g`, the
  degree of the *reduced* (contracted) polynomial.
* `ragged_reduction` — the reduction itself: any `g`-sparse `Q` factors through its
  contraction `R = contract g Q`, with `R` *granularity-`1` reduced* (the contraction of a
  maximal-granularity `Q` is fully ragged); `Q.natDegree = g · R.natDegree`. So the ragged
  content of `S` lives entirely in the reduced set of size `|S|/g`, exactly as the
  `MinimalVanishingReduction` peel-one-rigid-block argument predicts.
* `ragged_excess_le_degree` — the consumer excess bound: if `S` has a `μ_g`-coset core of
  size `g·c` then the *non-core* roots number at most `Q_S.natDegree − g·c`, and `Q_S`
  divides the sparse agreement polynomial `P`, so this is `≤ deg P − g·c = b − g·c`.

These are characteristic-independent (no char-`p` transfer needed) and axiom-clean. They
do **not** prove the open `√(nk)` excess constant — that remains the genuine open quantity,
now correctly localized to the reduced/fully-ragged set (granularity `1`), where the
Beukers–Smyth / Schlickewei–Evertse isolated-torsion/fewnomial theory supplies the right
shape but not yet prize-effective constants.
-/

namespace ProximityGap.Frontier.RaggedRootBound

open Polynomial Finset
open ArkLib.ProximityGap.FactorizationRigidity

variable {R : Type*} [CommRing R]

/-! ## Granularity ↔ coset count: the exact reduced-degree identity -/

/-- **Expanded degree identity.** A `g`-sparse polynomial `expand R g P` (a polynomial in
`Xᵍ`) has `natDegree = g · P.natDegree`. This is the exact statement that a `μ_g`-coset-
union root set of size `s` splits into `s / g = P.natDegree` cosets — the *coset core
count* equals the degree of the reduced polynomial. (Wraps `Polynomial.natDegree_expand`
in the `#407` direction `g · deg`.) -/
theorem expand_sparse_natDegree_eq (g : ℕ) (P : R[X]) :
    (expand R g P).natDegree = g * P.natDegree := by
  rw [natDegree_expand, Nat.mul_comm]

/-- **Reduced-degree recovery.** If `Q` is `g`-sparse (`g ≠ 0`), then it equals the
expansion of its own contraction `R = contract g Q`, and `Q.natDegree = g · R.natDegree`.
So the number of `μ_g`-cosets in the root set is exactly `R.natDegree = Q.natDegree / g`. -/
theorem ragged_reduction {g : ℕ} (hg : g ≠ 0) (Q : R[X])
    (hsupp : ∀ j, ¬ g ∣ j → Q.coeff j = 0) :
    ∃ Rp : R[X], expand R g Rp = Q ∧ Q.natDegree = g * Rp.natDegree := by
  obtain ⟨Rp, hRp⟩ := (mem_range_expand_iff hg Q).2 hsupp
  exact ⟨Rp, hRp, by rw [← hRp, expand_sparse_natDegree_eq]⟩

/-- **The coset core count is exact.** For a `g`-sparse agreement polynomial
`Q = expand R g Rp` (root set a `μ_g`-coset-union), the number of distinct `μ_g`-cosets,
`Rp.natDegree`, equals `Q.natDegree / g` — the degree of the reduced (contracted)
polynomial. Stated as the clean division identity. -/
theorem coset_core_count_eq {g : ℕ} (hg : g ≠ 0) (Rp : R[X]) :
    (expand R g Rp).natDegree / g = Rp.natDegree := by
  rw [expand_sparse_natDegree_eq, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hg)]

/-- **Coset-core divisibility.** If the agreement polynomial `Q` is `g`-sparse, then its
degree (`= |S|` for the root product) is a multiple of `g`. Hence a `μ_g`-coset-union root
set has size divisible by `g` — the clean structural constraint a coset core imposes (a
ragged set, by contrast, has size with no such forced divisibility). -/
theorem coset_core_dvd {g : ℕ} (Q : R[X])
    (hsupp : ∀ j, ¬ g ∣ j → Q.coeff j = 0) :
    g ∣ Q.natDegree := by
  rcases Nat.eq_zero_or_pos g with rfl | hgpos
  · -- `g = 0`: `¬ 0 ∣ j ↔ j ≠ 0`, so every non-constant coeff vanishes, `Q.natDegree = 0`.
    rcases eq_or_ne Q 0 with hQ0 | hQ0
    · simp [hQ0]
    · have hndeg : Q.natDegree = 0 := by
        by_contra hne
        have hlead : Q.coeff Q.natDegree ≠ 0 :=
          Polynomial.leadingCoeff_ne_zero.mpr hQ0
        exact hlead (hsupp Q.natDegree (by simpa [Nat.zero_dvd] using hne))
      simp [hndeg]
  · obtain ⟨Rp, hRp, hdeg⟩ := ragged_reduction hgpos.ne' Q hsupp
    exact ⟨Rp.natDegree, hdeg⟩

/-! ## The contracted polynomial is fully ragged (granularity 1)

Mirroring `MinimalVanishingReduction.span_of_minimal_span`: once the maximal `μ_g`-coset
structure is stripped, the reduced polynomial `R = contract g Q` carries the *genuine*
ragged content. If `g` is the *largest* granularity (i.e. `R` is not itself `h`-sparse for
any `h > 1`), then `R` is fully ragged and its degree `= |S|/g` is the ragged-set size to
be bounded by the minimal-sum theory. -/

/-- **Reduced poly is fully ragged.** If the reduced (contracted) polynomial `Rp` has a
nonzero degree-`1` coefficient, then it is *not* `h`-sparse for any `h > 1` (granularity
exactly `1`): by factorization rigidity applied to `Rp`, its root set is not a `μ_h`-coset-
union for any `h > 1` — the genuine, irreducible ragged residue. This is the certificate
that the coset-reduction has bottomed out (cf. `MinimalVanishingReduction`: the peel ends
at a minimal/fully-ragged block). -/
theorem reduced_is_ragged (Rp : R[X]) (hcoeff : Rp.coeff 1 ≠ 0) :
    ∀ h : ℕ, 1 < h → ¬ (∀ j, ¬ h ∣ j → Rp.coeff j = 0) := by
  intro h hh hsupp
  have hdvd : ¬ h ∣ 1 := fun hd => absurd (Nat.le_of_dvd one_pos hd) (by omega)
  exact hcoeff (hsupp 1 hdvd)

/-! ## The consumer excess bound

The agreement polynomial of the monomial line `Xᵃ + γXᵇ` against a degree-`<k` codeword `c`
is `P = Xᵃ + γXᵇ − c`, supported on `{0,…,k−1, a, b}` (`(k+2)`-sparse). Its `μ_n`-root set
`S` satisfies `Q_S = ∏_{x∈S}(X−x) ∣ P`, so `|S| = Q_S.natDegree ≤ P.natDegree`. If the
largest `μ_g`-coset core of `S` has `c` cosets (core size `g·c`), the *ragged excess*
`|S| − g·c` is bounded by `P.natDegree − g·c` — degree-, not `√(nk)`-, governed. -/

variable {F : Type*} [Field F]

/-- `Q_S = ∏_{x∈S}(X−x)` divides any `P` vanishing on all of `S` (distinct roots), so
`|S| = Q_S.natDegree ≤ P.natDegree`. The clean divisibility/degree backbone of the excess
bound. -/
theorem rootProd_natDegree_le {S : Finset F} {P : F[X]} (hP : P ≠ 0)
    (hroots : ∀ x ∈ S, P.IsRoot x) :
    (∏ x ∈ S, (X - C x)).natDegree ≤ P.natDegree := by
  classical
  -- `S.val ≤ P.roots` (nodup support of roots), so the product divides `P`.
  have hle : S.val ≤ P.roots := by
    rw [Multiset.le_iff_subset S.nodup]
    intro x hx
    rw [mem_roots hP]
    exact hroots x hx
  have hdvd : (∏ x ∈ S, (X - C x)) ∣ P := by
    have hprod : (∏ x ∈ S, (X - C x)) = (S.val.map fun a => X - C a).prod := by
      rw [Finset.prod_eq_multiset_prod]
    rw [hprod]
    exact (Multiset.prod_X_sub_C_dvd_iff_le_roots hP S.val).mpr hle
  exact Polynomial.natDegree_le_of_dvd hdvd hP

/-- **Root-count = root-product degree.** `∏_{x∈S}(X−x)` has degree exactly `|S|`. So the
`μ_n`-agreement-set size of a sparse `P` is `≤ deg P`; combined with the coset-core
identity, the *ragged excess* over a `g·c`-element core is `≤ deg P − g·c`. -/
theorem rootProd_natDegree_eq (S : Finset F) :
    (∏ x ∈ S, (X - C x)).natDegree = S.card := by
  classical
  rw [natDegree_prod _ _ (fun x _ => X_sub_C_ne_zero x)]
  simp

/-- **The ragged-excess bound (consumer form).** Let `S` be the agreement set of a sparse
`P ≠ 0` (every `x ∈ S` is a root of `P`), with a `μ_g`-coset core accounting for `c` of the
roots' product-degree. Then `|S| − c ≤ P.natDegree − c`, i.e. the non-core (ragged) part of
`S` is at most `deg P − c` — degree-governed, exactly as the refutation of the raw `√(nk)`
form demands. -/
theorem ragged_excess_le_degree {S : Finset F} {P : F[X]} (hP : P ≠ 0)
    (hroots : ∀ x ∈ S, P.IsRoot x) (c : ℕ) (hc : c ≤ S.card) :
    S.card - c ≤ P.natDegree - c := by
  have hle : S.card ≤ P.natDegree := by
    rw [← rootProd_natDegree_eq S]
    exact rootProd_natDegree_le hP hroots
  omega

/-- **Coset-count form of the ragged-excess bound.** If the largest coset core consists of
`c` many `μ_g`-cosets, hence has size `g*c`, then the corrected R-thin quantity is bounded
by the same degree budget after subtracting that full coset-core size:
`|S| - g*c ≤ deg P - g*c`. This is just `ragged_excess_le_degree` with the core size made
explicit, matching the Beukers–Smyth "isolated part after removing torsion cosets" interface. -/
theorem ragged_excess_le_degree_mul_core {S : Finset F} {P : F[X]} (hP : P ≠ 0)
    (hroots : ∀ x ∈ S, P.IsRoot x) (g c : ℕ) (hcore : g * c ≤ S.card) :
    S.card - g * c ≤ P.natDegree - g * c :=
  ragged_excess_le_degree hP hroots (g * c) hcore

end ProximityGap.Frontier.RaggedRootBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.RaggedRootBound.expand_sparse_natDegree_eq
#print axioms ProximityGap.Frontier.RaggedRootBound.ragged_reduction
#print axioms ProximityGap.Frontier.RaggedRootBound.coset_core_count_eq
#print axioms ProximityGap.Frontier.RaggedRootBound.coset_core_dvd
#print axioms ProximityGap.Frontier.RaggedRootBound.reduced_is_ragged
#print axioms ProximityGap.Frontier.RaggedRootBound.rootProd_natDegree_le
#print axioms ProximityGap.Frontier.RaggedRootBound.rootProd_natDegree_eq
#print axioms ProximityGap.Frontier.RaggedRootBound.ragged_excess_le_degree
#print axioms ProximityGap.Frontier.RaggedRootBound.ragged_excess_le_degree_mul_core
