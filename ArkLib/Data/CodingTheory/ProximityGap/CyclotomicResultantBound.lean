/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# The archimedean magnitude bound for the small-subgroup Sidon keystone (#389)

The small-subgroup reframing of the proximity prize (`p > 2^n ⟹ μ_n` Sidon over `F_p ⟹
E(μ_n) = 3n(n−1) ⟹ δ*` pinned for `n < log₂ p`) rests on one *archimedean* fact: the
cyclotomic resultant `Res(Φ_n, g)` of the `n`-th cyclotomic polynomial with a 4-term `±1`
"parallelogram" polynomial `g = X^a + X^b − X^c − X^d` has integer magnitude `≤ 4^{φ(n)} = 2^n`
(for `n = 2^m`).  Since `Φ_n` is monic, that resultant is exactly the product of `g` over the
primitive `n`-th roots of unity in `ℂ`, and `|g(ω)| ≤ 4` for every root of unity (triangle
inequality).  This file proves that product bound:

  `‖∏_{ω : Φ_n(ω)=0} g(ω)‖ ≤ 4^{φ(n)}`   (`nnnorm_prod_eval_cyclotomic_roots_le`).

Combined with `Res ≠ 0` (the ℂ-Sidon property of `μ_n`, proven by conjugation) and `p ∣ Res`
(a parallelogram mod `p` is a common root of `Φ_n` and `g`, via `resultant_map_map`), this forces
`p ≤ 4^{φ(n)} = 2^n`, i.e. `p > 2^n ⟹ μ_n` has no nontrivial additive coincidence — the keystone
discharging the no-coincidence hypothesis of `rootsOfUnity_additiveEnergy_eq` in the
small-subgroup regime.  Axiom-clean.
-/


open Polynomial

/-- Submultiplicativity of `nnnorm` over a multiset product in a normed ring. -/
theorem nnnorm_multiset_prod_le_ring {α : Type*} [NormedCommRing α] [NormOneClass α]
    (m : Multiset α) : ‖m.prod‖₊ ≤ (m.map (‖·‖₊)).prod := by
  induction m using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    exact le_trans (nnnorm_mul_le _ _) (mul_le_mul_of_nonneg_left ih (zero_le _))

/-- **The archimedean keystone for the small-subgroup Sidon bound.** For a polynomial `g` over
`ℂ` whose evaluations at all `n`-th roots of unity have norm `≤ 4` (e.g. a 4-term `±1`
"parallelogram" polynomial), the product of `g` over the primitive `n`-th roots — i.e. the
resultant `Res(Φ_n, g)` (the cyclotomic polynomial is monic, so its leading coefficient is `1`) —
has norm `≤ 4^{φ(n)}`.  Combined with `Res ≠ 0` (ℂ-Sidon) and `p ∣ Res` (common root mod `p`),
this yields `p ≤ 4^{φ(n)} = 2^n` for `n = 2^m`, i.e. `p > 2^n ⟹ μ_n` is Sidon over `F_p`. -/
theorem nnnorm_prod_eval_cyclotomic_roots_le (n : ℕ) (g : ℂ[X])
    (hg : ∀ ω : ℂ, ω ^ n = 1 → ‖g.eval ω‖₊ ≤ 4) :
    ‖((cyclotomic n ℂ).roots.map g.eval).prod‖₊ ≤ 4 ^ n.totient := by
  have hcard : (cyclotomic n ℂ).roots.card = n.totient := by
    rw [← (IsAlgClosed.splits (cyclotomic n ℂ)).natDegree_eq_card_roots, natDegree_cyclotomic]
  have hroot : ∀ ω ∈ (cyclotomic n ℂ).roots, ω ^ n = 1 := by
    intro ω hω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [cyclotomic_zero] at hω
    · haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr (by omega)⟩
      exact (isRoot_cyclotomic_iff.mp (isRoot_of_mem_roots hω)).pow_eq_one
  have hb : ∀ x ∈ ((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊), x ≤ 4 := by
    intro x hx
    rw [Multiset.map_map, Multiset.mem_map] at hx
    obtain ⟨ω, hω, rfl⟩ := hx
    exact hg ω (hroot ω hω)
  calc ‖((cyclotomic n ℂ).roots.map g.eval).prod‖₊
      ≤ (((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊)).prod := nnnorm_multiset_prod_le_ring _
    _ ≤ 4 ^ (((cyclotomic n ℂ).roots.map g.eval).map (‖·‖₊)).card :=
        Multiset.prod_le_pow_card _ 4 hb
    _ = 4 ^ n.totient := by rw [Multiset.card_map, Multiset.card_map, hcard]
