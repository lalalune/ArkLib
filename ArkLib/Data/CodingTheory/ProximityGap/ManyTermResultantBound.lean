/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SidonLiftAssembly

set_option linter.style.longLine false

/-!
# General-`r` cyclotomic resultant bound: `|Res(Φ_n, manyTerm)| ≤ (2r)^{φ(n)}` (#389)

Generalizes the Sidon (four-term, `r=2`) resultant bound `abs_resultant_le` to the
**`2r`-term** polynomial `manyTerm r a b = ∑_{s<r} (X^{a s} − X^{b s})`, which encodes a candidate
`r`-fold additive relation `∑_s ζ^{a s} = ∑_s ζ^{b s}` in `μ_n`. The bound

  `|Res(cyclotomic n ℤ, manyTerm r a b)| ≤ (2r)^{φ(n)}`

follows from the complex product formula `Res = ∏_{ζ primitive} manyTerm(ζ)` and `|manyTerm(ζ)| ≤ 2r`
on the unit circle (`2r` terms of modulus 1). Combined with the reduction `p ∣ Res` from a mod-`p`
relation (`resultant_map_eq_zero_of_primitiveRoot`), this gives: an `r`-fold additive relation at a
primitive `n`-th root over `F_p` forces `p ≤ (2r)^{φ(n)}`. So for `p > (2r)^{φ(n)}` there is **no**
nontrivial `r`-fold relation beyond the char-0 ones — i.e. the `r`-fold additive energy `E_r(μ_n)`
equals its char-0 (lattice-walk) value. Via the moment ladder `∑_b ‖η_b‖^{2r} = q·E_r(G)`, the
subgroup periods are then *structurally* pinned (exactly sub-Gaussian) for `q > (2r)^{φ(n)}` — a
constructive pin above an explicit field-size bound, with no sum-product / BGK input. (For `n = 2^m`,
`(2r)^{φ(n)} = (2r)^{n/2}`; the bound is met by production `q` only for bounded `r` or small `n` — the
frontier `r ~ n/log n` still exceeds it, consistent with the open core.)

This extends `AdditiveEnergyRepBound.abs_resultant_le` (the `r=2` Sidon case) to all moments.
Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Polynomial Complex

namespace ArkLib.ProximityGap.ManyTermResultant

/-- The `2r`-term polynomial `∑_{s<r} (X^{a s} − X^{b s})` over `ℤ`, encoding the candidate `r`-fold
relation `∑_s ζ^{a s} = ∑_s ζ^{b s}`. -/
noncomputable def manyTerm (r : ℕ) (a b : ℕ → ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range r, (X ^ (a s) - X ^ (b s))

/-- The `2r`-term complex value has norm `≤ 2r` on the unit circle. -/
theorem norm_manyTerm_eval_le {n : ℕ} (hn : n ≠ 0) {ζ : ℂ} (hζ : ζ ^ n = 1)
    (r : ℕ) (a b : ℕ → ℕ) :
    ‖(manyTerm r a b).eval₂ (algebraMap ℤ ℂ) ζ‖ ≤ 2 * r := by
  have hz : ‖ζ‖ = 1 := AdditiveEnergyRepBound.norm_eq_one_of_primitiveRoot hn hζ
  have hzi : ∀ m : ℕ, ‖ζ ^ m‖ = 1 := fun m => by rw [norm_pow, hz, one_pow]
  simp only [manyTerm, eval₂_finset_sum, eval₂_sub, eval₂_pow, eval₂_X]
  calc ‖∑ s ∈ Finset.range r, (ζ ^ (a s) - ζ ^ (b s))‖
      ≤ ∑ s ∈ Finset.range r, ‖ζ ^ (a s) - ζ ^ (b s)‖ := norm_sum_le _ _
    _ ≤ ∑ _s ∈ Finset.range r, (2 : ℝ) := by
        refine Finset.sum_le_sum (fun s _ => ?_)
        calc ‖ζ ^ (a s) - ζ ^ (b s)‖ ≤ ‖ζ ^ (a s)‖ + ‖ζ ^ (b s)‖ := norm_sub_le _ _
          _ = 2 := by rw [hzi, hzi]; norm_num
    _ = 2 * r := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- The integer resultant equals the complex product over primitive roots (general polynomial). -/
theorem resultant_cast_eq_prod_gen {n : ℕ} (f : ℤ[X]) :
    (algebraMap ℤ ℂ) (resultant (cyclotomic n ℤ) f) =
      (((cyclotomic n ℂ).roots).map
        (fun ζ => eval ζ (f.map (algebraMap ℤ ℂ)))).prod := by
  have hinj : Function.Injective (algebraMap ℤ ℂ) := (algebraMap ℤ ℂ).injective_int
  have hsplit : (cyclotomic n ℂ).Splits := by
    simpa using IsAlgClosed.splits_codomain (k := ℂ) (f := RingHom.id ℂ) (cyclotomic n ℂ)
  have hdeg : (f.map (algebraMap ℤ ℂ)).natDegree ≤ f.natDegree :=
    le_of_eq (natDegree_map_eq_of_injective hinj f)
  have hcd : (cyclotomic n ℤ).natDegree = (cyclotomic n ℂ).natDegree := by
    rw [natDegree_cyclotomic, natDegree_cyclotomic]
  have hprod := resultant_eq_prod_eval (cyclotomic n ℂ) (f.map (algebraMap ℤ ℂ)) f.natDegree hdeg hsplit
  rw [(cyclotomic.monic n ℂ).leadingCoeff, one_pow, one_mul] at hprod
  calc (algebraMap ℤ ℂ) (resultant (cyclotomic n ℤ) f)
      = resultant (cyclotomic n ℂ) (f.map (algebraMap ℤ ℂ))
          (cyclotomic n ℤ).natDegree f.natDegree := by
        rw [← map_cyclotomic n (algebraMap ℤ ℂ), resultant_map_map]
    _ = resultant (cyclotomic n ℂ) (f.map (algebraMap ℤ ℂ))
          (cyclotomic n ℂ).natDegree f.natDegree := by rw [hcd]
    _ = _ := hprod

/-- Product of a multiset of reals in `[0, B]` (`0 ≤ B`) is `≤ B^card`. -/
private theorem ms_prod_le_pow_gen {B : ℝ} (hB : 0 ≤ B) {s : Multiset ℝ}
    (hpos : ∀ x ∈ s, 0 ≤ x) (hle : ∀ x ∈ s, x ≤ B) : s.prod ≤ B ^ s.card := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a t ih =>
    simp only [Multiset.prod_cons, Multiset.card_cons, pow_succ]
    have ha : 0 ≤ a := hpos a (Multiset.mem_cons_self a t)
    have haB : a ≤ B := hle a (Multiset.mem_cons_self a t)
    have htpos : 0 ≤ t.prod :=
      Multiset.prod_nonneg (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
    have htih : t.prod ≤ B ^ t.card :=
      ih (fun x hx => hpos x (Multiset.mem_cons_of_mem hx))
        (fun x hx => hle x (Multiset.mem_cons_of_mem hx))
    have hBc : (0:ℝ) ≤ B ^ t.card := pow_nonneg hB t.card
    nlinarith

/-- **`|R| ≤ (2r)^{φ(n)}`.** The integer cyclotomic resultant of the `2r`-term polynomial is bounded
by `(2r)` to the totient — the all-moments generalization of `abs_resultant_le`. -/
theorem abs_resultant_manyTerm_le {n : ℕ} (hn : n ≠ 0) (r : ℕ) (a b : ℕ → ℕ) :
    |resultant (cyclotomic n ℤ) (manyTerm r a b)| ≤ (2 * r) ^ n.totient := by
  set R := resultant (cyclotomic n ℤ) (manyTerm r a b) with hR
  have key : (|R| : ℝ) ≤ ((2 * r : ℕ) : ℝ) ^ n.totient := by
    haveI : NeZero (n : ℂ) := ⟨Nat.cast_ne_zero.mpr hn⟩
    have hcast : ‖(algebraMap ℤ ℂ) R‖ = (|R| : ℝ) := by simp [Complex.norm_intCast]
    rw [← hcast, resultant_cast_eq_prod_gen]
    set g : ℂ → ℂ := fun ζ => eval ζ ((manyTerm r a b).map (algebraMap ℤ ℂ)) with hg
    have hmul : ‖((cyclotomic n ℂ).roots.map g).prod‖
        = ((cyclotomic n ℂ).roots.map (fun ζ => ‖g ζ‖)).prod := by
      have h := map_multiset_prod (normHom : ℂ →*₀ ℝ) ((cyclotomic n ℂ).roots.map g)
      simpa [Multiset.map_map, Function.comp] using h
    rw [hmul]
    have hcard : ((cyclotomic n ℂ).roots).card = n.totient := by
      have hs : (cyclotomic n ℂ).Splits := by
        simpa using IsAlgClosed.splits_codomain (k := ℂ) (f := RingHom.id ℂ) (cyclotomic n ℂ)
      rw [← hs.natDegree_eq_card_roots, natDegree_cyclotomic]
    have hB : (0:ℝ) ≤ ((2 * r : ℕ) : ℝ) := by positivity
    calc ((cyclotomic n ℂ).roots.map (fun ζ => ‖g ζ‖)).prod
        ≤ ((2 * r : ℕ) : ℝ) ^ ((cyclotomic n ℂ).roots.map (fun ζ => ‖g ζ‖)).card := by
          refine ms_prod_le_pow_gen hB (fun x hx => ?_) (fun x hx => ?_)
          · obtain ⟨ζ, _, rfl⟩ := Multiset.mem_map.mp hx; exact norm_nonneg _
          · obtain ⟨ζ, hζ, rfl⟩ := Multiset.mem_map.mp hx
            have hζu : ζ ^ n = 1 := ((isRoot_cyclotomic_iff).mp (isRoot_of_mem_roots hζ)).pow_eq_one
            show ‖eval ζ ((manyTerm r a b).map (algebraMap ℤ ℂ))‖ ≤ ((2 * r : ℕ) : ℝ)
            rw [← eval₂_eq_eval_map]
            have := norm_manyTerm_eval_le hn hζu r a b
            push_cast; push_cast at this; linarith
      _ = ((2 * r : ℕ) : ℝ) ^ n.totient := by rw [Multiset.card_map, hcard]
  exact_mod_cast key

end ArkLib.ProximityGap.ManyTermResultant

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ManyTermResultant.norm_manyTerm_eval_le
#print axioms ArkLib.ProximityGap.ManyTermResultant.abs_resultant_manyTerm_le
