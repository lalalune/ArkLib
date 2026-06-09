/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Group

/-!
# The Trace Map `Tr_H`

For a subgroup `H` of Galois automorphisms, the relative trace is `Tr_H(a) := Σ_{σ ∈ H} σ(a)`.
Hachi [NOZ26, §3] uses `Tr_H` (for `H = ⟨σ_{-1}, σ_{4k+1}⟩`) to express inner products over the
subfield `F_{q^k} ≅ R_q^H` as relations over `R_q` (Theorem 2).

Computably, the trace is the finite sum of the automorphism actions over the exponent set `Hexp`.
It is additive (proven here, from additivity of `galoisAut`). That its image lands in the fixed
subring `R_q^H` and that `Tr_H` restricted there is `(d/k)·id` on the diagonal (Theorem 2) are
deferred.

## Main definitions

* `traceOver Φ S` — `Σ_{i ∈ S} σ_i`, the trace over an arbitrary exponent set.
* `traceH α k` — the trace `Tr_H` over `H = ⟨σ_{-1}, σ_{4k+1}⟩`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
variable (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- The **trace over an exponent set** `S`: `Σ_{i ∈ S} σ_i(a)`.

Noncomputable as stated, since `Finset.sum` routes through `Rq`'s (transported, noncomputable)
`CommRing`. The computable counterpart is `traceOverComp` (equal by `traceOverComp_eq`); the
underlying automorphism action `galoisAut` is itself computable. -/
noncomputable def traceOver (S : Finset ℕ) (a : Rq Φ) : Rq Φ := ∑ i ∈ S, galoisAut Φ i a

@[simp] theorem traceOver_zero (S : Finset ℕ) : traceOver Φ S 0 = 0 := by
  unfold traceOver
  simp only [galoisAut_zero, Finset.sum_const_zero]

/-- The trace is additive. -/
theorem traceOver_add (S : Finset ℕ) (a b : Rq Φ) :
    traceOver Φ S (a + b) = traceOver Φ S a + traceOver Φ S b := by
  unfold traceOver
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => galoisAut_add Φ i a b)

/-- The **computable trace** over an exponent set `S`. The monomial remap is summed at the
`CPolynomial` level — whose ring structure is computable, unlike `Rq`'s transported one — and
reduced once at the end. Equal to `traceOver` (`traceOverComp_eq`). -/
def traceOverComp (S : Finset ℕ) (a : Rq Φ) : Rq Φ :=
  Rq.mk Φ (∑ i ∈ S, ∑ k ∈ Finset.range Φ.φ.natDegree,
    CompPoly.CPolynomial.monomial (k * i) (a.1.coeff k))

/-- The computable trace agrees with `traceOver`. -/
theorem traceOverComp_eq (S : Finset ℕ) (a : Rq Φ) : traceOverComp Φ S a = traceOver Φ S a := by
  rw [traceOverComp, Rq.mk_sum]
  simp only [traceOver, galoisAut]

/-- The **trace map `Tr_H`** for `H = ⟨σ_{-1}, σ_{4k+1}⟩`. -/
noncomputable def traceH (α k : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    Rq (powTwoCyclotomic (R := R) α) :=
  traceOver (powTwoCyclotomic α) (Hexp α k) a

/-- The **computable** trace map `Tr_H`, equal to `traceH` (`traceHComp_eq`). -/
def traceHComp (α k : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    Rq (powTwoCyclotomic (R := R) α) :=
  traceOverComp (powTwoCyclotomic α) (Hexp α k) a

/-- The computable `Tr_H` agrees with `traceH`. -/
theorem traceHComp_eq (α k : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    traceHComp α k a = traceH α k a :=
  traceOverComp_eq _ _ _

/-- **General invariance.** If the exponent automorphism `σ_j` permutes a finite exponent set `S`
(all-odd, with `i ↦ j·i mod 2^{α+1}` injective and self-mapping `S`), then the trace over `S` is
fixed by `σ_j`. This reduces `traceH_mem_fixed` to the pure combinatorics of `Hexp` being closed
under `×4k+1` and `×(−1)` mod `2^{α+1}`. -/
theorem galoisAut_traceOver_eq (α j : ℕ) (hj : Odd j) (S : Finset ℕ)
    (hodd : ∀ i ∈ S, Odd i)
    (hinj : ∀ x ∈ S, ∀ y ∈ S, j * x % 2 ^ (α + 1) = j * y % 2 ^ (α + 1) → x = y)
    (hbij : S.image (fun i => j * i % 2 ^ (α + 1)) = S)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisAut (powTwoCyclotomic α) j (traceOver (powTwoCyclotomic α) S a)
      = traceOver (powTwoCyclotomic α) S a := by
  rw [traceOver, ← galoisRingHom_apply α j hj, map_sum]
  simp only [galoisRingHom_apply]
  rw [Finset.sum_congr rfl (fun i hi => galoisAut_comp α j i hj (hodd i hi) a),
      Finset.sum_congr rfl (fun i hi => galoisAut_periodic α (j * i) (hj.mul (hodd i hi)) a)]
  rw [← Finset.sum_image (f := fun y => galoisAut (powTwoCyclotomic α) y a)
        (g := fun i => j * i % 2 ^ (α + 1)) hinj, hbij]

/-- **`Tr_H` lands in the fixed subring `R_q^H`.** Under the trace-map hypotheses (`k` a power of
two, `2k ∣ 2^α` — the same as `Hexp_card`), `Tr_H` is fixed by both generators `σ_{-1}` and
`σ_{4k+1}` of `H`. Assembled from `galoisAut_traceOver_eq` and the `Hexp` orbit closures
(`Hexp_image_conj`, `Hexp_image_gen`), which rest on the 2-adic order kernel and the Galois-action
periodicity. -/
theorem traceH_mem_fixed (α k : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    conjAut α (traceH α k a) = traceH α k a ∧ genAut α k (traceH α k a) = traceH α k a := by
  obtain ⟨κ, hκeq⟩ := hk2pow
  have hκ : κ + 1 ≤ α := by
    have h2 : (2 : ℕ) ^ (κ + 1) ∣ 2 ^ α := by
      rw [hκeq, show 2 * 2 ^ κ = 2 ^ (κ + 1) from by rw [pow_succ]; ring] at hk; exact hk
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h2
  refine ⟨?_, ?_⟩
  · rw [conjAut, galoisRingHom_apply, traceH]
    exact galoisAut_traceOver_eq α (conjExp α) (conjExp_odd α) (Hexp α k)
      (fun i hi => Hexp_odd α k i hi)
      (fun x hx y hy h => mul_mod_inj α (conjExp α) x y (conjExp_odd α)
        (Hexp_lt α k x hx) (Hexp_lt α k y hy) h)
      (Hexp_image_conj α k) a
  · rw [genAut, galoisRingHom_apply, traceH]
    exact galoisAut_traceOver_eq α (genExp k) (genExp_odd k) (Hexp α k)
      (fun i hi => Hexp_odd α k i hi)
      (fun x hx y hy h => mul_mod_inj α (genExp k) x y (genExp_odd k)
        (Hexp_lt α k x hx) (Hexp_lt α k y hy) h)
      (Hexp_image_gen α k κ hκeq hκ) a

end ArkLib.Lattices.CyclotomicModulus
