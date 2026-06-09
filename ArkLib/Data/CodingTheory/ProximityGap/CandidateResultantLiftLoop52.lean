/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Loop 52 (O16 kernel) — the resultant heart of the finite-field lifting: a common root mod `p`
# forces `p ∣ Res_ℤ`, and coprime integer polynomials have nonzero resultant.

Loop51 reduced the finite-field §7 disproof to one input: an injective reduction `ℤ[ζ] → F_p` on the
`2^{2^{m-1}}` subset sums. The obstruction to injectivity at a prime `p` is precisely a **collision**:
two subset sums `f_S(ζ_p) = f_T(ζ_p)`, i.e. the difference `g = f_S − f_T` and `ζ_p` (a primitive
`2^m`-th root, hence a root of `Φ_{2^m}`) share a root mod `p`. This loop proves the two facts that
turn "collision" into "`p` divides a fixed nonzero integer", so that only **finitely many** primes can
collide — the quantitative core of the lifting.

* `prime_dvd_resultant_of_common_root`: if `g, h ∈ ℤ[X]` keep their leading coefficients mod `p` and
  share a root `α ∈ F_p`, then `p ∣ Res_ℤ(g, h)`. Proof: a shared root makes the Bézout identity of
  any coprimality evaluate to `0 = 1`, so `g, h` are *not* coprime over `F_p`, hence
  `Res_{F_p}(ḡ, h̄) = 0` (`resultant_eq_zero_iff`); and `Res_{F_p}(ḡ, h̄) = Res_ℤ(g,h) mod p`
  (`resultant_map_map`), so `p ∣ Res_ℤ(g, h)`.
* `resultant_int_ne_zero_of_isCoprime_rat`: if `g, h` are coprime over `ℚ` (e.g. `Φ_{2^m}` irreducible
  and `deg g < deg Φ`), then `Res_ℤ(g, h) ≠ 0`.

Together: for coprime `g, h` over `ℚ`, `Res_ℤ(g,h)` is a *fixed nonzero integer*, so a common root
mod `p` happens for only finitely many `p` (those dividing it). With Dirichlet (infinitely many
`p ≡ 1 mod 2^m`) this yields a collision-free prime — the existence the Loop51 residual needs. That
final assembly (Dirichlet + primitive-root existence in `ZMod p` + the union over difference pairs) is
the remaining residual; this loop proves its load-bearing arithmetic. See `DISPROOF_LOG.md`
(O16/Loop52).
-/

open Polynomial

namespace ArkLib.ProximityGap.ResultantLiftLoop52

/-- **A common root mod `p` forces `p ∣ Res_ℤ(g, h)`.** If `g, h : ℤ[X]` keep their leading
coefficients nonzero mod the prime `p` (so reduction preserves their degrees) and share a root
`α : ZMod p`, then `p` divides the integer resultant `Res_ℤ(g, h)`. -/
theorem prime_dvd_resultant_of_common_root {p : ℕ} [Fact p.Prime]
    (g h : Polynomial ℤ)
    (hg : (g.leadingCoeff : ZMod p) ≠ 0) (hh : (h.leadingCoeff : ZMod p) ≠ 0)
    {α : ZMod p}
    (hgroot : (g.map (Int.castRingHom (ZMod p))).IsRoot α)
    (hhroot : (h.map (Int.castRingHom (ZMod p))).IsRoot α) :
    (p : ℤ) ∣ Polynomial.resultant g h := by
  set φ : ℤ →+* ZMod p := Int.castRingHom (ZMod p) with hφ
  -- reduction preserves the (formal) degrees, since the leading coefficients survive
  have hlcg : φ g.leadingCoeff ≠ 0 := hg
  have hlch : φ h.leadingCoeff ≠ 0 := hh
  have hdg : (g.map φ).natDegree = g.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hlcg
  have hdh : (h.map φ).natDegree = h.natDegree := natDegree_map_of_leadingCoeff_ne_zero φ hlch
  -- `g.map φ ≠ 0`, since its leading coefficient is nonzero
  have hgne : g.map φ ≠ 0 := by
    intro hz
    apply hlcg
    rw [leadingCoeff, ← coeff_map, hz, coeff_zero]
  -- a common root kills coprimality: the Bézout identity evaluates to `0 = 1`
  have hnc : ¬ IsCoprime (g.map φ) (h.map φ) := by
    rintro ⟨a, b, hab⟩
    have hev := congrArg (Polynomial.eval α) hab
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_mul,
      hgroot.eq_zero, hhroot.eq_zero, mul_zero, mul_zero, add_zero, Polynomial.eval_one] at hev
    exact zero_ne_one hev
  -- hence the resultant over `F_p` vanishes …
  have hres0 : Polynomial.resultant (g.map φ) (h.map φ) = 0 :=
    resultant_eq_zero_iff.mpr ⟨Or.inl hgne, hnc⟩
  -- … and it equals `Res_ℤ(g,h)` reduced mod `p`
  have hmap : Polynomial.resultant (g.map φ) (h.map φ) = φ (Polynomial.resultant g h) := by
    rw [show Polynomial.resultant (g.map φ) (h.map φ)
          = Polynomial.resultant (g.map φ) (h.map φ) g.natDegree h.natDegree by rw [hdg, hdh],
      Polynomial.resultant_map_map]
  rw [hmap] at hres0
  -- `φ x = 0 ↔ (p : ℤ) ∣ x`
  rwa [hφ, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd] at hres0

/-- **Coprime integer polynomials have a nonzero resultant.** If `g, h : ℤ[X]` map to coprime
polynomials over `ℚ`, then `Res_ℤ(g, h) ≠ 0`. (`ℤ ↪ ℚ` is injective, so it preserves the resultant
and reflects nonvanishing.) The intended use: `h = Φ_{2^m}` is irreducible over `ℚ` and `g = f_S − f_T`
has degree `< deg Φ` and is nonzero, so they are coprime over `ℚ`. -/
theorem resultant_int_ne_zero_of_isCoprime_rat (g h : Polynomial ℤ)
    (H : IsCoprime (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))) :
    Polynomial.resultant g h ≠ 0 := by
  have hinj : Function.Injective (Int.castRingHom ℚ) := Int.cast_injective
  intro hz
  -- map the (vanishing) integer resultant to `ℚ`; injectivity ⟹ the `ℚ`-resultant also vanishes
  have hdg : (g.map (Int.castRingHom ℚ)).natDegree = g.natDegree :=
    natDegree_map_eq_of_injective hinj g
  have hdh : (h.map (Int.castRingHom ℚ)).natDegree = h.natDegree :=
    natDegree_map_eq_of_injective hinj h
  have hmap : Polynomial.resultant (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))
      = (Int.castRingHom ℚ) (Polynomial.resultant g h) := by
    rw [show Polynomial.resultant (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))
          = Polynomial.resultant (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ))
              g.natDegree h.natDegree by rw [hdg, hdh],
      Polynomial.resultant_map_map]
  -- but coprimality forces the `ℚ`-resultant nonzero — contradiction
  have hne : Polynomial.resultant (g.map (Int.castRingHom ℚ)) (h.map (Int.castRingHom ℚ)) ≠ 0 :=
    resultant_ne_zero _ _ H
  rw [hmap, hz] at hne
  simp at hne

end ArkLib.ProximityGap.ResultantLiftLoop52

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.ResultantLiftLoop52.prime_dvd_resultant_of_common_root
#print axioms ArkLib.ProximityGap.ResultantLiftLoop52.resultant_int_ne_zero_of_isCoprime_rat
