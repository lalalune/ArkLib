/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26DimGeneralSharpPin
import ArkLib.Data.CodingTheory.ProximityGap.KKH26RegimeSplit
import ArkLib.Data.CodingTheory.ProximityGap.InterleavingStabilityLedger

/-!
# The interleaved sharp `δ*` pin (#371)

A one-stone composition that carries the past-the-`√n`-wall sharp pin
(`KKH26DimGeneralSharpPin`) to **row-interleaved** codes `C^{≡t}` — the batched form used by
FRI/STIR-style protocols — with **no interleaving-width factor**, via three already-proven bricks:

* `evalCode_eq_reedSolomon` (`KKH26RegimeSplit`) — the ceiling family is the Reed–Solomon code on
  the power domain;
* `mcaDeltaStar_interleaved_eq` (`InterleavingStabilityLedger`, [Jo26]) — `δ*` is *exactly*
  interleaving-stable (`δ*(C^{≡t}, ε*) = δ*(C, ε*)`, no width factor);
* the sharp pin `deltaStar_dimFour_pin_F4294967377` (`KKH26DimGeneralSharp`).

The result: the dimension-four rung that the swarm's factor-`2` ownership count provably cannot
reach still pins `δ* = 11/16` **after `t`-fold row interleaving**, at the same target error — the
sharp band law is preserved verbatim under batching. New wine in a new skin: no saturated file is
touched.
-/

open Finset
open scoped NNReal ENNReal ProbabilityTheory
open ProximityGap ProximityGap.MCAThresholdLedger ArkLib.ProximityGap.KKH26
open ProximityGap.KKH26DeltaStarReduction Code
open ArkLib.ProximityGap.KKH26DimGeneralSharp ProximityGap.KKH26RegimeSplit

namespace ArkLib.ProximityGap.KKH26DimGeneralSharp

section Concrete4294967377

local instance fact_prime_4294967377' : Fact (Nat.Prime 4294967377) := ⟨by norm_num⟩

/-- **The interleaved sharp `δ*` pin at the dimension-four past-the-wall rung.** For every fold
count `t ≥ 1`, the `t`-fold row interleaving of the degree-`3` Reed–Solomon code on the 16-point
smooth domain `⟨526957872⟩ ⊆ F_p^×` (`p = 2³²+81`) pins

  `δ*(C^{≡t}, 873/p) = 11/16`

— the same in-window value (Johnson `1/2 < 11/16 < 3/4` capacity) the un-interleaved sharp pin
gives, with **no interleaving-width factor** ([Jo26]).  The factor-`2` ownership count cannot reach
this rung even before interleaving (`factor_two_band_empty_mu4_r5`); interleaving preserves the gain
verbatim. -/
theorem deltaStar_dimFour_interleaved_pin_F4294967377 (t : ℕ) [NeZero t] :
    mcaDeltaStar (F := ZMod 4294967377) (A := Fin t → ZMod 4294967377)
        ((ReedSolomon.code (powDomain (526957872 : ZMod 4294967377)
            ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872
            (ne_zero_of_orderOf_eq ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872)) (3 + 1)
          : Set (Fin 16 → ZMod 4294967377)) ^⋈ (Fin t))
        ((((16 : ℕ).choose 5 / 5 : ℕ) : ℝ≥0∞) / (4294967377 : ℝ≥0∞))
      = 1 - (5 : ℝ≥0) / ((2 : ℝ≥0) ^ 4) := by
  haveI : NeZero (16 : ℕ) := ⟨by norm_num⟩
  rw [mcaDeltaStar_interleaved_eq, ← evalCode_eq_reedSolomon (526957872 : ZMod 4294967377)
    ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872
    (ne_zero_of_orderOf_eq ArkLib.ProximityGap.KKH26DimGeneral.orderOf_526957872) 3]
  exact deltaStar_dimFour_pin_F4294967377

end Concrete4294967377

end ArkLib.ProximityGap.KKH26DimGeneralSharp

/-! ## Axiom audit — kernel-clean. -/
#print axioms ArkLib.ProximityGap.KKH26DimGeneralSharp.deltaStar_dimFour_interleaved_pin_F4294967377
