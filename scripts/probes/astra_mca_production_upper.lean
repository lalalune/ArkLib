/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_production_events
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# A production MCA threshold upper bound from the four-generator construction

The event count is converted into the actual MCA error and threshold ledger.
This is an upper bound only. No matching universal lower bound is proved.
-/

set_option autoImplicit false

noncomputable section

namespace AstraMcaProductionUpper

open Polynomial AstraMcaProductionBasis AstraMcaProductionEvents
open ArkLib.ProximityGap.PrizeShapePrimeP30
open Code ProximityGap ProximityGap.MCAWitnessSpread ProximityGap.MCAThresholdLedger
open scoped NNReal ENNReal

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

/-- The concrete rate-one-half polynomial code on the certified power domain. -/
def productionCode : Set (Fin (2 ^ 30) → ZMod P) :=
  ReedSolomon.code productionEmbedding (2 ^ 29)

/-- Membership exposes the degree-bound and power-evaluation predicate used by the prize ledger. -/
theorem production_code_iff (w : Fin (2 ^ 30) → ZMod P) :
    w ∈ productionCode ↔ ∃ q : Polynomial (ZMod P), q.natDegree ≤ 536870911 ∧
      ∀ i : Fin (2 ^ 30), w i = q.eval (g ^ (i : ℕ)) := by
  constructor
  · rintro ⟨q, hq, heq⟩
    refine ⟨q, ?_, ?_⟩
    · have hdeg := ReedSolomon.natDegree_lt_of_mem_degreeLT hq
      change q.natDegree < 536870912 at hdeg
      omega
    · intro i
      exact (congrFun heq i).symm
  · rintro ⟨q, hq, heq⟩
    refine ⟨q, Polynomial.mem_degreeLT.mpr ?_, ?_⟩
    · apply Polynomial.degree_le_natDegree.trans_lt
      exact_mod_cast Nat.lt_succ_of_le hq
    · funext i
      exact (heq i).symm

/-- The actual MCA error is at least (n+4)/P at the four-deletion radius. -/
theorem production_mca_error_lower :
    (1073741828 : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := ZMod P) productionCode productionRadius := by
  obtain ⟨u0, u1, bad, hcount, hbad⟩ := production_many_events
  let u : WordStack (ZMod P) (Fin 2) (Fin (2 ^ 30)) := fun j => if j = 0 then u0 else u1
  have h := epsMCA_ge_card_div_of_mcaEvent_set (F := ZMod P) productionCode
    productionRadius u bad (fun c hc => by simpa [u, productionCode] using hbad c hc)
  simpa only [hcount, ZMod.card] using h

/-- The constructed MCA error strictly exceeds the 128-bit security budget. -/
theorem production_security_exceeded :
    (1 : ℝ≥0∞) / 2 ^ 128 < epsMCA (F := ZMod P) productionCode productionRadius := by
  apply lt_of_lt_of_le _ production_mca_error_lower
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (ENNReal.div_ne_top (by norm_num) (by norm_num [P]))).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_pow, P]

/-- A fully constructed upper bracket for the actual production MCA threshold. -/
theorem production_delta_star_upper :
    mcaDeltaStar (F := ZMod P) productionCode ((1 : ℝ≥0∞) / 2 ^ 128) ≤
      (357913942 : ℝ≥0) / 1073741824 :=
  mcaDeltaStar_le_of_bad productionCode _ production_security_exceeded

end AstraMcaProductionUpper

#print axioms AstraMcaProductionUpper.production_code_iff
#print axioms AstraMcaProductionUpper.production_mca_error_lower
#print axioms AstraMcaProductionUpper.production_security_exceeded
#print axioms AstraMcaProductionUpper.production_delta_star_upper
