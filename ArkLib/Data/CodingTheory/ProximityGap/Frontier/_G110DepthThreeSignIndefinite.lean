/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._G96DepthMomentWeld
import Mathlib.Tactic

/-!
# G110: the genuine depth-three centered anomaly has both signs

G101 rewrites the DC-energy wall as the sum of signed maximal-cancellation-depth anomalies.
G102 and G104 determine the structural signs at depths zero and one, while G107/G109 delimit
guarded depth-two positivity.  Depth three is the first genuinely arithmetic rung.

This file gives exact kernel-checked counterexamples to both possible universal sign claims, using
proper multiplicative subgroups rather than arbitrary finite sets:

* the order-four subgroup `μ₄ = {1,4,13,16} ⊂ ZMod 17` has depth-three anomaly `-420` at `r=3`;
* the order-six subgroup `μ₆ = {1,3,4,9,10,12} ⊂ ZMod 13` has anomaly `+1482`.

Thus neither `A₃ ≥ 0` nor `A₃ ≤ 0` is universally valid even on negation-closed proper
multiplicative subgroups.  Any production proof through G101 must retain genuine arithmetic
information and signed cross-depth accounting from depth three onward.

Issue #466.  Exact finite computation only; no CORE closure claim.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace ArkLib.ProximityGap.Frontier.G110DepthThreeSignIndefinite

open ArkLib.ProximityGap.Frontier.G95CardinalityDeepCapNoGo
open ArkLib.ProximityGap.Frontier.G96DepthMomentWeld

local instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩
local instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩

/-- The exact signed depth contribution, in the G101 normalization. -/
def depthAnomaly
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r s : ℕ) : ℤ :=
  (Fintype.card F : ℤ) * depthFiber G r s - allPairsDepthFiber G r s

/-- The proper order-four multiplicative subgroup of `ZMod 17`. -/
def muFour17 : Finset (ZMod 17) := {1, 4, 13, 16}

/-- The proper order-six multiplicative subgroup of `ZMod 13`. -/
def muSix13 : Finset (ZMod 13) := {1, 3, 4, 9, 10, 12}

set_option maxHeartbeats 0 in
-- `decide` exhaustively evaluates the finite ordered-word pair space.
theorem muFour17_depthFiber_three : depthFiber muFour17 3 3 = 0 := by
  decide

set_option maxHeartbeats 0 in
-- `decide` exhaustively evaluates the finite ordered-word pair space.
theorem muFour17_allPairsDepthFiber_three : allPairsDepthFiber muFour17 3 3 = 420 := by
  decide

/-- Exact negative depth-three anomaly on a proper multiplicative subgroup. -/
theorem muFour17_depthAnomaly_three : depthAnomaly muFour17 3 3 = -420 := by
  rw [depthAnomaly, muFour17_depthFiber_three, muFour17_allPairsDepthFiber_three]
  norm_num

set_option maxHeartbeats 0 in
-- The order-six witness requires checking all `6^6` ordered endpoint pairs.
theorem muSix13_depthFiber_three : depthFiber muSix13 3 3 = 864 := by
  decide

set_option maxHeartbeats 0 in
-- The order-six witness requires checking all `6^6` ordered endpoint pairs.
theorem muSix13_allPairsDepthFiber_three : allPairsDepthFiber muSix13 3 3 = 9750 := by
  decide

/-- Exact positive depth-three anomaly on a proper multiplicative subgroup. -/
theorem muSix13_depthAnomaly_three : depthAnomaly muSix13 3 3 = 1482 := by
  rw [depthAnomaly, muSix13_depthFiber_three, muSix13_allPairsDepthFiber_three]
  norm_num

theorem depthThree_has_negative_subgroup_example :
    depthAnomaly muFour17 3 3 < 0 := by
  rw [muFour17_depthAnomaly_three]
  norm_num

theorem depthThree_has_positive_subgroup_example :
    0 < depthAnomaly muSix13 3 3 := by
  rw [muSix13_depthAnomaly_three]
  norm_num

#print axioms muFour17_depthFiber_three
#print axioms muFour17_allPairsDepthFiber_three
#print axioms muFour17_depthAnomaly_three
#print axioms muSix13_depthFiber_three
#print axioms muSix13_allPairsDepthFiber_three
#print axioms muSix13_depthAnomaly_three
#print axioms depthThree_has_negative_subgroup_example
#print axioms depthThree_has_positive_subgroup_example

end ArkLib.ProximityGap.Frontier.G110DepthThreeSignIndefinite
