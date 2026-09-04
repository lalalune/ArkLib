/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Std

/-!
# Production-parameter derivative-chain arithmetic

Ordinary Lean kernel proofs, using only Std. The two final theorems quantify
over every finite list of factor R-degrees whose sum is at most 33. They bound
the corresponding sum of explicitly defined derivative-pair costs, rather
than charging every derivative the same worst-case cost.

These are arithmetic theorems. They do not formalize the polynomial derivative
support bridge, the seed cover, or ProtocolClaim. The mathematical bridge and
the remaining obligations are recorded in
`docs/kb/proximity-astra-derivative-chain-2026-09-04.md`.

The formulas are transcribed from RCN260.UnequalParameters at official companion
commit b34c0131cfa36b51111521541d7d3e35c8791082. In the RCN174 box, the cap L
controls Y+Z, so differentiating R does NOT reduce L.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace AstraCompanionChainBudget

/-- Weighted support gives the sharper Y cap after j R-derivatives. The
polynomial-to-support implication is not part of this core-only theorem. -/
theorem shifted_support_y_cap (x y r j : Nat) (hj : j ≤ 32)
    (h : x + 131071*y + 131070*(r+j) < 20131293) : y ≤ 153-j := by
  omega

theorem shifted_support_r_cap (r j d : Nat) (h : r+j ≤ d) : r ≤ d-j := by
  omega

theorem derivative_y_cap (j : Nat) (hj : j ≤ 32) :
    (20131293-j*131070-1)/131071 = 153-j := by
  omega

/-- Cost of the pair (dR^j F,F), with left caps (153-j,d-j,L)
and right caps (153,d,L). Valid derivative steps have 1 ≤ j < d ≤ 33. -/
def step (L d j : Nat) : Nat :=
  let yl := 153-j
  let rl := d-j
  let ay := 1+2*131071*153
  let ar := 131071*(2*d-1)
  let az := 2*131071*L+1
  let my := rl*L+L*d
  let mr := yl*L+L*153
  let mz := yl*d+rl*153
  (131073*(ay*my+ar*mr+az*mz)+80782*50292*mz)/50292

/-- The complete chain of one factor of R-degree d; omits j=0 and the R-free tail. -/
def chain (L d : Nat) : Nat :=
  ((List.range d).drop 1 |>.map fun j => step L d j).sum

def BoundedSuperadditive (f : Nat → Nat) : Prop :=
  ∀ a b : Fin 34, a.val+b.val ≤ 33 → f a.val+f b.val ≤ f (a.val+b.val)

/-- Superadditive costs combine along any finite degree partition. -/
theorem sum_le_value_sum (f : Nat → Nat) (hf0 : f 0=0)
    (hadd : BoundedSuperadditive f) (ds : List Nat) (hs : ds.sum ≤ 33) :
    (ds.map f).sum ≤ f ds.sum := by
  induction ds with
  | nil => simp [hf0]
  | cons d ds ih =>
    simp only [List.sum_cons] at hs
    have hds : ds.sum ≤ 33 := by omega
    have hd : d < 34 := by omega
    have ht : ds.sum < 34 := by omega
    have hh := hadd ⟨d,hd⟩ ⟨ds.sum,ht⟩ hs
    have hi := ih hds
    simp only [List.map_cons, List.sum_cons]
    exact Nat.le_trans (Nat.add_le_add_left hi _) hh

theorem sum_le_cap (f : Nat → Nat) (hf0 : f 0=0)
    (hadd : BoundedSuperadditive f) (ds : List Nat) (hs : ds.sum ≤ 33) :
    (ds.map f).sum ≤ f 33 := by
  have hsum := sum_le_value_sum f hf0 hadd ds hs
  have ha : ds.sum < 34 := by omega
  have hb : 33-ds.sum < 34 := by omega
  have hc : ds.sum+(33-ds.sum) = 33 := by omega
  have hh := hadd ⟨ds.sum,ha⟩ ⟨33-ds.sum,hb⟩
    (by change ds.sum+(33-ds.sum) ≤ 33; omega)
  change f ds.sum + f (33-ds.sum) ≤ f (ds.sum+(33-ds.sum)) at hh
  rw [hc] at hh
  omega

theorem selected_chain_value : chain 6676 33 = 3504566234932802 := by decide
theorem residual_chain_value : chain 14914 33 = 7829081955871376 := by decide

theorem selected_chain_superadditive : BoundedSuperadditive (chain 6676) := by
  unfold BoundedSuperadditive
  decide

theorem residual_chain_superadditive : BoundedSuperadditive (chain 14914) := by
  unfold BoundedSuperadditive
  decide

/-- Applies to any number of factors, including the empty list and zero degrees. -/
theorem selected_chain_budget (ds : List Nat) (hs : ds.sum ≤ 33) :
    (ds.map (chain 6676)).sum ≤ 3504566234932802 := by
  have h := sum_le_cap (chain 6676) rfl selected_chain_superadditive ds hs
  rw [selected_chain_value] at h
  exact h

theorem residual_chain_budget (ds : List Nat) (hs : ds.sum ≤ 33) :
    (ds.map (chain 14914)).sum ≤ 7829081955871376 := by
  have h := sum_le_cap (chain 14914) rfl residual_chain_superadditive ds hs
  rw [residual_chain_value] at h
  exact h

/-- Two stages can share the same degree budget. In the companion application,
the missing polynomial bridge must provide deg_R H + deg_R Q ≤ 33 from
QB=H*Q, and bound the factor-degree lists by these two degrees. We deliberately
use the larger L=14914 for both lists. -/
theorem shared_chain_budget (fixed residual : List Nat)
    (hs : fixed.sum+residual.sum ≤ 33) :
    (fixed.map (chain 14914)).sum + (residual.map (chain 14914)).sum ≤
      7829081955871376 := by
  have h := residual_chain_budget (fixed++residual) (by simpa using hs)
  simpa only [List.map_append, List.sum_append] using h

#print axioms shifted_support_y_cap
#print axioms derivative_y_cap
#print axioms selected_chain_budget
#print axioms residual_chain_budget
#print axioms shared_chain_budget

end AstraCompanionChainBudget
