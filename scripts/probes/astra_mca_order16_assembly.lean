/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import scripts.probes.astra_mca_order16_seed
import scripts.probes.astra_mca_order16_fibers
import scripts.probes.astra_mca_scaled_polynomials
import scripts.probes.astra_mca_received_assembly
import scripts.probes.astra_mca_production_upper

/-!
# Concrete order-sixteen MCA construction and numerical upper bound

All inputs are the explicit seed, locator, finite blocks, and certified prime.
The final theorem gives the upper bound `313174699 / 1073741824` for the
original MCA threshold on the concrete production rate-one-half code. It
accepts no mathematical residual hypothesis. A matching universal lower
bound, an exact threshold, and other challenge rates remain separate.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable section
namespace AstraMcaOrder16Assembly

open Polynomial AstraMcaProductionBasis AstraMcaProductionEvents
open AstraMcaOrder16Fibers AstraMcaScaledPolynomials AstraMcaReceivedAssembly
open ArkLib.ProximityGap.PrizeShapePrimeP30
open Code ProximityGap ProximityGap.MCAWitnessSpread ProximityGap.MCAThresholdLedger
open scoped NNReal ENNReal

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

abbrev F := ZMod P
abbrev s : ℕ := 6 * productionT + 4
abbrev W := AstraMcaOrder16Seed.seed
abbrev label := AstraMcaOrder16Seed.classLabel

def p (i : Fin 4) : F[X] := scaledP (locator productionCommonRoots) (W i) s
def q (i : Fin 4) : F[X] := scaledQ (locator productionCommonRoots) (W i) s

theorem eta_link : AstraMcaOrder16Seed.eta = g ^ s := by
  simpa only [s, production_size] using AstraMcaOrder16Seed.eta_eq_generator_pow

theorem domain_coordinate (x : F) (hx : x ∈ productionDomain) :
    ∃ (j : Fin 16) (u : Fin s), fiberPoint g s j u = x := by
  have hx' : x ∈ powerDomain g (16 * s) := by
    simpa only [productionDomain, s, production_size,
      show 16 * (2 ^ 26) = 2 ^ 30 by norm_num] using hx
  rw [← powerFiber_cover g s] at hx'
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx'
  obtain ⟨u, hu⟩ := (mem_powerFiber g s j x).mp hj
  exact ⟨j, u, hu⟩

theorem coordinate_pow (j : Fin 16) (u : Fin s) :
    (fiberPoint g s j u) ^ s = AstraMcaOrder16Seed.eta ^ j.val := by
  rw [eta_link]
  exact fiberPoint_pow g s production_fiber_order j u

theorem coordinate_core (i : Fin 4) (j : Fin 16) (u : Fin s) :
    fiberPoint g s j u ∈ productionCore i ↔
      coreStart productionT i j ≤ u.val ∧
        u.val < coreStart productionT i j + coreCount productionT i j :=
  fiberPoint_mem_fiberBlocks_iff g s production_fiber_order _ _
    (core_arithmetic productionT i).1 j u

theorem coordinate_roots (j : Fin 16) (u : Fin s) :
    fiberPoint g s j u ∈ productionCommonRoots ↔ u.val < rootCount productionT j := by
  have hb : ∀ j, 0 + rootCount productionT j ≤ s := by
    intro j
    have h := (allocation_arithmetic productionT).1 j
    dsimp only [s]
    omega
  simpa only [Nat.zero_le, true_and, zero_add] using
    (fiberPoint_mem_fiberBlocks_iff g s production_fiber_order
      (fun _ => 0) (rootCount productionT) hb j u)

/-- All non-root overlaps are within a single certified seed equality class.
The check is 4 x 4 x 16 small interval cases; it never unfolds the large domain. -/
theorem overlapping_labels (t : ℕ) (i k : Fin 4) (j : Fin 16) (u : ℕ)
    (hi : coreStart t i j ≤ u ∧ u < coreStart t i j + coreCount t i j)
    (hk : coreStart t k j ≤ u ∧ u < coreStart t k j + coreCount t k j)
    (hz : ¬ u < rootCount t j) : label j i = label j k := by
  fin_cases i <;> fin_cases k <;> fin_cases j <;>
    simp_all [label, AstraMcaOrder16Seed.classLabel, coreStart, coreCount, rootCount] <;>
    omega

theorem core_overlap (i k : Fin 4) (x : F)
    (hi : x ∈ productionCore i) (hk : x ∈ productionCore k) :
    (p i).eval x = (p k).eval x := by
  by_cases hz : x ∈ productionCommonRoots
  · exact (eval_at_common_root productionCommonRoots (W i) s x hz).1.trans
      (eval_at_common_root productionCommonRoots (W k) s x hz).1.symm
  · obtain ⟨j, u, rfl⟩ := domain_coordinate x (production_core_subset_domain i hi)
    have he := overlapping_labels productionT i k j u.val
      ((coordinate_core i j u).mp hi) ((coordinate_core k j u).mp hk)
      (fun h => hz ((coordinate_roots j u).mpr h))
    apply (scaledP_eval_eq_iff (locator productionCommonRoots) (W i) (W k) s _
      ((locator_eval_ne_zero_iff _ _).mpr hz)).mpr
    rw [coordinate_pow]
    exact (AstraMcaOrder16Seed.seed_table j i k).mpr he

/-- Select an existing core owner whenever one exists. This finite choice
constructs one shared received base, rather than assuming a compatible base. -/
def owner (x : F) : Fin 4 :=
  if h : ∃ i, x ∈ productionCore i then Classical.choose h else 0

theorem owner_mem (x : F) (h : ∃ i, x ∈ productionCore i) :
    x ∈ productionCore (owner x) := by
  simp only [owner, dif_pos h]
  exact Classical.choose_spec h

def base (x : F) : F × F := ((p (owner x)).eval x, x * (p (owner x)).eval x)

theorem core_base (i : Fin 4) (x : F) (hx : x ∈ productionCore i) :
    (p i).eval x = (base x).1 ∧ (q i).eval x = (base x).2 := by
  have he := core_overlap i (owner x) x hx (owner_mem x ⟨i, hx⟩)
  constructor
  · exact he
  · simpa only [q, scaledQ_eval, base, p] using congrArg (x * ·) he

theorem covered_domain (x : F) (hx : x ∈ productionCovered) : x ∈ productionDomain := by
  simpa only [productionCovered, productionDomain, s, production_size,
    show 16 * (2 ^ 26) = 2 ^ 30 by norm_num] using
      covered_subset_domain g productionT hx

theorem uncovered_domain (x : F) (hx : x ∈ productionUncovered) : x ∈ productionDomain := by
  simpa only [productionUncovered, productionDomain, s, production_size,
    show 16 * (2 ^ 26) = 2 ^ 30 by norm_num] using
      uncovered_subset_domain g productionT hx

theorem covered_not_root (x : F) (hx : x ∈ productionCovered) :
    x ∉ productionCommonRoots := by
  intro hz
  exact Finset.disjoint_left.mp production_allocation_disjoint.1 hz hx

theorem uncovered_not_root (x : F) (hx : x ∈ productionUncovered) :
    x ∉ productionCommonRoots := by
  intro hz
  exact Finset.disjoint_left.mp production_allocation_disjoint.2.1 hz hx

theorem covered_nonzero (x : F) (hx : x ∈ productionCovered) : x ≠ 0 := by
  have hpow := power_domain_roots g (2 ^ 30) orderOf_g x (covered_domain x hx)
  intro hz
  subst x
  norm_num at hpow

/-- On every covered point some source differs from the chosen base.
This uses the full seed table, without requiring a separately chosen nonowner. -/
theorem covered_nonowner (x : F) (hx : x ∈ productionCovered) :
    ∃ i, (p i).eval x ≠ (base x).1 := by
  by_contra h
  push Not at h
  have hz := covered_not_root x hx
  have hB := (locator_eval_ne_zero_iff productionCommonRoots x).mpr hz
  obtain ⟨j, u, hxu⟩ := domain_coordinate x (covered_domain x hx)
  have hpow : x ^ s = AstraMcaOrder16Seed.eta ^ j.val := by
    rw [← hxu]
    exact coordinate_pow j u
  apply AstraMcaOrder16Seed.no_common_zero_on_fibers j
  intro i
  have he := (scaledP_eval_eq_iff (locator productionCommonRoots) (W i) (W 0) s x hB).mp
    ((h i).trans (h 0).symm)
  simpa only [hpow, W, AstraMcaOrder16Seed.seed_zero, eval_zero] using he

theorem uncovered_pow (x : F) (hx : x ∈ productionUncovered) :
    x ^ s = AstraMcaOrder16Seed.eta ^ 2 := by
  obtain ⟨j, u, rfl⟩ := domain_coordinate x (uncovered_domain x hx)
  have hb : ∀ j, rootCount productionT j + coveredCount productionT j +
      uncoveredCount productionT j ≤ s := fun j => ((allocation_arithmetic productionT).1 j).le
  have hu := (fiberPoint_mem_fiberBlocks_iff g s production_fiber_order
    (fun j => rootCount productionT j + coveredCount productionT j)
    (uncoveredCount productionT) hb j u).mp hx
  have hj : j = 2 := by
    by_contra hj
    simp only [uncoveredCount, if_neg hj, add_zero] at hu
    omega
  subst j
  exact coordinate_pow 2 u

theorem uncovered_injective (x : F) (hx : x ∈ productionUncovered) :
    Function.Injective (fun i : Fin 4 => (p i).eval x) := by
  intro i k he
  apply AstraMcaOrder16Seed.seed_fiber_two_injective
  have hB := (locator_eval_ne_zero_iff productionCommonRoots x).mpr (uncovered_not_root x hx)
  have h := (scaledP_eval_eq_iff (locator productionCommonRoots) (W i) (W k) s x hB).mp he
  simpa only [uncovered_pow x hx] using h

theorem degree_budget (i : Fin 4) :
    (p i).natDegree ≤ 536870911 ∧ (q i).natDegree ≤ 536870911 := by
  obtain ⟨hp, hq⟩ := degree_seven_budget productionCommonRoots (W i) s
    (by norm_num [s, productionT])
    (by rw [production_cardinalities.1]; norm_num [s, productionT])
    (AstraMcaOrder16Seed.seed_natDegree_le i)
  constructor <;> norm_num [p, q, s, productionT] at hp hq ⊢ <;> omega

def radius : ℝ≥0 := 313174699 / 1073741824

theorem support_arithmetic :
    (1 - radius) * Fintype.card (Fin (2 ^ 30)) = (760567125 : ℝ≥0) := by
  apply NNReal.coe_injective
  have hδ : radius ≤ 1 := by
    apply NNReal.coe_le_coe.mp
    norm_num [radius]
  rw [NNReal.coe_mul, NNReal.coe_sub hδ]
  norm_num [radius]

/-- A completely specified construction in the original same-support MCA
event predicate. No event/count/compatibility assumption is accepted here. -/
theorem many_events :
    ∃ u₀ u₁ : Fin (2 ^ 30) → F, ∃ bad : Finset F,
      bad.card = 1073741828 ∧
      ∀ γ ∈ bad, mcaEvent (F := F) AstraMcaProductionUpper.productionCode radius u₀ u₁ γ := by
  obtain ⟨u₀, u₁, bad, hc, he⟩ := exists_received_word_and_events
    productionEmbedding 536870911 radius p q productionCore base
    productionCovered productionUncovered (fun _ (i : Fin 4) => i)
    (fun i => (degree_budget i).1) (fun i => (degree_budget i).2) core_base
    (fun i => by rw [production_cardinalities.2.2.2 i]; norm_num)
    (fun i => by rw [production_cardinalities.2.2.2 i, support_arithmetic]; norm_num)
    (fun i x hx => (mem_production_domain_iff x).mp (production_core_subset_domain i hx))
    (fun i x hx hu => Finset.disjoint_left.mp (production_core_disjoint_uncovered i) hx hu)
    (fun x hx => (mem_production_domain_iff x).mp (covered_domain x hx))
    (fun x hx => (mem_production_domain_iff x).mp (uncovered_domain x hx))
    production_allocation_disjoint.2.2 covered_nonzero
    (fun i x _ => scaledQ_eval _ _ _ _)
    (fun _ _ => rfl) covered_nonowner uncovered_injective
    (by norm_num [ZMod.card, P])
    (by rw [production_cardinalities.2.1, production_cardinalities.2.2.1]
        norm_num [ZMod.card, P])
  refine ⟨u₀, u₁, bad, ?_, ?_⟩
  · simpa only [Fintype.card_fin, production_direction_count] using hc
  · simpa only [AstraMcaProductionUpper.productionCode] using he

theorem mca_error_lower :
    (1073741828 : ℝ≥0∞) / (P : ℝ≥0∞) ≤
      epsMCA (F := F) AstraMcaProductionUpper.productionCode radius := by
  obtain ⟨u₀, u₁, bad, hc, he⟩ := many_events
  let u : WordStack F (Fin 2) (Fin (2 ^ 30)) := fun j => if j = 0 then u₀ else u₁
  have h := epsMCA_ge_card_div_of_mcaEvent_set (F := F)
    AstraMcaProductionUpper.productionCode radius u bad
    (fun γ hγ => by simpa [u] using he γ hγ)
  simpa only [hc, ZMod.card] using h

theorem security_exceeded :
    (1 : ℝ≥0∞) / 2 ^ 128 <
      epsMCA (F := F) AstraMcaProductionUpper.productionCode radius := by
  apply lt_of_lt_of_le _ mca_error_lower
  apply (ENNReal.toReal_lt_toReal
    (ENNReal.div_ne_top (by norm_num) (by norm_num))
    (ENNReal.div_ne_top (by norm_num) (by norm_num [P]))).mp
  norm_num [ENNReal.toReal_div, ENNReal.toReal_pow, P]

/-- Concrete numeric upper bound for the original MCA threshold at rate one half. -/
theorem delta_star_upper :
    mcaDeltaStar (F := F) AstraMcaProductionUpper.productionCode ((1 : ℝ≥0∞) / 2 ^ 128) ≤
      (313174699 : ℝ≥0) / 1073741824 :=
  mcaDeltaStar_le_of_bad _ _ security_exceeded

end AstraMcaOrder16Assembly

#print axioms AstraMcaOrder16Assembly.overlapping_labels
#print axioms AstraMcaOrder16Assembly.core_overlap
#print axioms AstraMcaOrder16Assembly.many_events
#print axioms AstraMcaOrder16Assembly.mca_error_lower
#print axioms AstraMcaOrder16Assembly.security_exceeded
#print axioms AstraMcaOrder16Assembly.delta_star_upper
