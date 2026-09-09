/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_production_basis

/-!
# Order-sixteen power fibers and exact production allocation

The bounded-exponent and finite-block proofs adapt `astra_mca_power_fibers`.
The generic allocation has fiber size `6*t+4`; its actual finite core sets
have cardinality `68*t+44`. This module proves geometry and counts only;
seed equality, received-word assembly, and the final MCA statement are separate.
-/

set_option autoImplicit false

namespace AstraMcaOrder16Fibers

open AstraMcaProductionBasis
open ArkLib.ProximityGap.PrizeShapePrimeP30
open scoped BigOperators

/-! ## Bounded exponent arithmetic -/

/-- The exponent of the `t`-th point in fiber `j`. -/
def sixteenFiberIndex (s : ℕ) (j : Fin 16) (t : Fin s) : Fin (16 * s) :=
  ⟨j.val + 16 * t.val, by have hj := j.isLt; have ht := t.isLt; omega⟩

/-- Quotient and remainder modulo sixteen, with the remainder coordinate first. -/
def sixteenFiberEquiv (s : ℕ) : Fin 16 × Fin s ≃ Fin (16 * s) where
  toFun p := sixteenFiberIndex s p.1 p.2
  invFun e := (⟨e.val % 16, Nat.mod_lt _ (by decide)⟩,
    ⟨e.val / 16, by have he := e.isLt; omega⟩)
  left_inv p := by
    obtain ⟨j, t⟩ := p
    apply Prod.ext
    · apply Fin.ext
      change (j.val + 16 * t.val) % 16 = j.val
      have hj := j.isLt
      omega
    · apply Fin.ext
      change (j.val + 16 * t.val) / 16 = t.val
      have hj := j.isLt
      omega
  right_inv e := by
    apply Fin.ext
    change e.val % 16 + 16 * (e.val / 16) = e.val
    exact Nat.mod_add_div e.val 16

@[simp] theorem sixteenFiberEquiv_apply_val (s : ℕ) (j : Fin 16) (t : Fin s) :
    (sixteenFiberEquiv s (j, t)).val = j.val + 16 * t.val := rfl

/-! ## Actual powers, finite images, and intrinsic fiber membership -/

section PowerFibers

variable {F : Type*} [Monoid F] [DecidableEq F]

/-- An actual field/domain point, with an explicitly bounded fiber coordinate. -/
def fiberPoint (g : F) (s : ℕ) (j : Fin 16) (t : Fin s) : F :=
  g ^ (j.val + 16 * t.val)

/-- The finite image of one residue class of exponents modulo sixteen. -/
def powerFiber (g : F) (s : ℕ) (j : Fin 16) : Finset F :=
  Finset.univ.image (fiberPoint g s j)

omit [DecidableEq F] in
theorem fiberPoint_injective (g : F) (s : ℕ) (hg : orderOf g = 16 * s) :
    Function.Injective (fun p : Fin 16 × Fin s => fiberPoint g s p.1 p.2) := by
  intro p q hpq
  apply (sixteenFiberEquiv s).injective
  apply Fin.ext
  exact pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (by rw [hg]; exact (sixteenFiberIndex s p.1 p.2).isLt))
    (Set.mem_Iio.mpr (by rw [hg]; exact (sixteenFiberIndex s q.1 q.2).isLt)) hpq

omit [DecidableEq F] in
theorem fiberPoint_injective_in_fiber (g : F) (s : ℕ)
    (hg : orderOf g = 16 * s) (j : Fin 16) :
    Function.Injective (fiberPoint g s j) := by
  intro t u htu
  exact congrArg Prod.snd (fiberPoint_injective g s hg (show
    fiberPoint g s (j, t).1 (j, t).2 = fiberPoint g s (j, u).1 (j, u).2 from htu))

@[simp] theorem mem_powerFiber (g : F) (s : ℕ) (j : Fin 16) (x : F) :
    x ∈ powerFiber g s j ↔ ∃ t : Fin s, fiberPoint g s j t = x := by
  simp only [powerFiber, Finset.mem_image, Finset.mem_univ, true_and]

theorem powerFiber_card (g : F) (s : ℕ) (hg : orderOf g = 16 * s) (j : Fin 16) :
    (powerFiber g s j).card = s := by
  rw [powerFiber, Finset.card_image_of_injective _
    (fiberPoint_injective_in_fiber g s hg j), Finset.card_univ, Fintype.card_fin]

theorem powerFiber_subset_domain (g : F) (s : ℕ) (j : Fin 16) :
    powerFiber g s j ⊆ powerDomain g (16 * s) := by
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_powerFiber g s j x).mp hx
  exact Finset.mem_image.mpr ⟨j.val + 16 * t.val,
    Finset.mem_range.mpr (sixteenFiberIndex s j t).isLt, rfl⟩

/-- The sixteen fibers exhaust the actual finite power domain. -/
theorem powerFiber_cover (g : F) (s : ℕ) :
    Finset.univ.biUnion (powerFiber g s) = powerDomain g (16 * s) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact powerFiber_subset_domain g s j hj
  · intro hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    have he' : e < 16 * s := Finset.mem_range.mp he
    let j : Fin 16 := ⟨e % 16, Nat.mod_lt _ (by decide)⟩
    let t : Fin s := ⟨e / 16, by omega⟩
    refine ⟨j, (mem_powerFiber g s j (g ^ e)).mpr ⟨t, ?_⟩⟩
    change g ^ (e % 16 + 16 * (e / 16)) = g ^ e
    rw [Nat.mod_add_div]

theorem powerFiber_disjoint (g : F) (s : ℕ) (hg : orderOf g = 16 * s)
    {i j : Fin 16} (hij : i ≠ j) : Disjoint (powerFiber g s i) (powerFiber g s j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨t, ht⟩ := (mem_powerFiber g s i x).mp hxi
  obtain ⟨u, hu⟩ := (mem_powerFiber g s j x).mp hxj
  have hp : (i, t) = (j, u) := fiberPoint_injective g s hg (ht.trans hu.symm)
  exact hij (congrArg Prod.fst hp)

omit [DecidableEq F] in
/-- The quotient generator really has order sixteen, not merely sixteenh power one. -/
theorem orderOf_fiber_generator (g : F) (s : ℕ) (hs : 0 < s)
    (hg : orderOf g = 16 * s) : orderOf (g ^ s) = 16 := by
  have hpow : (g ^ s) ^ 16 = 1 := by
    rw [← pow_mul, Nat.mul_comm s 16, ← hg]
    exact pow_orderOf_eq_one g
  have hupper : orderOf (g ^ s) ∣ 16 := orderOf_dvd_of_pow_eq_one hpow
  have hpow' : g ^ (s * orderOf (g ^ s)) = 1 := by
    rw [pow_mul]
    exact pow_orderOf_eq_one (g ^ s)
  have hlower : 16 * s ∣ s * orderOf (g ^ s) := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one hpow'
  rw [Nat.mul_comm 16 s] at hlower
  exact Nat.dvd_antisymm hupper ((Nat.mul_dvd_mul_iff_left hs).mp hlower)

omit [DecidableEq F] in
theorem fiber_generator_powers_injective (g : F) (s : ℕ) (hs : 0 < s)
    (hg : orderOf g = 16 * s) :
    Function.Injective (fun j : Fin 16 => (g ^ s) ^ j.val) := by
  intro i j hij
  apply Fin.ext
  exact pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (by rw [orderOf_fiber_generator g s hs hg]; exact i.isLt))
    (Set.mem_Iio.mpr (by rw [orderOf_fiber_generator g s hs hg]; exact j.isLt)) hij

omit [DecidableEq F] in
theorem fiberPoint_pow (g : F) (s : ℕ) (hg : orderOf g = 16 * s)
    (j : Fin 16) (t : Fin s) : (fiberPoint g s j t) ^ s = (g ^ s) ^ j.val := by
  have hgn : g ^ (16 * s) = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  change (g ^ (j.val + 16 * t.val)) ^ s = (g ^ s) ^ j.val
  calc
    (g ^ (j.val + 16 * t.val)) ^ s = g ^ ((j.val + 16 * t.val) * s) :=
      (pow_mul _ _ _).symm
    _ = g ^ (s * j.val + (16 * s) * t.val) := by congr 1; ring
    _ = (g ^ s) ^ j.val * (g ^ (16 * s)) ^ t.val := by
      rw [pow_add, pow_mul, pow_mul]
    _ = (g ^ s) ^ j.val := by rw [hgn, one_pow, mul_one]

theorem mem_powerFiber_pow (g : F) (s : ℕ) (hg : orderOf g = 16 * s)
    (j : Fin 16) {x : F} (hx : x ∈ powerFiber g s j) : x ^ s = (g ^ s) ^ j.val := by
  obtain ⟨t, rfl⟩ := (mem_powerFiber g s j x).mp hx
  exact fiberPoint_pow g s hg j t

/-- Inside the domain, exponent fibers are exactly the fibers of `x ↦ x^s`. -/
theorem mem_powerFiber_iff (g : F) (s : ℕ) (hs : 0 < s)
    (hg : orderOf g = 16 * s) (j : Fin 16) (x : F) :
    x ∈ powerFiber g s j ↔ x ∈ powerDomain g (16 * s) ∧ x ^ s = (g ^ s) ^ j.val := by
  constructor
  · intro hx
    exact ⟨powerFiber_subset_domain g s j hx, mem_powerFiber_pow g s hg j hx⟩
  · rintro ⟨hx, hpow⟩
    rw [← powerFiber_cover g s] at hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    have hij : i = j := fiber_generator_powers_injective g s hs hg
      ((mem_powerFiber_pow g s hg i hi).symm.trans hpow)
    subst i
    exact hi

theorem powerFiber_eq_filter (g : F) (s : ℕ) (hs : 0 < s)
    (hg : orderOf g = 16 * s) (j : Fin 16) :
    powerFiber g s j = (powerDomain g (16 * s)).filter (fun x => x ^ s = (g ^ s) ^ j.val) := by
  ext x
  simpa only [Finset.mem_filter] using mem_powerFiber_iff g s hs hg j x

/-! ## Consecutive finite blocks -/

/-- `count` consecutive points starting at fiber coordinate `start`. -/
def fiberBlock (g : F) (j : Fin 16) (start count : ℕ) : Finset F :=
  (Finset.range count).image (fun t => g ^ (j.val + 16 * (start + t)))

@[simp] theorem fiberBlock_zero (g : F) (j : Fin 16) (start : ℕ) :
    fiberBlock g j start 0 = ∅ := by simp [fiberBlock]

theorem mem_fiberBlock (g : F) (j : Fin 16) (start count : ℕ) (x : F) :
    x ∈ fiberBlock g j start count ↔
      ∃ t : ℕ, t < count ∧ g ^ (j.val + 16 * (start + t)) = x := by
  simp only [fiberBlock, Finset.mem_image, Finset.mem_range]

theorem fiberBlock_subset_fiber (g : F) (s : ℕ) (j : Fin 16)
    (start count : ℕ) (hbound : start + count ≤ s) :
    fiberBlock g j start count ⊆ powerFiber g s j := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := (mem_fiberBlock g j start count x).mp hx
  exact (mem_powerFiber g s j _).mpr ⟨⟨start + t, by omega⟩, rfl⟩

theorem fiberBlock_card (g : F) (s : ℕ) (hg : orderOf g = 16 * s) (j : Fin 16)
    (start count : ℕ) (hbound : start + count ≤ s) :
    (fiberBlock g j start count).card = count := by
  unfold fiberBlock
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  have ha' : a < count := Finset.mem_range.mp ha
  have hb' : b < count := Finset.mem_range.mp hb
  have hj := j.isLt
  have hexp : j.val + 16 * (start + a) = j.val + 16 * (start + b) :=
    pow_injOn_Iio_orderOf
      (Set.mem_Iio.mpr (by rw [hg]; omega))
      (Set.mem_Iio.mpr (by rw [hg]; omega)) hab
  omega

theorem fiberBlock_disjoint_of_ne (g : F) (s : ℕ) (hg : orderOf g = 16 * s)
    {i j : Fin 16} (hij : i ≠ j) (a b c d : ℕ)
    (hab : a + b ≤ s) (hcd : c + d ≤ s) :
    Disjoint (fiberBlock g i a b) (fiberBlock g j c d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Finset.disjoint_left.mp (powerFiber_disjoint g s hg hij)
    (fiberBlock_subset_fiber g s i a b hab hx)
    (fiberBlock_subset_fiber g s j c d hcd hy)

/-- A union of sixteen blocks, specified solely by their starts and lengths. -/
def fiberBlocks (g : F) (start count : Fin 16 → ℕ) : Finset F :=
  Finset.univ.biUnion (fun j => fiberBlock g j (start j) (count j))

theorem fiberBlocks_card (g : F) (s : ℕ) (hg : orderOf g = 16 * s)
    (start count : Fin 16 → ℕ) (hbound : ∀ j, start j + count j ≤ s) :
    (fiberBlocks g start count).card = ∑ j, count j := by
  have hdisj : (↑(Finset.univ : Finset (Fin 16)) : Set (Fin 16)).PairwiseDisjoint
      (fun j => fiberBlock g j (start j) (count j)) := by
    intro i _ j _ hij
    exact fiberBlock_disjoint_of_ne g s hg hij _ _ _ _ (hbound i) (hbound j)
  rw [fiberBlocks, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl (fun j _ => fiberBlock_card g s hg j _ _ (hbound j))

theorem fiberBlocks_subset_domain (g : F) (s : ℕ) (start count : Fin 16 → ℕ)
    (hbound : ∀ j, start j + count j ≤ s) :
    fiberBlocks g start count ⊆ powerDomain g (16 * s) := by
  intro x hx
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
  exact powerFiber_subset_domain g s j
    (fiberBlock_subset_fiber g s j _ _ (hbound j) hj)

/-- Ordered, nonoverlapping coordinate blocks remain disjoint after evaluation. -/
theorem fiberBlocks_disjoint (g : F) (s : ℕ) (hg : orderOf g = 16 * s)
    (a b c d : Fin 16 → ℕ) (hab : ∀ j, a j + b j ≤ s)
    (hcd : ∀ j, c j + d j ≤ s) (hsep : ∀ j, a j + b j ≤ c j) :
    Disjoint (fiberBlocks g a b) (fiberBlocks g c d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hy
  obtain ⟨t, ht, htx⟩ := (mem_fiberBlock g i (a i) (b i) x).mp hi
  obtain ⟨u, hu, hux⟩ := (mem_fiberBlock g j (c j) (d j) x).mp hj
  have htbound : a i + t < s := by have h := hab i; omega
  have hubound : c j + u < s := by have h := hcd j; omega
  have hp : (i, (⟨a i + t, htbound⟩ : Fin s)) =
      (j, (⟨c j + u, hubound⟩ : Fin s)) :=
    fiberPoint_injective g s hg (htx.trans hux.symm)
  have hij : i = j := congrArg Prod.fst hp
  subst j
  have hcoord : a i + t = c i + u := congrArg (fun p : Fin 16 × Fin s => p.2.val) hp
  have h := hsep i
  omega

/-- Three consecutive blocks per fiber partition the whole finite domain. -/
theorem fiberBlocks_three_cover (g : F) (s : ℕ) (a b c : Fin 16 → ℕ)
    (hsum : ∀ j, a j + b j + c j = s) :
    fiberBlocks g (fun _ => 0) a ∪ fiberBlocks g a b ∪
      fiberBlocks g (fun j => a j + b j) c = powerDomain g (16 * s) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · rcases Finset.mem_union.mp hx with hx | hx
      · exact fiberBlocks_subset_domain g s (fun _ => 0) a
          (fun j => by
            change 0 + a j ≤ s
            have h := hsum j
            omega) hx
      · exact fiberBlocks_subset_domain g s a b
          (fun j => by have h := hsum j; omega) hx
    · exact fiberBlocks_subset_domain g s (fun j => a j + b j) c
        (fun j => (hsum j).le) hx
  · intro x hx
    rw [← powerFiber_cover g s] at hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨t, rfl⟩ := (mem_powerFiber g s j x).mp hj
    have ht := t.isLt
    have h := hsum j
    by_cases hta : t.val < a j
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_union.mpr
      left
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
        (mem_fiberBlock g j 0 (a j) _).mpr ⟨t.val, hta, by simp [fiberPoint]⟩⟩
    · by_cases htab : t.val < a j + b j
      · apply Finset.mem_union.mpr
        left
        apply Finset.mem_union.mpr
        right
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
          (mem_fiberBlock g j (a j) (b j) _).mpr ⟨t.val - a j, by omega, ?_⟩⟩
        change g ^ (j.val + 16 * (a j + (t.val - a j))) = g ^ (j.val + 16 * t.val)
        congr 1
        omega
      · apply Finset.mem_union.mpr
        right
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
          (mem_fiberBlock g j (a j + b j) (c j) _).mpr
            ⟨t.val - (a j + b j), by omega, ?_⟩⟩
        change g ^ (j.val + 16 * (a j + b j + (t.val - (a j + b j)))) =
          g ^ (j.val + 16 * t.val)
        congr 1
        omega

/-- Intrinsic membership in a block union reduces to its bounded coordinate. -/
theorem fiberPoint_mem_fiberBlocks_iff (g : F) (s : ℕ) (hg : orderOf g = 16 * s)
    (start count : Fin 16 → ℕ) (hbound : ∀ j, start j + count j ≤ s)
    (j : Fin 16) (u : Fin s) :
    fiberPoint g s j u ∈ fiberBlocks g start count ↔
      start j ≤ u.val ∧ u.val < start j + count j := by
  constructor
  · intro hx
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨v, hv, heq⟩ := (mem_fiberBlock g i (start i) (count i) _).mp hi
    have hb : start i + v < s := by have h := hbound i; omega
    have hp : (i, (⟨start i + v, hb⟩ : Fin s)) = (j, u) :=
      fiberPoint_injective g s hg heq
    have hij : i = j := congrArg Prod.fst hp
    subst i
    have hc : start j + v = u.val := congrArg (fun p : Fin 16 × Fin s => p.2.val) hp
    omega
  · rintro ⟨hl, hu⟩
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
    refine (mem_fiberBlock g j (start j) (count j) _).mpr ⟨u.val - start j, by omega, ?_⟩
    change g ^ (j.val + 16 * (start j + (u.val - start j))) = g ^ (j.val + 16 * u.val)
    congr 1
    omega

end PowerFibers

/-! ## Generic allocation at fiber size `6*t+4` -/

/-- Common-root prefixes in fibers two, six, and fourteen. -/
def rootCount (t : ℕ) (j : Fin 16) : ℕ :=
  if j = 2 then 4 * t + 2 else if j = 6 ∨ j = 14 then t else 0

/-- All remaining points are covered except the suffix of fiber two. -/
def coveredCount (t : ℕ) (j : Fin 16) : ℕ :=
  if j = 2 then 0 else if j = 6 ∨ j = 14 then 5 * t + 4 else 6 * t + 4

def uncoveredCount (t : ℕ) (j : Fin 16) : ℕ := if j = 2 then 2 * t + 2 else 0

/-- Only the second ownership pair starts halfway through fiber ten. -/
def coreStart (t : ℕ) (i : Fin 4) (j : Fin 16) : ℕ :=
  if j = 10 ∧ (i = 1 ∨ i = 2) then 3 * t + 2 else 0

/-- Per-source core blocks: all common roots, nine triple fibers, its pair
fiber, and one half of fiber ten. -/
def coreCount (t : ℕ) (i : Fin 4) (j : Fin 16) : ℕ :=
  if j = 2 then 4 * t + 2 else
  if j = 6 then (if i = 0 ∨ i = 1 then 6 * t + 4 else t) else
  if j = 10 then 3 * t + 2 else
  if j = 14 then (if i = 2 ∨ i = 3 then 6 * t + 4 else t) else
  if (i = 0 ∧ (j = 4 ∨ j = 7 ∨ j = 15)) ∨
      (i = 1 ∧ (j = 3 ∨ j = 11 ∨ j = 12)) ∨
      (i = 2 ∧ (j = 1 ∨ j = 8 ∨ j = 9)) ∨
      (i = 3 ∧ (j = 0 ∨ j = 5 ∨ j = 13)) then 0 else 6 * t + 4

theorem allocation_arithmetic (t : ℕ) :
    (∀ j, rootCount t j + coveredCount t j + uncoveredCount t j = 6 * t + 4) ∧
    (∑ j, rootCount t j) = 6 * t + 2 ∧
    (∑ j, coveredCount t j) = 88 * t + 60 ∧
    (∑ j, uncoveredCount t j) = 2 * t + 2 := by
  constructor
  · intro j
    fin_cases j <;> simp [rootCount, coveredCount, uncoveredCount] <;> omega
  · refine ⟨?_, ?_, ?_⟩ <;>
      norm_num [rootCount, coveredCount, uncoveredCount, Fin.sum_univ_succ, Fin.ext_iff] <;> omega

theorem core_arithmetic (t : ℕ) (i : Fin 4) :
    (∀ j, coreStart t i j + coreCount t i j ≤ 6 * t + 4) ∧
    (∑ j, coreCount t i j) = 68 * t + 44 ∧
    (∀ j, coreStart t i j + coreCount t i j ≤ rootCount t j + coveredCount t j) := by
  constructor
  · intro j
    fin_cases i <;> fin_cases j <;> simp [coreStart, coreCount] <;> omega
  · constructor
    · simp only [Fin.sum_univ_succ, Fin.sum_univ_zero]
      change coreCount t i 0 + (coreCount t i 1 + (coreCount t i 2 +
        (coreCount t i 3 + (coreCount t i 4 + (coreCount t i 5 +
        (coreCount t i 6 + (coreCount t i 7 + (coreCount t i 8 +
        (coreCount t i 9 + (coreCount t i 10 + (coreCount t i 11 +
        (coreCount t i 12 + (coreCount t i 13 + (coreCount t i 14 +
        (coreCount t i 15 + 0))))))))))))))) = 68 * t + 44
      fin_cases i <;> norm_num [coreCount, Fin.ext_iff] <;> omega
    · intro j
      fin_cases i <;> fin_cases j <;>
        simp [coreStart, coreCount, rootCount, coveredCount] <;> omega

section Allocation

variable {F : Type*} [Monoid F] [DecidableEq F]

def commonRoots (g : F) (t : ℕ) : Finset F := fiberBlocks g (fun _ => 0) (rootCount t)
def covered (g : F) (t : ℕ) : Finset F := fiberBlocks g (rootCount t) (coveredCount t)
def uncovered (g : F) (t : ℕ) : Finset F :=
  fiberBlocks g (fun j => rootCount t j + coveredCount t j) (uncoveredCount t)
def core (g : F) (t : ℕ) (i : Fin 4) : Finset F :=
  fiberBlocks g (coreStart t i) (coreCount t i)

theorem commonRoots_card (g : F) (t : ℕ) (hg : orderOf g = 16 * (6 * t + 4)) :
    (commonRoots g t).card = 6 * t + 2 := by
  rw [commonRoots, fiberBlocks_card g (6 * t + 4) hg]
  · exact (allocation_arithmetic t).2.1
  · intro j
    have h := (allocation_arithmetic t).1 j
    omega

theorem covered_card (g : F) (t : ℕ) (hg : orderOf g = 16 * (6 * t + 4)) :
    (covered g t).card = 88 * t + 60 := by
  rw [covered, fiberBlocks_card g (6 * t + 4) hg]
  · exact (allocation_arithmetic t).2.2.1
  · intro j
    have h := (allocation_arithmetic t).1 j
    omega

theorem uncovered_card (g : F) (t : ℕ) (hg : orderOf g = 16 * (6 * t + 4)) :
    (uncovered g t).card = 2 * t + 2 := by
  rw [uncovered, fiberBlocks_card g (6 * t + 4) hg]
  · exact (allocation_arithmetic t).2.2.2
  · intro j
    exact ((allocation_arithmetic t).1 j).le

theorem core_card (g : F) (t : ℕ) (hg : orderOf g = 16 * (6 * t + 4)) (i : Fin 4) :
    (core g t i).card = 68 * t + 44 := by
  rw [core, fiberBlocks_card g (6 * t + 4) hg _ _ (core_arithmetic t i).1]
  exact (core_arithmetic t i).2.1

theorem allocation_cover (g : F) (t : ℕ) :
    commonRoots g t ∪ covered g t ∪ uncovered g t = powerDomain g (16 * (6 * t + 4)) :=
  fiberBlocks_three_cover g (6 * t + 4) _ _ _ (allocation_arithmetic t).1

theorem allocation_disjoint (g : F) (t : ℕ) (hg : orderOf g = 16 * (6 * t + 4)) :
    Disjoint (commonRoots g t) (covered g t) ∧
    Disjoint (commonRoots g t) (uncovered g t) ∧
    Disjoint (covered g t) (uncovered g t) := by
  have hsum := (allocation_arithmetic t).1
  have hr : ∀ j, 0 + rootCount t j ≤ 6 * t + 4 := by
    intro j
    have h := hsum j
    omega
  have hc : ∀ j, rootCount t j + coveredCount t j ≤ 6 * t + 4 := by
    intro j
    have h := hsum j
    omega
  have hu : ∀ j, rootCount t j + coveredCount t j + uncoveredCount t j ≤ 6 * t + 4 :=
    fun j => (hsum j).le
  refine ⟨?_, ?_, ?_⟩
  · exact fiberBlocks_disjoint g (6 * t + 4) hg _ _ _ _ hr hc (fun _ => by omega)
  · exact fiberBlocks_disjoint g (6 * t + 4) hg _ _ _ _ hr hu (fun _ => by omega)
  · exact fiberBlocks_disjoint g (6 * t + 4) hg _ _ _ _ hc hu (fun _ => le_rfl)

theorem core_subset_domain (g : F) (t : ℕ) (i : Fin 4) :
    core g t i ⊆ powerDomain g (16 * (6 * t + 4)) :=
  fiberBlocks_subset_domain g (6 * t + 4) _ _ (core_arithmetic t i).1

theorem core_disjoint_uncovered (g : F) (t : ℕ)
    (hg : orderOf g = 16 * (6 * t + 4)) (i : Fin 4) :
    Disjoint (core g t i) (uncovered g t) :=
  fiberBlocks_disjoint g (6 * t + 4) hg _ _ _ _ (core_arithmetic t i).1
    (fun j => ((allocation_arithmetic t).1 j).le) (core_arithmetic t i).2.2

theorem commonRoots_subset_core (g : F) (t : ℕ) (i : Fin 4) :
    commonRoots g t ⊆ core g t i := by
  intro x hx
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨u, hu, he⟩ := (mem_fiberBlock g j 0 (rootCount t j) x).mp hj
  have hblocks : coreStart t i j = 0 ∧ rootCount t j ≤ coreCount t i j := by
    fin_cases i <;> fin_cases j <;>
      simp_all [coreStart, coreCount, rootCount] <;> omega
  refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
  refine (mem_fiberBlock g j (coreStart t i j) (coreCount t i j) x).mpr
    ⟨u, by omega, ?_⟩
  simpa only [hblocks.1] using he

theorem covered_subset_domain (g : F) (t : ℕ) :
    covered g t ⊆ powerDomain g (16 * (6 * t + 4)) := by
  apply fiberBlocks_subset_domain g (6 * t + 4)
  intro j
  have h := (allocation_arithmetic t).1 j
  omega

theorem uncovered_subset_domain (g : F) (t : ℕ) :
    uncovered g t ⊆ powerDomain g (16 * (6 * t + 4)) :=
  fiberBlocks_subset_domain g (6 * t + 4) _ _ (fun j => ((allocation_arithmetic t).1 j).le)

end Allocation

/-! ## Certified production specialization -/

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

def productionT : ℕ := 11184810

theorem production_size : 6 * productionT + 4 = 2 ^ 26 := by norm_num [productionT]
theorem production_fiber_order : orderOf g = 16 * (6 * productionT + 4) := by
  rw [orderOf_g]
  norm_num [productionT]

def productionFiber (j : Fin 16) : Finset (ZMod P) := powerFiber g (6 * productionT + 4) j

def productionCommonRoots : Finset (ZMod P) := commonRoots g productionT
def productionCovered : Finset (ZMod P) := covered g productionT
def productionUncovered : Finset (ZMod P) := uncovered g productionT
def productionCore (i : Fin 4) : Finset (ZMod P) := core g productionT i

theorem production_fiber_card (j : Fin 16) : (productionFiber j).card = 67108864 :=
  powerFiber_card g (6 * productionT + 4) production_fiber_order j

theorem production_fiber_generator_order : orderOf (g ^ (2 ^ 26)) = 16 := by
  rw [← production_size]
  exact orderOf_fiber_generator g (6 * productionT + 4) (by omega) production_fiber_order

theorem production_fiber_mem_iff (j : Fin 16) (x : ZMod P) :
    x ∈ productionFiber j ↔ x ∈ productionDomain ∧ x ^ (2 ^ 26) = (g ^ (2 ^ 26)) ^ j.val := by
  simpa only [productionFiber, productionDomain, production_size,
    show 16 * (2 ^ 26) = 2 ^ 30 by norm_num] using
      mem_powerFiber_iff g (6 * productionT + 4) (by omega) production_fiber_order j x

theorem production_cardinalities :
    productionCommonRoots.card = 67108862 ∧
    productionCovered.card = 984263340 ∧
    productionUncovered.card = 22369622 ∧
    ∀ i, (productionCore i).card = 760567124 := by
  refine ⟨commonRoots_card g productionT production_fiber_order,
    covered_card g productionT production_fiber_order,
    uncovered_card g productionT production_fiber_order, ?_⟩
  exact fun i => core_card g productionT production_fiber_order i

theorem production_allocation_cover :
    productionCommonRoots ∪ productionCovered ∪ productionUncovered = productionDomain := by
  simpa only [productionCommonRoots, productionCovered, productionUncovered, productionDomain,
    production_size, show 16 * (2 ^ 26) = 2 ^ 30 by norm_num] using allocation_cover g productionT

theorem production_allocation_disjoint :
    Disjoint productionCommonRoots productionCovered ∧
    Disjoint productionCommonRoots productionUncovered ∧
    Disjoint productionCovered productionUncovered :=
  allocation_disjoint g productionT production_fiber_order

theorem production_core_disjoint_uncovered (i : Fin 4) :
    Disjoint (productionCore i) productionUncovered :=
  core_disjoint_uncovered g productionT production_fiber_order i

theorem production_core_subset_domain (i : Fin 4) : productionCore i ⊆ productionDomain := by
  simpa only [productionCore, productionDomain, production_size,
    show 16 * (2 ^ 26) = 2 ^ 30 by norm_num] using core_subset_domain g productionT i

/-- The finite received-word assembly's exact direction budget. -/
theorem production_direction_count :
    productionCovered.card + productionUncovered.card * 4 = 2 ^ 30 + 4 := by
  rw [production_cardinalities.2.1, production_cardinalities.2.2.1]
  norm_num

end AstraMcaOrder16Fibers

#print axioms AstraMcaOrder16Fibers.sixteenFiberEquiv
#print axioms AstraMcaOrder16Fibers.mem_powerFiber_iff
#print axioms AstraMcaOrder16Fibers.fiberBlocks_card
#print axioms AstraMcaOrder16Fibers.core_arithmetic
#print axioms AstraMcaOrder16Fibers.production_cardinalities
#print axioms AstraMcaOrder16Fibers.production_allocation_cover
#print axioms AstraMcaOrder16Fibers.production_allocation_disjoint
#print axioms AstraMcaOrder16Fibers.production_core_disjoint_uncovered
#print axioms AstraMcaOrder16Fibers.production_direction_count

#print axioms AstraMcaOrder16Fibers.fiberPoint_mem_fiberBlocks_iff
#print axioms AstraMcaOrder16Fibers.commonRoots_subset_core
#print axioms AstraMcaOrder16Fibers.production_core_subset_domain
