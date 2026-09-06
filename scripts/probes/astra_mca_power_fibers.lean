/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import scripts.probes.astra_mca_production_events

/-!
# Eight power fibers and the production allocation blocks

For a generator of order `8 * s`, this file uses the actual exponents `j + 8*t`
to partition its power domain. The proofs operate on bounded indices; none
enumerates the production domain. The last section specifies the consecutive
common-root, covered, and uncovered blocks of the four-cubic construction.

Status: proof source written on 2026-09-06; not kernel-checked in the local
session, whose Lean toolchain and dependency cache are unavailable. The seed,
polynomial, received-word, and final numerical MCA instantiations are separate.
-/

set_option autoImplicit false

namespace AstraMcaPowerFibers

open AstraMcaProductionBasis AstraMcaProductionEvents
open ArkLib.ProximityGap.PrizeShapePrimeP30
open scoped BigOperators

/-! ## Bounded exponent arithmetic -/

/-- The exponent of the `t`-th point in fiber `j`. -/
def eightFiberIndex (s : ℕ) (j : Fin 8) (t : Fin s) : Fin (8 * s) :=
  ⟨j.val + 8 * t.val, by have hj := j.isLt; have ht := t.isLt; omega⟩

/-- Quotient and remainder modulo eight, with the remainder coordinate first. -/
def eightFiberEquiv (s : ℕ) : Fin 8 × Fin s ≃ Fin (8 * s) where
  toFun p := eightFiberIndex s p.1 p.2
  invFun e := (⟨e.val % 8, Nat.mod_lt _ (by decide)⟩,
    ⟨e.val / 8, by have he := e.isLt; omega⟩)
  left_inv p := by
    obtain ⟨j, t⟩ := p
    apply Prod.ext
    · apply Fin.ext
      change (j.val + 8 * t.val) % 8 = j.val
      have hj := j.isLt
      omega
    · apply Fin.ext
      change (j.val + 8 * t.val) / 8 = t.val
      have hj := j.isLt
      omega
  right_inv e := by
    apply Fin.ext
    change e.val % 8 + 8 * (e.val / 8) = e.val
    exact Nat.mod_add_div e.val 8

@[simp] theorem eightFiberEquiv_apply_val (s : ℕ) (j : Fin 8) (t : Fin s) :
    (eightFiberEquiv s (j, t)).val = j.val + 8 * t.val := rfl

/-! ## Actual powers, finite images, and intrinsic fiber membership -/

section PowerFibers

variable {F : Type*} [Monoid F] [DecidableEq F]

/-- An actual field/domain point, with an explicitly bounded fiber coordinate. -/
def fiberPoint (g : F) (s : ℕ) (j : Fin 8) (t : Fin s) : F :=
  g ^ (j.val + 8 * t.val)

/-- The finite image of one residue class of exponents modulo eight. -/
def powerFiber (g : F) (s : ℕ) (j : Fin 8) : Finset F :=
  Finset.univ.image (fiberPoint g s j)

omit [DecidableEq F] in
theorem fiberPoint_injective (g : F) (s : ℕ) (hg : orderOf g = 8 * s) :
    Function.Injective (fun p : Fin 8 × Fin s => fiberPoint g s p.1 p.2) := by
  intro p q hpq
  apply (eightFiberEquiv s).injective
  apply Fin.ext
  exact pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (by rw [hg]; exact (eightFiberIndex s p.1 p.2).isLt))
    (Set.mem_Iio.mpr (by rw [hg]; exact (eightFiberIndex s q.1 q.2).isLt)) hpq

omit [DecidableEq F] in
theorem fiberPoint_injective_in_fiber (g : F) (s : ℕ)
    (hg : orderOf g = 8 * s) (j : Fin 8) :
    Function.Injective (fiberPoint g s j) := by
  intro t u htu
  exact congrArg Prod.snd (fiberPoint_injective g s hg (show
    fiberPoint g s (j, t).1 (j, t).2 = fiberPoint g s (j, u).1 (j, u).2 from htu))

@[simp] theorem mem_powerFiber (g : F) (s : ℕ) (j : Fin 8) (x : F) :
    x ∈ powerFiber g s j ↔ ∃ t : Fin s, fiberPoint g s j t = x := by
  simp only [powerFiber, Finset.mem_image, Finset.mem_univ, true_and]

theorem powerFiber_card (g : F) (s : ℕ) (hg : orderOf g = 8 * s) (j : Fin 8) :
    (powerFiber g s j).card = s := by
  rw [powerFiber, Finset.card_image_of_injective _
    (fiberPoint_injective_in_fiber g s hg j), Finset.card_univ, Fintype.card_fin]

theorem powerFiber_subset_domain (g : F) (s : ℕ) (j : Fin 8) :
    powerFiber g s j ⊆ powerDomain g (8 * s) := by
  intro x hx
  obtain ⟨t, rfl⟩ := (mem_powerFiber g s j x).mp hx
  exact Finset.mem_image.mpr ⟨j.val + 8 * t.val,
    Finset.mem_range.mpr (eightFiberIndex s j t).isLt, rfl⟩

/-- The eight fibers exhaust the actual finite power domain. -/
theorem powerFiber_cover (g : F) (s : ℕ) :
    Finset.univ.biUnion (powerFiber g s) = powerDomain g (8 * s) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    exact powerFiber_subset_domain g s j hj
  · intro hx
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hx
    have he' : e < 8 * s := Finset.mem_range.mp he
    let j : Fin 8 := ⟨e % 8, Nat.mod_lt _ (by decide)⟩
    let t : Fin s := ⟨e / 8, by omega⟩
    refine ⟨j, (mem_powerFiber g s j (g ^ e)).mpr ⟨t, ?_⟩⟩
    change g ^ (e % 8 + 8 * (e / 8)) = g ^ e
    rw [Nat.mod_add_div]

theorem powerFiber_disjoint (g : F) (s : ℕ) (hg : orderOf g = 8 * s)
    {i j : Fin 8} (hij : i ≠ j) : Disjoint (powerFiber g s i) (powerFiber g s j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨t, ht⟩ := (mem_powerFiber g s i x).mp hxi
  obtain ⟨u, hu⟩ := (mem_powerFiber g s j x).mp hxj
  have hp : (i, t) = (j, u) := fiberPoint_injective g s hg (ht.trans hu.symm)
  exact hij (congrArg Prod.fst hp)

omit [DecidableEq F] in
/-- The quotient generator really has order eight, not merely eighth power one. -/
theorem orderOf_fiber_generator (g : F) (s : ℕ) (hs : 0 < s)
    (hg : orderOf g = 8 * s) : orderOf (g ^ s) = 8 := by
  have hpow : (g ^ s) ^ 8 = 1 := by
    rw [← pow_mul, Nat.mul_comm s 8, ← hg]
    exact pow_orderOf_eq_one g
  have hupper : orderOf (g ^ s) ∣ 8 := orderOf_dvd_of_pow_eq_one hpow
  have hpow' : g ^ (s * orderOf (g ^ s)) = 1 := by
    rw [pow_mul]
    exact pow_orderOf_eq_one (g ^ s)
  have hlower : 8 * s ∣ s * orderOf (g ^ s) := by
    rw [← hg]
    exact orderOf_dvd_of_pow_eq_one hpow'
  rw [Nat.mul_comm 8 s] at hlower
  exact Nat.dvd_antisymm hupper ((Nat.mul_dvd_mul_iff_left hs).mp hlower)

omit [DecidableEq F] in
theorem fiber_generator_powers_injective (g : F) (s : ℕ) (hs : 0 < s)
    (hg : orderOf g = 8 * s) :
    Function.Injective (fun j : Fin 8 => (g ^ s) ^ j.val) := by
  intro i j hij
  apply Fin.ext
  exact pow_injOn_Iio_orderOf
    (Set.mem_Iio.mpr (by rw [orderOf_fiber_generator g s hs hg]; exact i.isLt))
    (Set.mem_Iio.mpr (by rw [orderOf_fiber_generator g s hs hg]; exact j.isLt)) hij

omit [DecidableEq F] in
theorem fiberPoint_pow (g : F) (s : ℕ) (hg : orderOf g = 8 * s)
    (j : Fin 8) (t : Fin s) : (fiberPoint g s j t) ^ s = (g ^ s) ^ j.val := by
  have hgn : g ^ (8 * s) = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  change (g ^ (j.val + 8 * t.val)) ^ s = (g ^ s) ^ j.val
  calc
    (g ^ (j.val + 8 * t.val)) ^ s = g ^ ((j.val + 8 * t.val) * s) :=
      (pow_mul _ _ _).symm
    _ = g ^ (s * j.val + (8 * s) * t.val) := by congr 1; ring
    _ = (g ^ s) ^ j.val * (g ^ (8 * s)) ^ t.val := by
      rw [pow_add, pow_mul, pow_mul]
    _ = (g ^ s) ^ j.val := by rw [hgn, one_pow, mul_one]

theorem mem_powerFiber_pow (g : F) (s : ℕ) (hg : orderOf g = 8 * s)
    (j : Fin 8) {x : F} (hx : x ∈ powerFiber g s j) : x ^ s = (g ^ s) ^ j.val := by
  obtain ⟨t, rfl⟩ := (mem_powerFiber g s j x).mp hx
  exact fiberPoint_pow g s hg j t

/-- Inside the domain, exponent fibers are exactly the fibers of `x ↦ x^s`. -/
theorem mem_powerFiber_iff (g : F) (s : ℕ) (hs : 0 < s)
    (hg : orderOf g = 8 * s) (j : Fin 8) (x : F) :
    x ∈ powerFiber g s j ↔ x ∈ powerDomain g (8 * s) ∧ x ^ s = (g ^ s) ^ j.val := by
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
    (hg : orderOf g = 8 * s) (j : Fin 8) :
    powerFiber g s j = (powerDomain g (8 * s)).filter (fun x => x ^ s = (g ^ s) ^ j.val) := by
  ext x
  simpa only [Finset.mem_filter] using mem_powerFiber_iff g s hs hg j x

/-! ## Consecutive finite blocks -/

/-- `count` consecutive points starting at fiber coordinate `start`. -/
def fiberBlock (g : F) (j : Fin 8) (start count : ℕ) : Finset F :=
  (Finset.range count).image (fun t => g ^ (j.val + 8 * (start + t)))

@[simp] theorem fiberBlock_zero (g : F) (j : Fin 8) (start : ℕ) :
    fiberBlock g j start 0 = ∅ := by simp [fiberBlock]

theorem mem_fiberBlock (g : F) (j : Fin 8) (start count : ℕ) (x : F) :
    x ∈ fiberBlock g j start count ↔
      ∃ t : ℕ, t < count ∧ g ^ (j.val + 8 * (start + t)) = x := by
  simp only [fiberBlock, Finset.mem_image, Finset.mem_range]

theorem fiberBlock_subset_fiber (g : F) (s : ℕ) (j : Fin 8)
    (start count : ℕ) (hbound : start + count ≤ s) :
    fiberBlock g j start count ⊆ powerFiber g s j := by
  intro x hx
  obtain ⟨t, ht, rfl⟩ := (mem_fiberBlock g j start count x).mp hx
  exact (mem_powerFiber g s j _).mpr ⟨⟨start + t, by omega⟩, rfl⟩

theorem fiberBlock_card (g : F) (s : ℕ) (hg : orderOf g = 8 * s) (j : Fin 8)
    (start count : ℕ) (hbound : start + count ≤ s) :
    (fiberBlock g j start count).card = count := by
  unfold fiberBlock
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb hab
  have ha' : a < count := Finset.mem_range.mp ha
  have hb' : b < count := Finset.mem_range.mp hb
  have hj := j.isLt
  have hexp : j.val + 8 * (start + a) = j.val + 8 * (start + b) :=
    pow_injOn_Iio_orderOf
      (Set.mem_Iio.mpr (by rw [hg]; omega))
      (Set.mem_Iio.mpr (by rw [hg]; omega)) hab
  omega

theorem fiberBlock_disjoint_of_ne (g : F) (s : ℕ) (hg : orderOf g = 8 * s)
    {i j : Fin 8} (hij : i ≠ j) (a b c d : ℕ)
    (hab : a + b ≤ s) (hcd : c + d ≤ s) :
    Disjoint (fiberBlock g i a b) (fiberBlock g j c d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact Finset.disjoint_left.mp (powerFiber_disjoint g s hg hij)
    (fiberBlock_subset_fiber g s i a b hab hx)
    (fiberBlock_subset_fiber g s j c d hcd hy)

/-- A union of eight blocks, specified solely by their starts and lengths. -/
def fiberBlocks (g : F) (start count : Fin 8 → ℕ) : Finset F :=
  Finset.univ.biUnion (fun j => fiberBlock g j (start j) (count j))

theorem fiberBlocks_card (g : F) (s : ℕ) (hg : orderOf g = 8 * s)
    (start count : Fin 8 → ℕ) (hbound : ∀ j, start j + count j ≤ s) :
    (fiberBlocks g start count).card = ∑ j, count j := by
  have hdisj : (↑(Finset.univ : Finset (Fin 8)) : Set (Fin 8)).PairwiseDisjoint
      (fun j => fiberBlock g j (start j) (count j)) := by
    intro i _ j _ hij
    exact fiberBlock_disjoint_of_ne g s hg hij _ _ _ _ (hbound i) (hbound j)
  rw [fiberBlocks, Finset.card_biUnion hdisj]
  exact Finset.sum_congr rfl (fun j _ => fiberBlock_card g s hg j _ _ (hbound j))

theorem fiberBlocks_subset_domain (g : F) (s : ℕ) (start count : Fin 8 → ℕ)
    (hbound : ∀ j, start j + count j ≤ s) :
    fiberBlocks g start count ⊆ powerDomain g (8 * s) := by
  intro x hx
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
  exact powerFiber_subset_domain g s j
    (fiberBlock_subset_fiber g s j _ _ (hbound j) hj)

/-- Ordered, nonoverlapping coordinate blocks remain disjoint after evaluation. -/
theorem fiberBlocks_disjoint (g : F) (s : ℕ) (hg : orderOf g = 8 * s)
    (a b c d : Fin 8 → ℕ) (hab : ∀ j, a j + b j ≤ s)
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
  have hcoord : a i + t = c i + u := congrArg (fun p : Fin 8 × Fin s => p.2.val) hp
  have h := hsep i
  omega

/-- Three consecutive blocks per fiber partition the whole finite domain. -/
theorem fiberBlocks_three_cover (g : F) (s : ℕ) (a b c : Fin 8 → ℕ)
    (hsum : ∀ j, a j + b j + c j = s) :
    fiberBlocks g (fun _ => 0) a ∪ fiberBlocks g a b ∪
      fiberBlocks g (fun j => a j + b j) c = powerDomain g (8 * s) := by
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
        change g ^ (j.val + 8 * (a j + (t.val - a j))) = g ^ (j.val + 8 * t.val)
        congr 1
        omega
      · apply Finset.mem_union.mpr
        right
        refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
          (mem_fiberBlock g j (a j + b j) (c j) _).mpr
            ⟨t.val - (a j + b j), by omega, ?_⟩⟩
        change g ^ (j.val + 8 * (a j + b j + (t.val - (a j + b j)))) =
          g ^ (j.val + 8 * t.val)
        congr 1
        omega

end PowerFibers

/-! ## The certified production generator and the four-cubic allocation -/

local instance : Fact (Nat.Prime P) := ⟨prime_P⟩

theorem production_fiber_order : orderOf g = 8 * (2 ^ 27) := by
  rw [orderOf_g]
  norm_num

def productionFiber (j : Fin 8) : Finset (ZMod P) := powerFiber g (2 ^ 27) j

theorem production_fiber_card (j : Fin 8) : (productionFiber j).card = 134217728 :=
  powerFiber_card g (2 ^ 27) production_fiber_order j

theorem production_fibers_disjoint {i j : Fin 8} (hij : i ≠ j) :
    Disjoint (productionFiber i) (productionFiber j) :=
  powerFiber_disjoint g (2 ^ 27) production_fiber_order hij

theorem production_fibers_cover :
    Finset.univ.biUnion productionFiber = productionDomain := by
  simpa only [productionFiber, productionDomain,
    show 8 * (2 ^ 27) = 2 ^ 30 by norm_num] using powerFiber_cover g (2 ^ 27)

theorem production_fiber_generator_order : orderOf (g ^ (2 ^ 27)) = 8 :=
  orderOf_fiber_generator g (2 ^ 27) (by norm_num) production_fiber_order

theorem production_fiber_mem_iff (j : Fin 8) (x : ZMod P) :
    x ∈ productionFiber j ↔
      x ∈ productionDomain ∧ x ^ (2 ^ 27) = (g ^ (2 ^ 27)) ^ j.val := by
  simpa only [productionFiber, productionDomain,
    show 8 * (2 ^ 27) = 2 ^ 30 by norm_num] using
      mem_powerFiber_iff g (2 ^ 27) (by norm_num) production_fiber_order j x

/-- The fiber coordinates are positions in the existing full-code evaluation embedding. -/
theorem production_embedding_fiberPoint (j : Fin 8) (t : Fin (2 ^ 27)) :
    productionEmbedding
      ⟨j.val + 8 * t.val, by
        simpa only [show 8 * (2 ^ 27) = 2 ^ 30 by norm_num] using
          (eightFiberIndex (2 ^ 27) j t).isLt⟩ = fiberPoint g (2 ^ 27) j t := rfl

/-- Common-root prefix lengths: `s/2-1` in fibers four and five. -/
def productionRootCount (j : Fin 8) : ℕ :=
  if j = 4 ∨ j = 5 then 67108863 else 0

/-- The covered blocks start immediately after the common-root prefix. -/
def productionCoveredCount (j : Fin 8) : ℕ :=
  if j = 2 ∨ j = 4 ∨ j = 5 then 67108864 else 134217728

/-- The suffix is half of fiber two and one point each in fibers four and five. -/
def productionUncoveredCount (j : Fin 8) : ℕ :=
  if j = 2 then 67108864 else if j = 4 ∨ j = 5 then 1 else 0

theorem production_allocation_arithmetic :
    (∀ j, productionRootCount j + productionCoveredCount j +
      productionUncoveredCount j = 2 ^ 27) ∧
    (∑ j, productionRootCount j) = 134217726 ∧
    (∑ j, productionCoveredCount j) = 872415232 ∧
    (∑ j, productionUncoveredCount j) = 67108866 := by
  decide

def productionCommonRoots : Finset (ZMod P) :=
  fiberBlocks g (fun _ => 0) productionRootCount

def productionCovered : Finset (ZMod P) :=
  fiberBlocks g productionRootCount productionCoveredCount

def productionUncovered : Finset (ZMod P) :=
  fiberBlocks g (fun j => productionRootCount j + productionCoveredCount j)
    productionUncoveredCount

theorem production_common_roots_two_prefixes :
    productionCommonRoots = fiberBlock g 4 0 67108863 ∪ fiberBlock g 5 0 67108863 := by
  ext x
  constructor
  · intro hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    by_cases h45 : j = 4 ∨ j = 5
    · rcases h45 with h4 | h5
      · subst j
        exact Finset.mem_union.mpr (Or.inl (by simpa [productionRootCount] using hj))
      · subst j
        exact Finset.mem_union.mpr (Or.inr (by simpa [productionRootCount] using hj))
    · have hempty : fiberBlock g j 0 (productionRootCount j) = ∅ := by
        simp only [productionRootCount, if_neg h45, fiberBlock_zero]
      rw [hempty] at hj
      simp at hj
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_biUnion.mpr ⟨4, Finset.mem_univ _,
        by simpa [productionRootCount] using hx⟩
    · exact Finset.mem_biUnion.mpr ⟨5, Finset.mem_univ _,
        by simpa [productionRootCount] using hx⟩

theorem production_common_roots_card : productionCommonRoots.card = 134217726 := by
  rw [productionCommonRoots, fiberBlocks_card g (2 ^ 27) production_fiber_order]
  · exact production_allocation_arithmetic.2.1
  · intro j
    have h := production_allocation_arithmetic.1 j
    omega

theorem production_covered_card : productionCovered.card = 872415232 := by
  rw [productionCovered, fiberBlocks_card g (2 ^ 27) production_fiber_order]
  · exact production_allocation_arithmetic.2.2.1
  · intro j
    have h := production_allocation_arithmetic.1 j
    omega

theorem production_uncovered_card : productionUncovered.card = 67108866 := by
  rw [productionUncovered, fiberBlocks_card g (2 ^ 27) production_fiber_order]
  · exact production_allocation_arithmetic.2.2.2
  · intro j
    exact (production_allocation_arithmetic.1 j).le

/-- The allocation is an actual partition of the full certified evaluation domain. -/
theorem production_allocation_cover :
    productionCommonRoots ∪ productionCovered ∪ productionUncovered = productionDomain := by
  simpa only [productionCommonRoots, productionCovered, productionUncovered, productionDomain,
    show 8 * (2 ^ 27) = 2 ^ 30 by norm_num] using
      fiberBlocks_three_cover g (2 ^ 27) productionRootCount productionCoveredCount
        productionUncoveredCount production_allocation_arithmetic.1

theorem production_allocation_disjoint :
    Disjoint productionCommonRoots productionCovered ∧
    Disjoint productionCommonRoots productionUncovered ∧
    Disjoint productionCovered productionUncovered := by
  have hsum := production_allocation_arithmetic.1
  have hroot : ∀ j, 0 + productionRootCount j ≤ 2 ^ 27 := by
    intro j
    have h := hsum j
    omega
  have hcovered : ∀ j, productionRootCount j + productionCoveredCount j ≤ 2 ^ 27 := by
    intro j
    have h := hsum j
    omega
  have huncovered : ∀ j, productionRootCount j + productionCoveredCount j +
      productionUncoveredCount j ≤ 2 ^ 27 := fun j => (hsum j).le
  refine ⟨?_, ?_, ?_⟩
  · exact fiberBlocks_disjoint g (2 ^ 27) production_fiber_order _ _ _ _
      hroot hcovered (fun j => by omega)
  · exact fiberBlocks_disjoint g (2 ^ 27) production_fiber_order _ _ _ _
      hroot huncovered (fun j => by omega)
  · exact fiberBlocks_disjoint g (2 ^ 27) production_fiber_order _ _ _ _
      hcovered huncovered (fun _ => le_rfl)

end AstraMcaPowerFibers

#print axioms AstraMcaPowerFibers.eightFiberEquiv
#print axioms AstraMcaPowerFibers.fiberPoint_injective
#print axioms AstraMcaPowerFibers.powerFiber_card
#print axioms AstraMcaPowerFibers.powerFiber_cover
#print axioms AstraMcaPowerFibers.powerFiber_disjoint
#print axioms AstraMcaPowerFibers.orderOf_fiber_generator
#print axioms AstraMcaPowerFibers.mem_powerFiber_iff
#print axioms AstraMcaPowerFibers.fiberBlock_card
#print axioms AstraMcaPowerFibers.fiberBlocks_card
#print axioms AstraMcaPowerFibers.fiberBlocks_disjoint
#print axioms AstraMcaPowerFibers.fiberBlocks_three_cover
#print axioms AstraMcaPowerFibers.production_fiber_card
#print axioms AstraMcaPowerFibers.production_fibers_cover
#print axioms AstraMcaPowerFibers.production_fiber_mem_iff
#print axioms AstraMcaPowerFibers.production_common_roots_two_prefixes
#print axioms AstraMcaPowerFibers.production_common_roots_card
#print axioms AstraMcaPowerFibers.production_covered_card
#print axioms AstraMcaPowerFibers.production_uncovered_card
#print axioms AstraMcaPowerFibers.production_allocation_cover
#print axioms AstraMcaPowerFibers.production_allocation_disjoint
