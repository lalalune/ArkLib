/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
/-
Round 15 (own grind) — the EXACT-COUNT GS wall: the upper bound on the weighted-degree monomial
count, and the resulting necessary condition for exact-count GS feasibility.
Self-contained, Mathlib-only.
-/
import Mathlib.Tactic

open Finset

namespace GSExactWall

variable {c D : ℕ}

/-- The exact `(1,c)`-weighted-degree monomial count (with `c = k − 1`):
`gsCount c D = #{(i,j) : i + c·j < D} = ∑_{j<D} (D − c·j)` (truncated subtraction;
terms with `c·j ≥ D` vanish). This matches the `gsSupport` cardinality used by the
in-tree interpolation-existence front end. -/
def gsCount (c D : ℕ) : ℕ := ∑ j ∈ Finset.range D, (D - c * j)

/-- The number of genuinely contributing indices: `q = ⌈D/c⌉ = (D + c − 1)/c`. -/
def qIdx (c D : ℕ) : ℕ := (D + c - 1) / c

theorem qIdx_le (hc : 0 < c) : c * qIdx c D ≤ D + c - 1 := by
  rw [qIdx, Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

theorem qIdx_ge (hc : 0 < c) (hD : 0 < D) : D ≤ c * qIdx c D := by
  rw [qIdx]
  have hdm := Nat.div_add_mod (D + c - 1) c
  have hml : (D + c - 1) % c < c := Nat.mod_lt _ hc
  omega

theorem qIdx_le_D (hc : 0 < c) (hD : 0 < D) : qIdx c D ≤ D := by
  by_contra hcon
  have hq : D + 1 ≤ qIdx c D := by omega
  have h3 : c * (D + 1) ≤ c * qIdx c D := Nat.mul_le_mul_left c hq
  have h4 : D ≤ c * D := Nat.le_mul_of_pos_left D hc
  have h1 := qIdx_le (D := D) hc
  rw [Nat.mul_add, Nat.mul_one] at h3
  omega

/-- Terms with index `≥ q` vanish: the sum over `range D` equals the sum over `range q`. -/
theorem gsCount_eq_sum_q (hc : 0 < c) (hD : 0 < D) :
    gsCount c D = ∑ j ∈ Finset.range (qIdx c D), (D - c * j) := by
  rw [gsCount]
  symm
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_range] at hj ⊢
    exact lt_of_lt_of_le hj (qIdx_le_D hc hD)
  · intro j _ hj
    rw [Finset.mem_range] at hj
    have hj' : qIdx c D ≤ j := by omega
    have h1 : c * qIdx c D ≤ c * j := Nat.mul_le_mul_left c hj'
    have h2 := qIdx_ge hc hD
    omega

/-- **The exact-count UPPER bound (the new content; the in-tree lower bound is `D² < 2c·count`).**
`2c · gsCount(c,D) ≤ (D + c)²`. Proof: the genuine terms sum to `qD − c·q(q−1)/2` (Gauss), and with
`u = cq ∈ [D, D+c−1]`, `2c·Σ = u(2D + c − u) ≤ ((2D+c)/2)² ≤ (D+c)²` (AM–GM). -/
theorem two_c_gsCount_le (hc : 0 < c) (hD : 0 < D) :
    2 * c * gsCount c D ≤ (D + c) ^ 2 := by
  rw [gsCount_eq_sum_q hc hD]
  set q := qIdx c D with hq
  -- each genuine term has c·j < D (no truncation)
  have hterm : ∀ j ∈ Finset.range q, c * j < D := by
    intro j hj
    rw [Finset.mem_range] at hj
    have hj' : j + 1 ≤ q := by omega
    have h1 : c * (j + 1) ≤ c * q := Nat.mul_le_mul_left c hj'
    have h2 := qIdx_le (D := D) hc
    rw [← hq] at h2
    rw [Nat.mul_add, Nat.mul_one] at h1
    omega
  -- compute the doubled sum exactly over ℤ
  have hgauss : (2 * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ)
      = 2 * q * D - c * (q * (q - 1)) := by
    have hcast : ((∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ)
        = ∑ j ∈ Finset.range q, ((D : ℤ) - c * j) := by
      rw [Nat.cast_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have h := hterm j hj
      rw [Nat.cast_sub (le_of_lt h)]
      push_cast
      ring
    rw [hcast, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, ← Finset.mul_sum,
        nsmul_eq_mul]
    have hgsum : (∑ j ∈ Finset.range q, (j : ℤ)) * 2 = q * ((q : ℤ) - 1) := by
      have h := Finset.sum_range_id_mul_two q
      rcases Nat.eq_zero_or_pos q with hq0 | hq0
      · rw [hq0]; simp
      · calc (∑ j ∈ Finset.range q, (j : ℤ)) * 2
            = (((∑ j ∈ Finset.range q, j) * 2 : ℕ) : ℤ) := by push_cast [Nat.cast_sum]; ring
          _ = ((q * (q - 1) : ℕ) : ℤ) := by rw [h]
          _ = q * ((q : ℤ) - 1) := by
              push_cast [Nat.cast_sub (by omega : 1 ≤ q)]
              ring
    linear_combination (-(c : ℤ)) * hgsum
  -- the AM–GM endgame over ℤ with u = c·q ∈ [D, D+c−1]
  have hu_ge : (D : ℤ) ≤ c * q := by
    have h := qIdx_ge hc hD
    rw [← hq] at h
    exact_mod_cast h
  have hu_le : (c * q : ℤ) ≤ (D : ℤ) + c - 1 := by
    have h := qIdx_le (D := D) hc
    rw [← hq] at h
    have h' : ((c * q : ℕ) : ℤ) ≤ ((D + c - 1 : ℕ) : ℤ) := Nat.cast_le.mpr h
    have hDc : 1 ≤ D + c := by omega
    rw [Nat.cast_sub hDc] at h'
    push_cast at h' ⊢
    omega
  -- 2c·Σ = u(2D + c − u) ≤ (D+c)²
  have hexp : (2 * c * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ)
      = (c * q) * (2 * D + c - c * q) := by
    have h2 : (2 * c * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ)
        = c * (2 * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ) := by ring
    rw [h2, hgauss]
    ring
  have hmain : (2 * c * (∑ j ∈ Finset.range q, (D - c * j) : ℕ) : ℤ) ≤ ((D : ℤ) + c) ^ 2 := by
    rw [hexp]
    nlinarith [sq_nonneg ((2 * (D : ℤ) + c) - 2 * (c * q)), sq_nonneg ((D : ℤ) - c)]
  exact_mod_cast hmain

/-- **The exact-count GS wall (necessary condition).**  If the exact-count GS system is feasible —
some weighted-degree budget `D` satisfies BOTH the (doubled) constraint excess
`n·m·(m+1) < 2·gsCount(c,D)` AND the root-order condition `D < t·m` — then

  `n · c · m · (m+1) < (t·m + c)²`.

So the agreement threshold obeys `t·m + c > √(n·c·m·(m+1))`: the exact-lattice-count system has the
same `√(c·n)`-asymptotics as the `D²`-form wall (`GSJohnsonWall`), with the explicit `+c` slack
(`c = k−1`) quantifying exactly how far below the `D²`-form threshold the exact count can reach. -/
theorem exact_wall {c n m t : ℕ} (hc : 0 < c)
    (hfeas : ∃ D, 0 < D ∧ n * m * (m + 1) < 2 * gsCount c D ∧ D < t * m) :
    n * c * m * (m + 1) < (t * m + c) ^ 2 := by
  obtain ⟨D, hD, hcount, hroot⟩ := hfeas
  have h1 : c * (n * m * (m + 1)) < c * (2 * gsCount c D) :=
    (Nat.mul_lt_mul_left hc).mpr hcount
  have h2 : c * (2 * gsCount c D) = 2 * c * gsCount c D := by ring
  have h3 := two_c_gsCount_le hc hD
  have h4 : (D + c) ^ 2 ≤ (t * m + c - 1) ^ 2 := by
    apply Nat.pow_le_pow_left
    omega
  have h5 : (t * m + c - 1) ^ 2 < (t * m + c) ^ 2 := by
    apply Nat.pow_lt_pow_left
    · omega
    · norm_num
  calc n * c * m * (m + 1) = c * (n * m * (m + 1)) := by ring
    _ < 2 * c * gsCount c D := by omega
    _ ≤ (D + c) ^ 2 := h3
    _ ≤ (t * m + c - 1) ^ 2 := h4
    _ < (t * m + c) ^ 2 := h5

/-- **Square-root form of the wall:** `√(n·c·m·(m+1)) < t·m + c`. -/
theorem exact_wall_sqrt {c n m t : ℕ} (hc : 0 < c)
    (hfeas : ∃ D, 0 < D ∧ n * m * (m + 1) < 2 * gsCount c D ∧ D < t * m) :
    Nat.sqrt (n * c * m * (m + 1)) < t * m + c := by
  rw [Nat.sqrt_lt']
  nlinarith [exact_wall hc hfeas]

/-! ## Concrete instances: where the exact count reaches below the `D²`-form threshold —
and where it still cannot go (`n = 100, c = 25` (`k = 26`), `m = 1`; Johnson `= √2500 = 50`). -/

/-- At `t = 60` the exact-count system IS feasible: `D = 59` gives
`gsCount 25 59 = 59 + 34 + 9 = 102`, and `n·m·(m+1) = 200 < 204 = 2·102`, with `59 < 60`.
(The `D²`-form threshold would demand `t ≥ 72`: the exact count genuinely reaches lower.) -/
theorem exact_feasible_t60 :
    ∃ D, 0 < D ∧ 100 * 1 * (1 + 1) < 2 * gsCount 25 D ∧ D < 60 * 1 := by
  refine ⟨59, by norm_num, ?_, by norm_num⟩
  have h : gsCount 25 59 = 102 := by decide
  rw [h]
  norm_num

/-- At `t = 59` the exact-count system is INFEASIBLE: every admissible `D ≤ 58` has
`2·gsCount 25 D ≤ 2·gsCount 25 58 = 198 ≤ 200 = n·m·(m+1)` (monotonicity + finite check). -/
theorem exact_infeasible_t59 :
    ¬ ∃ D, 0 < D ∧ 100 * 1 * (1 + 1) < 2 * gsCount 25 D ∧ D < 59 * 1 := by
  rintro ⟨D, hD, hcount, hroot⟩
  have hD58 : D ≤ 58 := by omega
  have hmono : gsCount 25 D ≤ gsCount 25 58 := by
    rw [gsCount, gsCount]
    calc ∑ j ∈ Finset.range D, (D - 25 * j)
        ≤ ∑ j ∈ Finset.range D, (58 - 25 * j) :=
          Finset.sum_le_sum (fun j _ => by omega)
      _ ≤ ∑ j ∈ Finset.range 58, (58 - 25 * j) := by
          apply Finset.sum_le_sum_of_subset
          intro x hx
          rw [Finset.mem_range] at hx ⊢
          omega
  have h58 : gsCount 25 58 = 99 := by decide
  omega

/-- **The wall holds at the feasible point** (consistency check of `exact_wall`):
`n·c·m·(m+1) = 5000 < 7225 = (60·1 + 25)²`, while Johnson is `√(n·c) = 50 < 60`.
The exact count reaches `t = 60` — below the `D²`-form's `72`, **still above Johnson's `50`.** -/
theorem wall_consistency : 100 * 25 * 1 * (1 + 1) < (60 * 1 + 25) ^ 2 ∧ 50 * 50 = 100 * 25 := by
  norm_num

end GSExactWall

#print axioms GSExactWall.two_c_gsCount_le
#print axioms GSExactWall.exact_wall
#print axioms GSExactWall.exact_wall_sqrt
#print axioms GSExactWall.exact_feasible_t60
#print axioms GSExactWall.exact_infeasible_t59
#print axioms GSExactWall.wall_consistency
