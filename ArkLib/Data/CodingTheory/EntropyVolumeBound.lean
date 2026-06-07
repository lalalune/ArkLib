/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import ArkLib.Data.CodingTheory.BinomialEntropyBound
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume

/-!
# The q-ary entropy / Hamming-ball volume lower bound (ABF26 Corollary 3.8)

This file discharges the genuine *real-valued* q-ary entropy-volume bound — the bridge
connecting `qEntropy` (ABF26 Def 2.2) to `hammingBallVolume` (ABF26 Def 2.4) that the CS25 /
ABF26 T4.17 `epsCA` breakdown analysis (issue #82) needs:

  `q ^ (n · H_q(δ))  ≤  (n + 1) · Vol_q(δ, n)`           (the easy `/(n+1)` form).

The proof rests on the entropy-free combinatorial core
`CodingTheory.npow_le_succ_mul_choose_mul_pow` (`BinomialEntropyBound.lean`):

  `n^n ≤ (n + 1) · C(n,k) · k^k · (n-k)^{n-k}`.

The single genuinely-analytic step here is the **entropy algebra** (`entropy_rpow_eq`):

  `q ^ (n · H_q(k/n)) · (k^k · (n-k)^{n-k}) = (q-1)^k · n^n`,

which clears the `q`-ary entropy into the binomial mode term. Combining it with the ℕ core
(cast to `ℝ`) gives the per-term bound `choose_pow_ge_qEntropy`, and the single-term
Hamming-ball volume lower bound (`hammingBallVolume_real_ge_term_of_le_floor`) lifts it to the
volume form `hammingBallVolume_ge_qEntropy`.

All declarations are `sorry`/`axiom`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace CodingTheory

open Real

variable {q : ℕ}

/-- The entropy-clearing identity (the only genuinely-analytic step).  For `2 ≤ q`,
`0 < k`, `k < n`, with `x := k/n`:

  `q ^ (n · H_q(k/n)) · (k^k · (n-k)^{n-k}) = (q-1)^k · n^n`.

This turns the `q`-ary entropy into the entropy-free binomial mode term, after which the
combinatorial core `npow_le_succ_mul_choose_mul_pow` discharges the inequality. -/
theorem entropy_rpow_eq (hq : 2 ≤ q) (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ)))
        * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))
      = ((q : ℝ) - 1) ^ k * (n : ℝ) ^ n := by
  -- Numeric facts.
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) < (q : ℝ) := by exact_mod_cast (show 1 < q by omega)
  have hq1 : (q : ℝ) ≠ 1 := ne_of_gt hq1'
  have hqsub0 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn0' : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hk0' : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  set m : ℕ := n - k with hmdef
  have hm0 : 0 < m := by omega
  have hm0R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hmR : (m : ℝ) = (n : ℝ) - (k : ℝ) := by
    rw [hmdef, Nat.cast_sub (le_of_lt hkn)]
  have hkmn : k + m = n := by omega
  -- The reusable `rpow ∘ logb` collapse: `q ^ (j · logb q b) = b ^ j`.
  have hpow : ∀ (b : ℝ) (j : ℕ), 0 < b →
      (q : ℝ) ^ ((j : ℝ) * Real.logb (q : ℝ) b) = b ^ j := by
    intro b j hb
    rw [mul_comm (j : ℝ) (Real.logb (q : ℝ) b),
        Real.rpow_mul hq0.le, Real.rpow_logb hq0 hq1 hb, Real.rpow_natCast]
  -- The `1 - k/n = m/n` rewrite.
  have h1x : (1 : ℝ) - (k : ℝ) / (n : ℝ) = (m : ℝ) / (n : ℝ) := by
    rw [hmR]; field_simp
  -- Reduce `n · H_q(k/n)` to the three-term logb combination.
  have hexp : (n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ))
      = (k : ℝ) * Real.logb (q : ℝ) ((q : ℝ) - 1)
        - (k : ℝ) * Real.logb (q : ℝ) ((k : ℝ) / (n : ℝ))
        - (m : ℝ) * Real.logb (q : ℝ) ((m : ℝ) / (n : ℝ)) := by
    unfold qEntropy
    rw [h1x]
    set A := Real.logb (q : ℝ) ((q : ℝ) - 1)
    set B := Real.logb (q : ℝ) ((k : ℝ) / (n : ℝ))
    set C := Real.logb (q : ℝ) ((m : ℝ) / (n : ℝ))
    field_simp
    ring
  -- Expand `q ^ (n · H)` via the rpow split.
  rw [hexp, Real.rpow_sub hq0, Real.rpow_sub hq0,
      hpow ((q : ℝ) - 1) k hqsub0,
      hpow ((k : ℝ) / (n : ℝ)) k (div_pos hk0' hn0),
      hpow ((m : ℝ) / (n : ℝ)) m (div_pos hm0R hn0),
      div_pow, div_pow]
  -- Pure field identity; clear denominators and use `n^k · n^m = n^n`.
  have hnk0 : (n : ℝ) ^ k ≠ 0 := by positivity
  have hnm0 : (n : ℝ) ^ m ≠ 0 := by positivity
  have hkk0 : (k : ℝ) ^ k ≠ 0 := pow_ne_zero _ (ne_of_gt hk0')
  have hmm0 : (m : ℝ) ^ m ≠ 0 := pow_ne_zero _ (ne_of_gt hm0R)
  have hnn : (n : ℝ) ^ k * (n : ℝ) ^ m = (n : ℝ) ^ n := by
    rw [← pow_add, hkmn]
  rw [← hnn]
  field_simp
  ring

/-- **Per-term q-ary entropy bound (the core of ABF26 C3.8).**  For `2 ≤ q`, `0 < k`, `k < n`:

  `q ^ (n · H_q(k/n)) ≤ (n + 1) · C(n,k) · (q-1)^k`.

Obtained from the entropy-clearing identity `entropy_rpow_eq` and the entropy-free
combinatorial mode bound `npow_le_succ_mul_choose_mul_pow`. -/
theorem choose_pow_ge_qEntropy (hq : 2 ≤ q) (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ)))
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k) := by
  have hkle : k ≤ n := le_of_lt hkn
  have hqsub_nonneg : (0 : ℝ) ≤ ((q : ℝ) - 1) ^ k := by
    have h1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    exact pow_nonneg (by linarith) k
  -- Positivity of the denominator `k^k · (n-k)^{n-k}`.
  have hk0' : (0 : ℝ) < (k : ℝ) ^ k := pow_pos (by exact_mod_cast hk0) k
  have hmnR : (0 : ℝ) < ((n - k : ℕ) : ℝ) ^ (n - k) :=
    pow_pos (by exact_mod_cast (show 0 < n - k by omega)) (n - k)
  have hden0 : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) := mul_pos hk0' hmnR
  -- The ℕ core, cast to ℝ:  `n^n ≤ (n+1) · (C(n,k) · k^k · (n-k)^{n-k})`.
  have hcore : (n : ℝ) ^ n
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    have h := npow_le_succ_mul_choose_mul_pow n k hkle
    calc (n : ℝ) ^ n = ((n ^ n : ℕ) : ℝ) := by push_cast; ring
      _ ≤ (((n + 1) * (n.choose k * k ^ k * (n - k) ^ (n - k)) : ℕ) : ℝ) := by exact_mod_cast h
      _ = ((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
          push_cast; ring
  -- Reduce to the ℕ core by multiplying through by the positive denominator.
  refine le_of_mul_le_mul_right ?_ hden0
  rw [entropy_rpow_eq hq n k hk0 hkn]
  calc ((q : ℝ) - 1) ^ k * (n : ℝ) ^ n
      ≤ ((q : ℝ) - 1) ^ k
          * (((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))) :=
        mul_le_mul_of_nonneg_left hcore hqsub_nonneg
    _ = ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k)
          * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by ring

/-- **The q-ary Hamming-ball entropy-volume lower bound (ABF26 Corollary 3.8, `/(n+1)` form).**

For `2 ≤ q`, and `δ` with mode index `k := ⌊δ·n⌋` satisfying `0 < k < n`:

  `q ^ (n · H_q(k/n)) ≤ (n + 1) · Vol_q(δ, n)`.

This is the bridge from `qEntropy` to `hammingBallVolume` required by the CS25 / ABF26 T4.17
breakdown band (issue #82): it keeps a single mode summand of the volume
(`hammingBallVolume_real_ge_term_of_le_floor`) and bounds it below by the per-term entropy
estimate `choose_pow_ge_qEntropy`. -/
theorem hammingBallVolume_ge_qEntropy (hq : 2 ≤ q) (δ : ℝ) (n : ℕ)
    (hk0 : 0 < ⌊δ * n⌋₊) (hkn : ⌊δ * n⌋₊ < n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((⌊δ * n⌋₊ : ℝ) / (n : ℝ)))
      ≤ ((n : ℝ) + 1) * (hammingBallVolume q δ n : ℝ) := by
  set k : ℕ := ⌊δ * (n : ℝ)⌋₊ with hk
  -- `((q-1 : ℕ) : ℝ) = (q : ℝ) - 1`, since `1 ≤ q`.
  have hqcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ q by omega)]; norm_num
  -- The single mode summand `C(n,k)·(q-1)^k` lower-bounds the volume.
  have hterm : ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k) ≤ (hammingBallVolume q δ n : ℝ) := by
    have h := hammingBallVolume_real_ge_term_of_le_floor q δ n k (le_of_eq hk)
    have hcast : ((Nat.choose n k * (q - 1) ^ k : ℕ) : ℝ)
        = (n.choose k : ℝ) * ((q : ℝ) - 1) ^ k := by push_cast [hqcast]; ring
    rw [hcast] at h
    exact h
  -- Chain with the per-term entropy bound.
  calc (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ)))
        ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k) :=
      choose_pow_ge_qEntropy hq n k hk0 hkn
    _ ≤ ((n : ℝ) + 1) * (hammingBallVolume q δ n : ℝ) :=
      mul_le_mul_of_nonneg_left hterm (by positivity)

end CodingTheory

-- Axiom audit: every declaration depends on exactly `[propext, Classical.choice, Quot.sound]`.
#print axioms CodingTheory.entropy_rpow_eq
#print axioms CodingTheory.choose_pow_ge_qEntropy
#print axioms CodingTheory.hammingBallVolume_ge_qEntropy
