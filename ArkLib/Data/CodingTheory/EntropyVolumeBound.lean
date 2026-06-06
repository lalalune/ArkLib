/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Logb
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

The single genuinely-analytic step here is the **entropy algebra**: clearing the `q`-ary
entropy into the binomial mode term,

  `q ^ (n · H_q(k/n)) · (k^k · (n-k)^{n-k}) = (q-1)^k · n^n`,

which is `entropy_rpow_eq` below. Combining it with the ℕ core (cast to `ℝ`) gives the
per-term bound `choose_pow_ge_qEntropy`, and then the single-term Hamming-ball volume lower
bound (`hammingBallVolume_real_ge_term_of_le_floor`) lifts it to the volume form
`hammingBallVolume_ge_qEntropy`.

All declarations are `sorry`/`axiom`-free and axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

namespace CodingTheory

open Real

variable {q : ℕ}

section EntropyAlgebra

variable (hq : 2 ≤ q)

/-- The entropy-clearing identity (the only genuinely-analytic step).  For `2 ≤ q`,
`0 < k`, `k < n`, with `x := k/n`:

  `q ^ (n · H_q(k/n)) · (k^k · (n-k)^{n-k}) = (q-1)^k · n^n`.

This turns the `q`-ary entropy into the entropy-free binomial mode term, after which the
combinatorial core `npow_le_succ_mul_choose_mul_pow` discharges the inequality. -/
theorem entropy_rpow_eq (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ)))
        * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))
      = ((q : ℝ) - 1) ^ k * (n : ℝ) ^ n := by
  -- Numeric facts.
  have hq0 : (0 : ℝ) < (q : ℝ) := by positivity
  have hq1' : (1 : ℝ) < (q : ℝ) := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hq1 : (q : ℝ) ≠ 1 := ne_of_gt hq1'
  have hqsub0 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have hn0 : (0 : ℝ) < (n : ℝ) := by positivity
  have hn0' : (n : ℝ) ≠ 0 := ne_of_gt hn0
  have hk0' : (0 : ℝ) < (k : ℝ) := by positivity
  set m : ℕ := n - k with hmdef
  have hm0 : 0 < m := by omega
  have hmR : (m : ℝ) = (n : ℝ) - (k : ℝ) := by
    rw [hmdef, Nat.cast_sub (le_of_lt hkn)]
  have hm0R : (0 : ℝ) < (m : ℝ) := by rw [hmR]; have : (k:ℝ) < (n:ℝ) := by exact_mod_cast hkn; linarith
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
      hpow ((k : ℝ) / (n : ℝ)) k (by positivity),
      hpow ((m : ℝ) / (n : ℝ)) m (by positivity),
      div_pow, div_pow]
  -- Now a pure field identity; clear denominators (`k^k, m^m, n^k, n^m ≠ 0`) and use `n^k·n^m=n^n`.
  rw [← hmR]
  have hnk0 : (n : ℝ) ^ k ≠ 0 := by positivity
  have hnm0 : (n : ℝ) ^ m ≠ 0 := by positivity
  have hkk0 : (k : ℝ) ^ k ≠ 0 := by positivity
  have hmm0 : (m : ℝ) ^ m ≠ 0 := by positivity
  have hnn : (n : ℝ) ^ k * (n : ℝ) ^ m = (n : ℝ) ^ n := by
    rw [← pow_add, hkmn]
  field_simp
  rw [hnn]
  ring

end EntropyAlgebra

/-- **Per-term q-ary entropy bound (the core of ABF26 C3.8).**  For `2 ≤ q`, `0 < k`, `k < n`:

  `q ^ (n · H_q(k/n)) ≤ (n + 1) · C(n,k) · (q-1)^k`.

Obtained from the entropy-clearing identity `entropy_rpow_eq` and the entropy-free
combinatorial mode bound `npow_le_succ_mul_choose_mul_pow`. -/
theorem choose_pow_ge_qEntropy (hq : 2 ≤ q) (n k : ℕ) (hk0 : 0 < k) (hkn : k < n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ)))
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k) := by
  have hkle : k ≤ n := le_of_lt hkn
  have hqsub0 : (0 : ℝ) ≤ ((q : ℝ) - 1) ^ k := by
    have : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
    positivity
  -- Positivity of the denominator `k^k · (n-k)^{n-k}`.
  have hk0' : (0 : ℝ) < (k : ℝ) ^ k := by positivity
  have hmnR : (0 : ℝ) < ((n - k : ℕ) : ℝ) ^ (n - k) := by
    have : 0 < n - k := by omega
    have : (0 : ℝ) < ((n - k : ℕ) : ℝ) := by positivity
    positivity
  have hden0 : (0 : ℝ) < (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) := mul_pos hk0' hmnR
  -- The ℕ core, cast to ℝ:  `n^n ≤ (n+1) · (C(n,k) · k^k · (n-k)^{n-k})`.
  have hcore : (n : ℝ) ^ n
      ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by
    have h := npow_le_succ_mul_choose_mul_pow n k hkle
    have hcast : (n ^ n : ℝ)
        ≤ ((n + 1 : ℕ) : ℝ) * ((n.choose k * k ^ k * (n - k) ^ (n - k) : ℕ) : ℝ) := by
      exact_mod_cast h
    push_cast at hcast
    convert hcast using 2 <;> ring
  -- Reduce the goal to the ℕ core by multiplying through by the positive denominator.
  rw [← entropy_rpow_eq hq n k hk0 hkn] at *
  refine le_of_mul_le_mul_right ?_ hden0
  calc
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ)))
        * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))
        = ((q : ℝ) - 1) ^ k * (n : ℝ) ^ n := entropy_rpow_eq hq n k hk0 hkn
    _ ≤ ((q : ℝ) - 1) ^ k
          * (((n : ℝ) + 1) * ((n.choose k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k))) :=
        mul_le_mul_of_nonneg_left hcore hqsub0
    _ = ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k)
          * ((k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k)) := by ring

/-- **The q-ary Hamming-ball entropy-volume lower bound (ABF26 Corollary 3.8, `/(n+1)` form).**

For `2 ≤ q`, and `δ` with mode index `k := ⌊δ·n⌋` satisfying `0 < k < n`:

  `q ^ (n · H_q(k/n)) ≤ (n + 1) · Vol_q(δ, n)`.

This is the bridge from `qEntropy` to `hammingBallVolume` required by the CS25 / ABF26 T4.17
breakdown band (issue #82).  It keeps a single mode summand of the volume
(`hammingBallVolume_real_ge_term_of_le_floor`) and bounds it below by the per-term entropy
estimate `choose_pow_ge_qEntropy`. -/
theorem hammingBallVolume_ge_qEntropy (hq : 2 ≤ q) (δ : ℝ) (n : ℕ)
    (hk0 : 0 < ⌊δ * n⌋₊) (hkn : ⌊δ * n⌋₊ < n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((⌊δ * n⌋₊ : ℝ) / (n : ℝ)))
      ≤ ((n : ℝ) + 1) * (hammingBallVolume q δ n : ℝ) := by
  set k : ℕ := ⌊δ * n⌋₊ with hkdef
  -- `((q-1 : ℕ) : ℝ) = (q : ℝ) - 1`, since `1 ≤ q`.
  have hqcast : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ q)]; norm_num
  -- The single mode summand `C(n,k)·(q-1)^k` lower-bounds the volume.
  have hterm : ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k) ≤ (hammingBallVolume q δ n : ℝ) := by
    have h := hammingBallVolume_real_ge_term_of_le_floor q δ n k (le_refl _)
    rw [← hkdef] at h
    -- Rearrange the cast: `((C(n,k) * (q-1)^k : ℕ) : ℝ) = C(n,k) * ((q:ℝ)-1)^k`.
    have hcast : ((Nat.choose n k * (q - 1) ^ k : ℕ) : ℝ)
        = (n.choose k : ℝ) * ((q : ℝ) - 1) ^ k := by
      push_cast [hqcast]
    rw [hcast] at h
    exact h
  -- Chain with the per-term entropy bound.
  have hpos : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  calc
    (q : ℝ) ^ ((n : ℝ) * qEntropy q ((k : ℝ) / (n : ℝ)))
        ≤ ((n : ℝ) + 1) * ((n.choose k : ℝ) * ((q : ℝ) - 1) ^ k) :=
      choose_pow_ge_qEntropy hq n k hk0 hkn
    _ ≤ ((n : ℝ) + 1) * (hammingBallVolume q δ n : ℝ) :=
      mul_le_mul_of_nonneg_left hterm hpos

end CodingTheory

-- Axiom audit: every declaration depends on exactly `[propext, Classical.choice, Quot.sound]`.
#print axioms CodingTheory.entropy_rpow_eq
#print axioms CodingTheory.choose_pow_ge_qEntropy
#print axioms CodingTheory.hammingBallVolume_ge_qEntropy
