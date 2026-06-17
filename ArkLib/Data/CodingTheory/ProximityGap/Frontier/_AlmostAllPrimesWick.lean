/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Almost-all-primes Wick helper — distinct-prime-factor count ≤ `log₂`

Minimal provider for `Frontier/_BchksF4_GoodPrimeLinnik.lean`, which consumes
`AlmostAllPrimesWick.card_primeFactors_le_natLog` to bound the per-pair bad-prime set
(`#(primeFactors |N|) ≤ log₂ |N|`).

Recovery note: the `_AlmostAllPrimesWick.lean` that commit `4a1b8dee4` imported was never
`git add`-ed — it is absent from every branch, commit, and PR (so the build of `_BchksF4`
and of `main` itself failed with `no such file … _AlmostAllPrimesWick.lean`). This file
re-derives, from scratch, exactly the one lemma the consumer needs: the classical
`ω(n) ≤ log₂ n`. Axiom-clean, no `sorry`.
-/

namespace ArkLib.ProximityGap.Frontier.AlmostAllPrimesWick

/-- **Distinct prime factors are at most `log₂`.** For `n ≥ 1`, the number of distinct prime
factors of `n` is at most `Nat.log 2 n`, since `2 ^ ω(n) ≤ ∏_{p ∈ primeFactors n} p ≤ n`. -/
theorem card_primeFactors_le_natLog {n : ℕ} (h : 1 ≤ n) :
    n.primeFactors.card ≤ Nat.log 2 n := by
  have hpos : 0 < n := h
  have hprod : 2 ^ n.primeFactors.card ≤ ∏ p ∈ n.primeFactors, p :=
    Finset.pow_card_le_prod n.primeFactors (fun p => p) 2
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have hdvd : (∏ p ∈ n.primeFactors, p) ≤ n :=
    Nat.le_of_dvd hpos (Nat.prod_primeFactors_dvd n)
  have hpow : 2 ^ n.primeFactors.card ≤ n := le_trans hprod hdvd
  exact Nat.le_log_of_pow_le (b := 2) (by decide) hpow

end ArkLib.ProximityGap.Frontier.AlmostAllPrimesWick
