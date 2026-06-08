/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity

/-!
# Query-round soundness amplification

The probabilistic core of the FRI / Batched-FRI query phase (Claim 8.2, issue #14): `m`
*independent* query rounds amplify a per-round acceptance probability `p` to `pᵐ`.  If on each
round the verifier accepts only when the query lands in an "accept" set `A` of density `≤ p`
inside the query domain `dom`, then the fraction of fully-accepting `m`-round transcripts is at
most `pᵐ`.

* `accept_transcripts_card` — there are exactly `|A|ᵐ` all-accepting `m`-round transcripts.
* `accept_transcripts_card_le` — hence `≤ kᵐ` when `|A| ≤ k`.
* `accept_density_le` — the real-valued soundness bound: all-accept count `≤ pᵐ · |dom|ᵐ`
  when `|A| ≤ p·|dom|`, i.e. acceptance probability `≤ pᵐ`.
-/

open Finset

namespace ArkLib.QueryRound

variable {α : Type*} [DecidableEq α]

/-- The number of `m`-round transcripts that accept on every round (each query lands in `A`) is
exactly `|A|ᵐ`. -/
theorem accept_transcripts_card (A : Finset α) (m : ℕ) :
    (Fintype.piFinset (fun _ : Fin m => A)).card = A.card ^ m :=
  Finset.card_piFinset_const A m

/-- If each round's accept set has size `≤ k`, at most `kᵐ` transcripts accept on every round. -/
theorem accept_transcripts_card_le (A : Finset α) (m k : ℕ) (hA : A.card ≤ k) :
    (Fintype.piFinset (fun _ : Fin m => A)).card ≤ k ^ m := by
  rw [accept_transcripts_card]
  exact Nat.pow_le_pow_left hA m

/-- **Query-round amplification (soundness bound).**  If the per-round accept set `A` has
density at most `p` in the query domain `dom` (`|A| ≤ p·|dom|`, `0 ≤ p`), then the number of
fully-accepting `m`-round transcripts is at most `pᵐ` times the total `|dom|ᵐ` — i.e. the
all-rounds acceptance probability is at most `pᵐ`. -/
theorem accept_density_le (A dom : Finset α) (m : ℕ) (p : ℝ)
    (hp : (A.card : ℝ) ≤ p * dom.card) :
    ((Fintype.piFinset (fun _ : Fin m => A)).card : ℝ)
      ≤ p ^ m * ((Fintype.piFinset (fun _ : Fin m => dom)).card : ℝ) := by
  rw [accept_transcripts_card, accept_transcripts_card]
  push_cast
  calc (A.card : ℝ) ^ m
      ≤ (p * dom.card) ^ m := by
        gcongr
        exact Nat.cast_nonneg _
    _ = p ^ m * (dom.card : ℝ) ^ m := by rw [mul_pow]

end ArkLib.QueryRound
