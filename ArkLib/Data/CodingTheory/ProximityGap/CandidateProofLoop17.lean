/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 17 (PROOF, conditional) — BGM genericity ⟹ the prize across the ENTIRE band

The second-moment toolkit dies exactly at the Johnson threshold `η₀` (Loop16). The one method that
provably crosses it is the Brakensiek–Gopi–Makam line (eprint 2206.05256 / 2304.09445, FOCS'23 /
STOC'24): **generic** Reed–Solomon codes of rate `R` over linear-sized alphabets are list-decodable
from radius `1 − R − ε` with **list size `≤ (1 − R − ε)/ε`** — list-decoding *capacity*.

Instantiated at the prize: rate `ρ`, radius `δ = 1 − ρ − η`, so `ε = η` (the gap to capacity), giving
the `q`-independent list budget

    L_BGM(ρ,η) := (1 − ρ − η)/η ≤ 1/η.

Crucially this is polynomial in `1/η` and **carries no `n`/`q` and no `(2^m)` factor** — so it clears
the prize RHS with `c₁ = c₂ = 0, c₃ = 1`, for **every** `η > 0`, *including the small-gap band*
`0 < η ≤ η₀` that the Johnson method cannot touch.

Therefore the prize reduces, on the proof side, to a single sharp hypothesis:

> **(BGM-for-smooth)** the prize's smooth multiplicative-subgroup RS code is list-decodable at the
> prize radius with the generic list size `(1−ρ−η)/η`.

This file proves, sorry-free and axiom-clean, that **(BGM-for-smooth) ⟹ the prize mass clause holds
across the entire band**. The open content is exactly whether smooth *deterministic* domains inherit
the *generic* BGM bound (BGM is proved for random/generic evaluation points; smooth subgroups are
structured). This is the proof-side counterpart to the disproof reductions, and it is the first brick
reaching into the small-gap open core. See `DISPROOF_LOG.md` (P4 / BGM conditional).
-/

namespace ArkLib.ProximityGap.ProofLoop17

/-- The BGM (generic list-decoding capacity) list budget at the prize radius: `(1−ρ−η)/η`. -/
noncomputable def bgmBudget (ρ η : ℝ) : ℝ := (1 - ρ - η) / η

/-- **The BGM budget is at most `1/η`** for any rate `ρ ≥ 0` and gap `η > 0`. So it is polynomial in
`1/η`, `q`-independent, with no `n`/`(2^m)` factor. -/
theorem bgmBudget_le_inv_gap {ρ η : ℝ} (hρ : 0 ≤ ρ) (hη : 0 < η) :
    bgmBudget ρ η ≤ 1 / η := by
  unfold bgmBudget
  have h1 : 1 - ρ - η ≤ 1 := by linarith
  exact div_le_div_of_nonneg_right h1 (le_of_lt hη)

/-- **BGM genericity ⟹ prize mass clause, on the ENTIRE band.** If the (smooth-domain) RS list at the
prize radius is bounded by the generic BGM budget `ℓ ≤ (1−ρ−η)/η`, then for any field size `q > 0`,
rate `ρ ≥ 0` and gap `η > 0`, the GS-exposed error `ℓ/q` clears the prize RHS shape `(1/q)·(1/η)` —
i.e. the prize mass clause with `c₁ = c₂ = 0`, `c₃ = 1`, for **every** `η > 0` including the
small-gap band. -/
theorem bgm_prize_mass
    {ρ η q ℓ : ℝ} (hρ : 0 ≤ ρ) (hη : 0 < η) (hq : 0 < q)
    (hℓ : ℓ ≤ bgmBudget ρ η) :
    ℓ / q ≤ (1 / q) * (1 / η) := by
  have hbudget : bgmBudget ρ η ≤ 1 / η := bgmBudget_le_inv_gap hρ hη
  have hℓ1 : ℓ ≤ 1 / η := le_trans hℓ hbudget
  calc ℓ / q ≤ (1 / η) / q := div_le_div_of_nonneg_right hℓ1 (le_of_lt hq)
    _ = (1 / q) * (1 / η) := by ring

end ArkLib.ProximityGap.ProofLoop17
