/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CS25BreakdownFarCount

/-!
# CS25 #82: isolating the second moment

This file reduces the CS25 T4.17 residual `ε_ca(RS, δ) = 1` to a single **covering** inequality on
the number of words `δ`-close to the Reed–Solomon code, completing the wiring of the covered-set
machinery (`SupportSqBound`, `CS25SecondMomentReduction`).

`rs_epsCA_breakdown_cs25_of_close_lower` (part A): a purely combinatorial reduction — if

  `(|F|-1)·|ι→F|² + #{u : jointProx} < |F| · |ι→F| · #{w : δᵣ(w,RS) ≤ δ}`,

then `ε_ca(RS, δ) = 1`.  (The covered set carries more than a `(1 - 1/|F|)` fraction, with room for
the jointly-close stacks.)  Proof: the far count is the complement of the close count, the stack
count is `|ι→F|²`, and the arithmetic feeds `rs_epsCA_breakdown_cs25_of_far_count`.

The remaining input is the lower bound on `#{w : δᵣ(w,RS) ≤ δ}` — exactly what the Paley-Zygmund
covered-set bound `(|RS|·V)² ≤ |close| · E[N²]` produces from the second moment `E[N²]`.
-/

open scoped NNReal ProbabilityTheory BigOperators

namespace CodingTheory

open ProximityGap Code Finset

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The number of two-row stacks over `ι → F` equals `|ι→F|²`. -/
theorem card_wordStack_eq :
    Fintype.card (Code.WordStack F (Fin 2) ι)
      = Fintype.card (ι → F) * Fintype.card (ι → F) := by
  show Fintype.card (Fin 2 → ι → F) = Fintype.card (ι → F) * Fintype.card (ι → F)
  rw [Fintype.card_fun, Fintype.card_fin, pow_two]

open Classical in
/-- **CS25 complete breakdown from a covering lower bound (part A).** If the close count, scaled by
`|F| · |ι→F|`, strictly exceeds `(|F|-1)·|ι→F|²` plus the jointly-close stack count, then
`ε_ca(RS, δ) = 1`. -/
theorem rs_epsCA_breakdown_cs25_of_close_lower
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0)
    (hq_ge : 10 ≤ Fintype.card F)
    (hδ_lo :
        1 - qEntropy (Fintype.card F) (δ : ℝ) + 2 / (Fintype.card ι : ℝ)
            + ((qEntropy (Fintype.card F) (δ : ℝ) - (δ : ℝ))
                / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / 2)
          ≤ (k : ℝ) / Fintype.card ι)
    (hδ_hi : (k : ℝ) / Fintype.card ι ≤ 1 - (δ : ℝ) - 2 / (Fintype.card ι : ℝ))
    (hcov :
      (Fintype.card F - 1) * (Fintype.card (ι → F) * Fintype.card (ι → F))
          + (univ.filter (fun u : Code.WordStack F (Fin 2) ι =>
              Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)).card
        < Fintype.card F *
            (Fintype.card (ι → F) *
              (univ.filter (fun w : ι → F =>
                δᵣ(w, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card)) :
    rs_epsCA_breakdown_cs25 domain k δ hq_ge hδ_lo hδ_hi := by
  refine rs_epsCA_breakdown_cs25_of_far_count domain k δ hq_ge hδ_lo hδ_hi ?_
  rw [card_wordStack_eq]
  -- abbreviations
  set q := Fintype.card F with hq
  set N := Fintype.card (ι → F) with hNdef
  set close := (univ.filter (fun w : ι → F =>
      δᵣ(w, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card with hclose
  set far := (univ.filter (fun w : ι → F =>
      ¬ δᵣ(w, (ReedSolomon.code domain k : Set (ι → F))) ≤ δ)).card with hfar
  set jp := (univ.filter (fun u : Code.WordStack F (Fin 2) ι =>
      Code.jointProximity (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ)).card with hjp
  -- close + far = N
  have hpart : close + far = N := by
    rw [hclose, hfar, hNdef, ← Finset.card_univ]
    exact Finset.filter_card_add_filter_neg_card_eq_card _
  -- multiplicative identity feeding omega
  have hmul : q * (N * close) + q * (N * far) = q * (N * N) := by
    rw [← Nat.mul_add, ← Nat.mul_add, hpart]
  have hq1 : 1 ≤ q := by omega
  have hge : N * N ≤ q * (N * N) := Nat.le_mul_of_pos_left _ (by omega)
  -- (q-1)*(N*N) = q*(N*N) - N*N
  have hsub : (q - 1) * (N * N) = q * (N * N) - N * N := by
    rw [Nat.sub_mul, one_mul]
  rw [hsub] at hcov
  omega

end CodingTheory
