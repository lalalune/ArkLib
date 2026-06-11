/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckingVerifier

/-!
# The t-repetition STIR wire shape (#301, hypothesis A1, part 1)

The single-query wire model (`stirMultiVSpec`, challenge length `1`) provably cannot reach
paper-STIR's L5.4 budgets: the switch prover pins every valid rbr budget family at
`Σᵢ εᵢ ≥ 1 − (⌊δ|ι|⌋+1)/|F|` (the K4 fence; quantitative core in
`CheckingRbrTightnessCore`).  The honest path to genuine `2^{-secpar}` budgets is
**t-fold repetition per challenge**: each binding check samples `t` points, and the flip
probability becomes a product (`≤ ((|F| − D)/|F|)ᵗ`), supplied by the landed
product-marginal engine (`ArkLib.Data.Probability.ProductMarginal`,
`probEvent_uniform_vector_bind_le`) over the pass sets bounded by
`TightnessCore.pass_count_ge`.

This file lands the wire shape itself:

* `stirMultiVSpecT M ι t` — the `(3M+3)`-round STIR shape with `t`-point vector challenges
  (the challenge length was ALWAYS a parameter of `stirVSpec`; the single-query model pinned
  it to `1`);
* `stirMultiVSpecT_one` — at `t = 1` it is DEFINITIONALLY the landed `stirMultiVSpec`;
* the length lemmas (`_length_msg`, `_length_chal`, `_length_chal_pos`) mirroring the
  `t = 1` versions;
* `chalCoordT` — reading the `j`-th field element off a committed `t`-point vector
  challenge (the multi-point analogue of `chalFE`).

Next bricks (tracked on issue #301): the `t`-point checking computation (fold the
binding/consistency checks over all `t` coordinates), its `simulateQ` collapse and
completeness, and the door-die soundness re-run with product flip bounds.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

open ProtocolSpec

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι]

/-- **The t-repetition STIR multi-round wire shape**: `3M + 3` rounds, message length
`|ι|`, challenge length `t`. -/
def stirMultiVSpecT (M : ℕ) (ι : Type) [Fintype ι] (t : ℕ) :
    ProtocolSpec.VectorSpec (3 * M + 3) :=
  stirVSpec M (fun _ => Fintype.card ι) t

/-- At `t = 1` the repetition shape degenerates to the landed single-query shape,
definitionally. -/
@[simp] theorem stirMultiVSpecT_one (M : ℕ) :
    stirMultiVSpecT M ι 1 = stirMultiVSpec M ι := rfl

/-- Message rounds of `stirMultiVSpecT` have length `|ι|`. -/
theorem stirMultiVSpecT_length_msg {M t : ℕ}
    (i : ((stirMultiVSpecT M ι t).toProtocolSpec F).MessageIdx) :
    Fintype.card ι = (stirMultiVSpecT M ι t).length i.1 := by
  have h := i.2
  rw [show ((stirMultiVSpecT M ι t).toProtocolSpec F).dir i.1
      = (stirVSpec M (fun _ => Fintype.card ι) t).dir i.1 from rfl,
    stirVSpec_dir_eq_msg_iff] at h
  simp [stirMultiVSpecT, stirVSpec, h]

/-- Challenge rounds of `stirMultiVSpecT` have length `t`. -/
theorem stirMultiVSpecT_length_chal {M t : ℕ}
    (i : ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx) :
    (stirMultiVSpecT M ι t).length i.1 = t := by
  have h := i.2
  rw [show ((stirMultiVSpecT M ι t).toProtocolSpec F).dir i.1
      = (stirVSpec M (fun _ => Fintype.card ι) t).dir i.1 from rfl,
    stirVSpec_dir_eq_chal_iff] at h
  simp [stirMultiVSpecT, stirVSpec, h]

/-- Challenge rounds of `stirMultiVSpecT` have positive length when `t > 0`. -/
theorem stirMultiVSpecT_length_chal_pos {M t : ℕ} (ht : 0 < t)
    (i : ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx) :
    0 < (stirMultiVSpecT M ι t).length i.1 := by
  rw [stirMultiVSpecT_length_chal i]
  exact ht

/-- **Read the `j`-th field element off a `t`-point vector challenge** — the multi-point
analogue of `chalFE`. -/
def chalCoordT {M t : ℕ}
    (chals : ((stirMultiVSpecT M ι t).toProtocolSpec F).Challenges)
    (i : ((stirMultiVSpecT M ι t).toProtocolSpec F).ChallengeIdx) (j : Fin t) : F :=
  (chals i).get (Fin.cast (stirMultiVSpecT_length_chal i).symm j)

/-- At `t = 1`, the coordinate reader recovers `chalFE` at the unique coordinate. -/
theorem chalCoordT_one [SampleableType F] {M : ℕ} [Nonempty ι]
    (chals : ((stirMultiVSpecT M ι 1).toProtocolSpec F).Challenges)
    (i : ((stirMultiVSpecT M ι 1).toProtocolSpec F).ChallengeIdx) :
    chalCoordT chals i 0 = chalFE chals i := rfl

end MultiRound

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.MultiRound.stirMultiVSpecT_length_msg
#print axioms StirIOP.MultiRound.stirMultiVSpecT_length_chal
#print axioms StirIOP.MultiRound.chalCoordT_one
