/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.DCSubtractedMoment

/-!
# The phase-alignment "tower law" is just reality — a NO-GO constraint lemma (#407)

## The refuted lane (probe-first, then pinned)

The fleet observed (phase-alignment tower probes) that at the worst frequency `b*`, the two
half-coset sums `S0(b*) = ∑_{x∈μ_{n/2}} e_p(b*·x)` and `S1(b*)` are *maximally phase-aligned*
(`cos(S0, S1) = 1.0000`, machine-exact, `n = 8,16,32,64`). This was floated as a candidate
**non-average structural handle** (a tower-recursive self-similarity a descent/Stepanov argument
could exploit, since average/moment methods are blind to worst-frequency alignment).

## Adversarial recheck (refutation)

The interpretation does NOT survive. Two probes (`scripts/probes/probe_phase_dichotomy.py`,
`probe_phase_why.py`, `probe_reality.py`) show:

1. `|cos(S0(b), S1(b))| = 1.0000` for **EVERY** frequency `b` (256/256, 599/599 sampled), not just
   `b*`. The two half-coset sums are **always real-collinear**.
2. This holds **identically in the THIN (prize) and THICK (anti-prize) regimes** — at `β ≈ 9.8`
   (deep prize) and at `β ≈ 1.07` (very thick) alike. The cosine is `±1` everywhere; the rare `−1`
   cases are sporadic sign flips of two *real* numbers, not a regime signal.
3. **Root cause:** `μ_{n/2}` is a `2`-power cyclic subgroup of **even** order `n/2`, so it contains
   the unique order-`2` element `−1`. Hence `μ_{n/2}` is closed under negation, which forces
   `S0(b) = ∑_{x∈μ_{n/2}} e_p(b·x)` to be **REAL** (pair `x` with `−x`: `e_p(bx)+e_p(−bx) = 2cos`).
   Verified `max|Im S0(b)| ~ 1e-15`. Two real numbers are trivially collinear, so `cos = ±1` is
   automatic.

**Constraint lemma (`eta_real_of_neg_closed`, below).** If `G` is closed under negation then
`eta ψ G b` is real for every `b`. This is the precise, axiom-clean reason the "alignment" is NOT
a tower mechanism: it is forced by reality, holds for all `b`, and is **NOT thinness-essential**
(it is identical in the thick window where the prize is FALSE). Any descent built on the cosine
being `±1` is therefore thickness-monotone, which §3/rule-3 of #407 forbids. **Lane pinned.**

Issue #407.
-/

open Finset ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.PhaseAlignmentReality

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
/-- **Reality from negation-closure (the constraint lemma).** If `G` is closed under negation, the
period `eta ψ G b = ∑_{y∈G} ψ(b·y)` is REAL (conjugate-invariant) for every `b`, for any character
with `conj(ψ a) = ψ(-a)`. The observed worst-frequency "phase alignment" `cos(S0,S1)=±1` is exactly
this automatic reality (pairing `y ↔ -y`), holding for ALL `b` in thin AND thick regimes — hence
**not** a tower-recursive, thinness-essential mechanism. -/
theorem eta_real_of_neg_closed {ψ : AddChar F ℂ} (G : Finset F)
    (hG : ∀ y ∈ G, -y ∈ G)
    (hchar : ∀ a : F, (starRingEnd ℂ) (ψ a) = ψ (-a)) (b : F) :
    (starRingEnd ℂ) (eta ψ G b) = eta ψ G b := by
  classical
  unfold eta
  rw [map_sum]
  rw [show (∑ y ∈ G, (starRingEnd ℂ) (ψ (b * y)))
        = ∑ y ∈ G, ψ (b * (-y)) from
      Finset.sum_congr rfl (fun y _ => by rw [hchar]; ring_nf)]
  apply Finset.sum_nbij' (fun y => -y) (fun y => -y)
  · intro y hy; exact hG y hy
  · intro y hy; exact hG y hy
  · intro y _; ring
  · intro y _; ring
  · intro y _; ring

end ProximityGap.Frontier.PhaseAlignmentReality

#print axioms ProximityGap.Frontier.PhaseAlignmentReality.eta_real_of_neg_closed
