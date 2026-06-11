/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.JohnsonListBound

/-!
# B2 — curve decodability ([GG25] Def 3.1) → [Jo26] curve-decodability half (#334)

**Target.** Formalize **[GG25] Definition 3.1 (curve decodability)** from scratch, then use
it to prove the [Jo26] curve-decodability half of the generator-factor bound. This is its own
**multi-brick project**: (1) the definition (a code is curve-decodable if low-degree curves
through close words are themselves close, with controlled list size), (2) the basic closure
lemmas, (3) the [Jo26] consumer.

**Reference.** [GG25] ePrint 2025/2054 Def 3.1; [Jo26] ePrint 2026/891 (the curve half of
Thm 4.2). The affine-line *exact* case is already in-tree as `epsMCA_interleaved_eq`
(`InterleavingStabilityMCA.lean`) — B2 generalizes lines to higher-degree curves.

**Substrate to consume.** `JohnsonListBound` (the up-to-Johnson list-size side),
`epsMCA_interleaved_eq` (the line base case), `MCAThresholdLedger` (the bracket engine).

**Plan.** Start with the Def 3.1 `def CurveDecodable …` (honest definition, no proof needed),
then the smallest closure brick. Break into multiple lanes — see the issue #334 thread for the
sibling `Jo26MarkedCurveDecodability` lane state before duplicating work.

**Honesty.** Definitions are free; each derived bound is a named obligation until proven.
-/

-- Replace with `def CurveDecodable …` and the first closure lemma.
example : True := trivial
