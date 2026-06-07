/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCoverage
import ArkLib.ResidualAxioms

/-!
# LineDecoding: ABF26 T4.21 status (issue #140)

**De-fabricated.** This file previously contained
`theorem mcaForallDoubleCover_holds … := mcaForallDoubleCover_residual …`, "closing" the global
line-decoding hypothesis via a fabricated `axiom`. That was unsound: `MCAForallDoubleCover` is the
unconstrained black-box ABF26 T4.21 form, which is **formally refuted** in
`LineDecodingRefutation.lean` (it fails for codes with bad scalars). The laundering theorem and the
asserting `axiom` are removed; `mcaForallDoubleCover_residual` is now a non-asserting
`def : Prop` open residual (`ArkLib.ResidualAxioms`).

The genuine repair is the constrained GS-interpolant form, not the refuted black-box statement.
Open #140.
-/
