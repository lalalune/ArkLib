/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds

/-!
# ABF26 C3.5 — named-`Prop` endpoint from the single coordinate-fiber-cap residual

This file closes the **named** external statement `frs_list_decoding_capacity_cz25`
(ABF26 Corollary 3.5 [CZ25 Cor 2.21], the unfolded inequality `Prop` admitted in
`ListDecoding/Bounds.lean`) reduced to exactly:

* `hT218` — ABF26 T2.18 [GK16] (FRS is a `τ`-subspace-design), and
* `hCap`  — the single named bridge residual `CZ25CoordFiberCap` for **every**
  `τ`-subspace-design code (the irreducible Guruswami–Wang affine-flat
  coordinate-fiber cap; documented in `CZ25SpanDimension.lean` as having no
  in-tree shortcut), plus
* `hηnat` — the documented floor/real reconciliation `1/η = ⌊1/η⌋`.

The inequality-body version of this composition is
`CZ25CapacityReduction.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218`.
Here we land the variant whose **conclusion is the named `Prop`**
`frs_list_decoding_capacity_cz25 …`, so downstream assembly code that targets the
named statement (not its unfolded inequality body) routes through one named
residual `CZ25CoordFiberCap` (+ T2.18) rather than re-discharging the
`hT34` general `Λ`-bound hypothesis.

The reduction is a pure composition of two already-landed, axiom-clean in-tree
bricks:

* `subspaceDesign_list_decoding_cz25_of_coordFiberCap` (T3.4 from the fiber cap,
  the #93 bridge), and
* `frs_list_decoding_capacity_cz25_of_residuals_prop` (the C3.5 corollary's own
  τ-substitution + bound algebra + floor/real reconciliation, concluding the
  named `Prop`).

No `sorry`, no new axioms. It does **not** attempt `CZ25CoordFiberCap` itself.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

#print axioms CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop
