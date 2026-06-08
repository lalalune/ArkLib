/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

/-!
# Batched FRI Joint Proximity (Issue #14)

The batched-FRI joint-proximity residual — the bound on the probability that a random linear
combination of functions is `δ`-close to a Reed–Solomon code while the individual functions are
not jointly close — is tracked **honestly** as the named proposition
`ProximityGap.Issue14.BatchedFRIJointProximityKernel` (an open `def : Prop` in `Issue14Kernels`).

Its proof is the beyond-list-decoding-radius mass bound and is **not** in tree. This module
intentionally contains **no** `theorem` discharging it: an earlier
`batched_fri_joint_proximity_breakthrough : … := by sorry` "Resolution" was removed because it
laundered the open residual into `sorryAx` while claiming a breakthrough. Downstream developments
should consume `BatchedFRIJointProximityKernel` as an explicit hypothesis until the underlying
list-decoding bound is actually proved.
-/
