/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListSizeMoments
import ArkLib.Data.CodingTheory.ProximityGap.BallVolume

/-!
# Direction A, made concrete: explicit moment list bounds (#232)

Ties together the moment identities (`ListSizeMoments.lean`) and the ball-volume closed form
(`BallVolume.lean`): the abstract ball volume `V(r)` is replaced by `Σ_{i≤r} C(n,i)(q-1)^i`, so the
first-moment worst-case list bound becomes a fully explicit inequality in `n = |ι|`, `q = |F|`, `r`.

* `ballVol_closed` — `V(r) = Σ_{i≤r} C(n,i)·(q-1)^i` (bridging `hammingDist 0 = hammingNorm`).
* `exists_large_list_concrete` — some received word has list size `≥ |C|·Σ_{i≤r}C(n,i)(q-1)^i / qⁿ`,
  the explicit averaged lower bound (concrete form of `exists_large_list`).
-/

namespace ArkLib.CodingTheory.ListMoments

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [Field F]

/-- **The ball volume in closed form.** `V(r) = Σ_{i=0}^{r} C(n,i)·(q-1)^i`. -/
theorem ballVol_closed (r : ℕ) :
    ballVol ι F r
      = ∑ i ∈ Finset.range (r + 1), (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i := by
  unfold ballVol
  simp only [hammingDist_zero_left]
  exact ArkLib.CodingTheory.BallVolume.ballVol_eq r

/-- **Concrete worst-case list lower bound.** At radius `r`, some received word `f` has a decoding
list of size at least the explicit average `|C|·Σ_{i≤r}C(n,i)(q-1)^i / qⁿ`; clearing `qⁿ`:
`|C|·(Σ_{i≤r}C(n,i)(q-1)^i) ≤ qⁿ·|Λ(C,r,f)|`. Fully explicit in `n, q, r` — direction A's averaged
lower half of `δ*` as a closed-form inequality. -/
theorem exists_large_list_concrete (C : Finset (ι → F)) (r : ℕ) :
    ∃ f : ι → F,
      C.card * (∑ i ∈ Finset.range (r + 1), (Fintype.card ι).choose i * (Fintype.card F - 1) ^ i)
        ≤ Fintype.card (ι → F) * (lam C r f).card := by
  rw [← ballVol_closed]
  exact exists_large_list C r

#print axioms ballVol_closed
#print axioms exists_large_list_concrete

end ArkLib.CodingTheory.ListMoments
