/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.InterleavedListSize

/-!
# GGR11 interleaved-code list-size recursion — residual reduction

This file isolates the **single external obstruction** behind ABF26 Lemma 2.10
(= Gopalan–Guruswami–Raghavendra 2011, "List Decoding Tensor Products and
Interleaved Codes", RANDOM 2011) so that `lambda_le_ggr11` in
`ArkLib.Data.CodingTheory.InterleavedCode` can be discharged *modulo a single,
precisely named combinatorial hypothesis* with **no `sorry` and no `axiom`** in
the reduction itself.

## The theorem

Let `C ⊆ (ι → F)` be a code with relative minimum distance `δ_C := δ_min(C)/|ι|`,
and `δ ∈ [0, δ_C)`. With `η := δ_C - δ`, `b := ⌈δ/η⌉`, `r := ⌈log₂(δ_C/η)⌉`,
GGR11 / ABF26 L2.10 states, for every `m ≥ 1`,

  `|Λ(C^{≡m}, δ)| ≤ (b+r choose r) · |Λ(C, δ)|^r`.   (★)

## What is in-tree, what is the residual

`ArkLib.Data.CodingTheory.InterleavedListSize` proves, fully `sorry`-free, the
elementary `m`-*dependent* bound

  `|Λ(C^{≡m}, δ)| ≤ |Λ(C, δ)|^m`   (the per-column product bound),

via the injection `V ↦ (V.transpose ·)` of a close interleaved codeword into the
product of its per-column base-code lists.  That is the deepest in-tree-reachable
statement: it uses only the row/column projection lemmas.

The improvement of (★) over the product bound is the replacement of the exponent
`m` by the `m`-*independent* `r = ⌈log₂(δ_C/η)⌉`, together with the `(b+r choose
r)` prefactor.  Achieving `m`-independence is exactly the GGR11 list-recovery /
column-pruning recursion: of the `m` columns, only `r` "pivot" columns carry
independent list freedom (a budget/covering argument over the `b`-bounded
agreement deficits), and the joint list embeds into the product of the per-pivot
lists.  ArkLib presently has **no list-recovery primitive and no column-pruning /
iterated-projection lemma**, so this step is a genuine external-paper wall, not a
missing local proof.

We therefore name precisely that wall — the per-received-word form of (★) — as
`GGR11PerWordBound`, and prove that it implies (★) for the maximised `Lambda`.
This converts the live `sorry` into a single, auditable named hypothesis.

## Edge cases discharged unconditionally

`lambda_le_ggr11` itself (in `InterleavedCode.lean`) already closes the
infinite-list case `Λ(C, δ) = ⊤` completely (the RHS is then `⊤`).  Here we also
record `lambda_le_ggr11_of_perWordBound`, the finite-regime reduction.
-/

open ListDecodable Code InterleavedCode

namespace InterleavedCode.GGR11

variable {ι F : Type} [Fintype ι]

/-- **The GGR11 residual (per-received-word form).**

For a fixed received interleaved word `f : Matrix ι (Fin m) F`, the number of
interleaved codewords `δ`-close to `f` is at most `(b+r choose r) · |Λ(C,δ)|^r`,
with `r` (and `b`) the GGR11 exponent/prefactor — **independent of `m`**.

This is exactly the content GGR11 §3 establishes by the list-recovery /
column-pruning recursion described in the module docstring.  It is stated as an
`encard` bound so that it is meaningful over an arbitrary (possibly infinite)
field `F`, with no `Fintype F` assumption: when a per-column list is infinite the
hypothesis is vacuously informative on the `⊤` side, and the genuine content is
the finite case.

We do **not** prove this here: it is the named external obstruction. -/
def GGR11PerWordBound (C : Set (ι → F)) (δ : ℝ) (m b r : ℕ) : Prop :=
  ∀ f : Matrix ι (Fin m) F,
    (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r

/-- **Reduction of the GGR11 interleaved list-size bound to its per-word form.**

Given the per-received-word bound `GGR11PerWordBound`, the maximised list size
`Lambda (C^{≡m}) δ` obeys the same bound.  The lift is a routine `iSup`/`ncard ≤
encard` argument; *all* the mathematical depth lives in the hypothesis. -/
theorem lambda_le_ggr11_of_perWordBound
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (h : GGR11PerWordBound C δ m b r) :
    Lambda (interleavedCodeSet (κ := Fin m) C) δ
      ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := by
  refine iSup_le (fun f => ?_)
  calc ((closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).ncard : ℕ∞)
      ≤ (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard :=
        Set.ncard_le_encard _
    _ ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := h f

set_option linter.unusedFintypeInType false in
/-- Over a *finite* field the in-tree elementary product bound discharges the
GGR11 residual whenever the GGR11 exponent `r` already dominates the interleaving
factor `m` **and** the base list size is at least one — i.e. exactly the regime
in which `m`-independence carries no extra information.  Concretely, if `m ≤ r`
and `1 ≤ Λ(C,δ)`, then
`|Λ(C^{≡m},δ)| ≤ |Λ(C,δ)|^m ≤ |Λ(C,δ)|^r ≤ (b+r choose r)·|Λ(C,δ)|^r`.

This is **not** the GGR11 content (which is the complementary `m > r` regime); it
is a sanity sub-case showing the reduction is consistent with the in-tree bound. -/
theorem ggr11_perWordBound_of_le_exp [Fintype F] [Nonempty ι]
    {C : Set (ι → F)} {δ : ℝ} {m b r : ℕ}
    (hmr : m ≤ r) (hL : 1 ≤ Lambda C δ) :
    GGR11PerWordBound C δ m b r := by
  intro f
  have hpow : (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
      ≤ (Lambda C δ) ^ m :=
    InterleavedCode.ListSize.encard_closeCodewordsRel_interleaved_le f
  have hexp : (Lambda C δ) ^ m ≤ (Lambda C δ) ^ r := pow_le_pow_right₀ hL hmr
  have hbinom : (1 : ℕ∞) ≤ ((b + r).choose r : ℕ∞) := by
    have : 1 ≤ (b + r).choose r := Nat.choose_pos (Nat.le_add_left r b)
    exact_mod_cast this
  calc (closeCodewordsRel (interleavedCodeSet (κ := Fin m) C) f δ).encard
      ≤ (Lambda C δ) ^ m := hpow
    _ ≤ (Lambda C δ) ^ r := hexp
    _ = 1 * (Lambda C δ) ^ r := (one_mul _).symm
    _ ≤ ((b + r).choose r : ℕ∞) * (Lambda C δ) ^ r := by
          gcongr

end InterleavedCode.GGR11
