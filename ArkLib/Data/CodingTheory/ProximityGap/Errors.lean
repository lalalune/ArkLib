/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.Probability.Instances

/-!
# Numeric ε-error functions: ε_ca and ε_mca

Numeric versions of the proximity gap, correlated agreement (CA), and mutual correlated
agreement (MCA) error functions as defined in
*Open Problems in List Decoding and Correlated Agreement*
(Arnon, Boneh, Fenzi; April 8, 2026), Section 4.

This file implements the **numeric error-function API** for CA and MCA. It coexists with the
predicate-style API in [`Basic.lean`](Basic.lean); each predicate has a bridging
`*_iff_eps*_le` lemma elsewhere in this directory.

## Main definitions

- `ProximityGap.epsPG` — proximity gap error, introduced informally in paper §4.1.
- `ProximityGap.epsCA` — ABF26 Definition 4.1: correlated agreement error
  `ε_ca(C, δ_fld, δ_int)` (affine-line case, `Fin 2` stacks).
- `ProximityGap.epsCA'` — Convenience alias for the no-proximity-loss case
  `ε_ca(C, δ) := ε_ca(C, δ, δ)`.
- `ProximityGap.epsCA_curves` — `Fin (k+1)`-stack variant: worst-case probability over
  polynomial curves `∑ i, r^i · f_i`. Generalises `epsCA` (the `k = 1` case).
- `ProximityGap.epsCA_affineSpaces` — `Fin (k+1)`-stack variant: worst-case probability
  over random points in the affine subspace `f₀ + span{f₁, ..., f_k}`.
- `ProximityGap.epsMCA` — ABF26 Definition 4.3: mutual correlated agreement error.

## Note on MCA with proximity loss (ABF26 Remark 4.4)

The paper intentionally does **not** define a proximity-loss variant of `ε_mca` analogous to
`ε_ca(C, δ_fld, δ_int)`. Per Remark 4.4 this remains to be thoroughly explored, so this file
exposes only the no-loss `ε_mca(C, δ)`.

## Open follow-ups

The following items from ABF26 Section 4 are tracked in `docs/kb/ABF26_PLAN.md` §7 and remain to be
added on top of this file's definitions. Each is in scope for Phase 1 of the plan:

- **Monotonicity / antitonicity of `epsCA`** (ABF26-D4.1 sub-tasks 4–5). `epsCA` is
  *monotone* in `δ_fld` (larger fold-distance ⇒ more `γ` in the event) and **antitone**
  in `δ_int` (larger interleaved-distance ⇒ stricter `Δ_joint > δ_int` condition).
- **ABF26 Remark 4.2** — discretization: `epsCA C δ (δ + β) = epsCA C δ (δ + β')` for
  `β, β' ∈ [0, 1/n)`. Follows from `Δ ∈ {0, 1/n, ..., 1}`.
- **ABF26 Fact 4.5** — `ε_pg ≤ ε_ca ≤ ε_mca`. Requires defining `epsPG` first.
- **ABF26 Lemma 4.6** — `ε_mca = ε_ca` below `δ_min(C)/2`. Proof leans on the helper
  predicates `pairJointAgreesOn` and `mcaEvent` defined here.
- **ABF26 Lemma 4.7** — `ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)` via union bound.
- **Bridging lemmas**: `δ_ε_correlatedAgreementAffineLines C δ ε ↔ epsCA C δ δ ≤ ε` (and
  similar for `Curves`, `AffineSpaces`) connecting the predicate API in `Basic.lean` to the
  numeric API here.

## Design notes worth flagging

- **`epsCA` / `epsMCA` take `C : Set (ι → A)` and not `Submodule F (ι → A)`** by design.
  The definitions are pure predicates over a set of codewords — neither uses the linear
  structure. Theorems that *need* `C` to be a `ModuleCode` add the `Submodule` hypothesis
  separately (e.g. F4.5 takes `C : Submodule F (ι → A)`). Linear callers pass their
  `Submodule` via the implicit coercion `(C : Set _)`. We keep the definitions
  Set-based to:
  1. Avoid narrowing the API — `epsCA` is meaningful for non-linear codes too.
  2. Match the paper's `C ⊆ Σ^n` shape, which is also Set-based.
  3. Avoid a deep refactor of every `epsCA` / `epsMCA` call site for a one-character
     win at each one.
- **`F` is implicit in `epsCA` but does not appear in its return type**, so callers that
  invoke `epsCA` without an explicit pair `(f₁, f₂)` (e.g. inside `epsCA'`) need
  `epsCA (F := F) C δ δ` to thread `F` through. If this becomes painful in proofs,
  switching `epsCA` to take `F` as an explicit argument is a cheap refactor.
- **`epsMCA` and `mcaEvent` are `Fin 2`-only** (the affine-line case). Paper Section 4
  considers more general interleavings; generalizing to `Fin ℓ` is a future extension,
  not required for F4.5 or L4.6.
- **`pairJointAgreesOn` and `mcaEvent` are intentionally public**, exposed as named
  anchors for the planned L4.6 proof and bridging lemmas. If they prove unhelpful in
  practice they can be inlined / marked `private`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

-- The definitions and proofs below all take the variables `ι`, `F`, `A` from a single section
-- (PMF forces them into `Type 0`). Several theorems use `Fintype`/`DecidableEq` instances at
-- proof-time but not in their types; suppressing the noisy `unused...InType` linter warnings
-- file-wide here, matching the idiom used in `ReedSolomon/FftDomain.lean` and similar files.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

section

-- Universe constraints: `PMF` (used by the `Pr_{...}` notation) is universe-monomorphic at
-- `Type 0`, so `ι`, `F`, and `A` must live in `Type`, matching the existing predicate-style API
-- in `Basic.lean` (`δ_ε_correlatedAgreementAffineLines` and friends).
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **ABF26 Section 4.1 (proximity gap error).** Worst-case "bad fraction" of `γ`-points
for which a line `f₁ + γ·f₂` is `δ`-close to `C` while the line is *not* entirely `δ`-close.

Paper §4.1 page 17 introduces this informally: a code has proximity gap `ε_pg(C, δ)` if
every line is either entirely `δ`-close to `C` (i.e. every `γ ∈ F` gives a δ-close point)
or at most `ε_pg` fraction of it is — a dichotomy. The strict comparison with `ε_ca`
(`epsPG ≤ epsCA`, paper Fact 4.5) is that the "bad" set for `epsPG` (`¬ ∀ γ, line close`)
is contained in the "bad" set for `epsCA` (`¬ jointProximity`) when `C` is closed under
linear combination, since any joint codeword pair `(v₀, v₁)` produces a line of codewords
`v₀ + γ·v₁ ∈ C`. -/
noncomputable def epsPG (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if (∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ) then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ]

open Classical in
/-- **ABF26 Definition 4.1.** Correlated agreement (CA) error of an `F`-additive code `C`
with respect to fold-distance `δ_fld` and interleaved-distance `δ_int`.

The worst-case probability over pairs of words `(f₁, f₂)` and over `γ ← $ᵖ F` that

- the line `f₁ + γ·f₂` is `δ_fld`-close to `C`, **and**
- the pair `(f₁, f₂)` is **not** `δ_int`-close to the interleaved code `C^⋈ (Fin 2)`.

The second condition is `γ`-independent, so the formula simplifies to `0` when `(f₁, f₂)`
is jointly close, and to the line probability otherwise. Cf. paper Section 4.1. -/
noncomputable def epsCA (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ_fld]

/-- No-proximity-loss specialization: `ε_ca(C, δ) := ε_ca(C, δ, δ)`. Matches the paper's
short-form notation when both fold-distance and interleaved-distance coincide.

By definition `epsCA C δ δ ≡ epsCA' C δ`; no explicit `epsCA_self` simp lemma is needed
because the two forms are definitionally equal.

Currently unused inside this file — F4.5 and downstream theorems state things in terms of
`epsCA C δ δ` directly to keep the two `δ` arguments visible. Kept exported because external
callers (and future bridging lemmas) may prefer the short form. -/
noncomputable def epsCA' (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  epsCA (F := F) C δ δ

open Classical in
/-- **ABF26 Definition 4.1, curves variant.** Worst-case probability over `(k+1)`-stacks
`u = (f₀, ..., f_k)` and `r ← $ᵖ F` that the polynomial curve `∑ i, r^i · f_i` is
`δ_fld`-close to `C` while the stack is *not* `δ_int`-close to the interleaved code
`C^⋈ (Fin (k+1))`.

For `k = 1` this collapses to `epsCA` (the affine-line case), modulo the syntactic
difference between `∑ i : Fin 2, r^i · u i` and `u 0 + r · u 1` (they are mathematically
equal). -/
noncomputable def epsCA_curves
    (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin (k + 1)) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let r ← $ᵖ F}[δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fld]

open Classical in
/-- **ABF26 Definition 4.1, affine-spaces variant.** Worst-case probability over
`(k+1)`-stacks `u = (f₀, ..., f_k)` and a uniformly random point `y` in the affine
subspace `f₀ + span{f₁, ..., f_k}` (≡ `Affine.affineSubspaceAtOrigin (u 0) (Fin.tail u)`)
that `y` is `δ_fld`-close to `C` while the stack is *not* `δ_int`-close to the interleaved
code `C^⋈ (Fin (k+1))`. Parallels `epsCA` and `epsCA_curves`. -/
noncomputable def epsCA_affineSpaces
    (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin (k + 1)) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      δᵣ(y.1, C) ≤ δ_fld]

/-- The pair `(u₀, u₁)` jointly agrees with two codewords of `C` on every position in `S`.
Equivalent in spirit to `Δ_S((u₀, u₁), C^≡2) = 0` from the paper. -/
def pairJointAgreesOn (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) : Prop :=
  ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i

/-- The "bad" event in ABF26 Definition 4.3: there is a witness set `S` of size at least
`(1-δ)·n` on which the line `u₀ + γ • u₁` exactly equals some codeword of `C`, but no
joint pair of codewords agrees with `(u₀, u₁)` on `S`. -/
def mcaEvent (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁

open Classical in
/-- **ABF26 Definition 4.3.** Mutual correlated agreement (MCA) error.

The worst-case probability over pairs `(f₁, f₂)` and over `γ ← $ᵖ F` of the
`mcaEvent`: a single set `S` of size `≥ (1-δ)·n` witnesses both that the line
`f₁ + γ·f₂` exactly equals some codeword of `C` on `S` **and** that no joint pair
of codewords agrees with `(f₁, f₂)` on `S`. MCA strengthens CA (Definition 4.1)
by requiring the witness set for closeness and non-agreement to coincide.

Per Remark 4.4, the paper intentionally does not define a proximity-loss variant. -/
noncomputable def epsMCA (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]

/-! ## Monotonicity of `epsCA` (ABF26 Definition 4.1 sub-tasks 4–5)

These two lemmas, together with `epsCA_eq_of_floor_eq`, characterize how `epsCA` varies
with its two distance arguments.

- `epsCA` is **monotone** in `δ_fld`: a larger fold-distance means more `γ` satisfy the
  "line `δ_fld`-close" event, so the inner `Pr` grows.
- `epsCA` is **antitone** in `δ_int`: a larger interleaved-distance is a *weaker* condition
  for `jointProximity`, so *more* pairs `(f₁, f₂)` are jointly close and contribute `0`
  rather than a non-zero `Pr`, decreasing the supremum.

The direction of the second one was a recurring confusion in the original plan; the proof
makes it concrete. -/

/-- **ABF26 Definition 4.1, sub-task 5.** `epsCA` is monotone in `δ_fld`. -/
theorem epsCA_mono_δ_fld
    (C : Set (ι → A)) {δ_fld δ_fld' : ℝ≥0} (δ_int : ℝ≥0) (h : δ_fld ≤ δ_fld') :
    epsCA (F := F) C δ_fld δ_int ≤ epsCA (F := F) C δ_fld' δ_int := by
  classical
  unfold epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos hjp]
  · rw [if_neg hjp, if_neg hjp]
    -- `Pr_γ[Δ ≤ δ_fld] ≤ Pr_γ[Δ ≤ δ_fld']` by event implication.
    apply Pr_le_Pr_of_implies
    intro _ h_close
    exact le_trans h_close (by exact_mod_cast h)

/-- **ABF26 Definition 4.1, sub-task 4.** `epsCA` is **antitone** in `δ_int`. -/
theorem epsCA_antitone_δ_int
    (C : Set (ι → A)) (δ_fld : ℝ≥0) {δ_int δ_int' : ℝ≥0} (h : δ_int ≤ δ_int') :
    epsCA (F := F) C δ_fld δ_int' ≤ epsCA (F := F) C δ_fld δ_int := by
  classical
  unfold epsCA
  apply iSup_mono
  intro u
  -- `jointProximity` is monotone in `δ` (the relative distance comparison `δᵣ ≤ δ`
  -- becomes easier when `δ` grows), so `jointProximity_δ_int → jointProximity_δ_int'`.
  have h_jp_mono :
      jointProximity (C := C) (u := u) δ_int →
      jointProximity (C := C) (u := u) δ_int' := by
    intro h_jp
    exact le_trans h_jp (by exact_mod_cast h)
  by_cases hjp' : jointProximity (C := C) (u := u) δ_int'
  · rw [if_pos hjp']; exact zero_le _
  · -- Contrapositive of `h_jp_mono`: `¬jointProximity_δ_int' → ¬jointProximity_δ_int`.
    have hjp : ¬ jointProximity (C := C) (u := u) δ_int := fun h_jp ↦ hjp' (h_jp_mono h_jp)
    rw [if_neg hjp', if_neg hjp]

/-- **`epsMCA` is monotone in `δ`.** A larger proximity radius `δ` only *weakens* the
size constraint `|S| ≥ (1 - δ)·n` of `mcaEvent` (the other two clauses — a codeword
agreeing with the line on `S`, and the absence of a joint codeword pair on `S` — do not
mention `δ`), so the bad event holds for at least as many witness sets `S`. The per-`u`
probability therefore grows pointwise, and so does the supremum.

This is the `epsMCA` analogue of `epsCA_mono_δ_fld`; it is the monotonicity fact behind the
maximality clause of the ABF26 §1 Grand MCA Challenge (a threshold `δ*` with `ε_mca ≤ ε*`
below and `> ε*` above only makes sense because `ε_mca` is non-decreasing in `δ`). -/
theorem epsMCA_mono
    (C : Set (ι → A)) {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    epsMCA (F := F) C δ ≤ epsMCA (F := F) C δ' := by
  classical
  unfold epsMCA
  apply iSup_mono
  intro u
  apply Pr_le_Pr_of_implies
  intro γ h_event
  obtain ⟨S, hS_card, hline, hpair⟩ := h_event
  -- The size clause `(1 - δ')·n ≤ (1 - δ)·n ≤ |S|` survives; `hline`/`hpair` are δ-free.
  exact ⟨S, le_trans (mul_le_mul_of_nonneg_right (tsub_le_tsub_left h 1) (zero_le _)) hS_card,
    hline, hpair⟩

/-! ## Helpers toward ABF26 Fact 4.5

Fact 4.5 says `ε_pg ≤ ε_ca ≤ ε_mca`. The first inequality requires the underlying code to
be closed under linear combination, so we state the helper lemmas with a `Submodule F (ι → A)`
hypothesis. -/

/-- **Helper for ABF26 Fact 4.5.** If the pair `(u 0, u 1)` is jointly `δ`-close to the
interleaved code from a `Submodule` `MC`, then for *every* scalar `γ`, the line
`u 0 + γ • u 1` is `δ`-close to `MC`. The proof uses the witness codeword pair
`(v 0, v 1)` to build a single line of codewords `v 0 + γ • v 1 ∈ MC`. -/
theorem jointProximity_imp_line_close
    (MC : Submodule F (ι → A)) (u : WordStack A (Fin 2) ι) (δ : ℝ≥0)
    (h : jointProximity (C := (MC : Set (ι → A))) (u := u) δ) :
    ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ := by
  rw [← jointAgreement_iff_jointProximity] at h
  obtain ⟨S, hS_card, v, hv⟩ := h
  -- Common: pointwise agreement of `v i` and `u i` on `S`.
  have h_agree : ∀ j ∈ S, v 0 j = u 0 j ∧ v 1 j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have : j ∈ Finset.filter (fun k ↦ v 0 k = u 0 k) Finset.univ := (hv 0).2 hj
      exact (Finset.mem_filter.mp this).2
    · have : j ∈ Finset.filter (fun k ↦ v 1 k = u 1 k) Finset.univ := (hv 1).2 hj
      exact (Finset.mem_filter.mp this).2
  intro γ
  have hv_γ_mem : (v 0 + γ • v 1) ∈ (MC : Set (ι → A)) :=
    MC.add_mem (hv 0).1 (MC.smul_mem γ (hv 1).1)
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨v 0 + γ • v 1, hv_γ_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj_in ↦ ?_, fun hne hj_in ↦ ?_⟩
  · obtain ⟨h0, h1⟩ := h_agree j hj_in
    simp [Pi.add_apply, Pi.smul_apply, h0, h1]
  · obtain ⟨h0, h1⟩ := h_agree j hj_in
    exact hne (by simp [Pi.add_apply, Pi.smul_apply, h0, h1])

/-- **ABF26 Fact 4.5, first inequality.** `ε_pg ≤ ε_ca` for a `Submodule F (ι → A)`.

Pointwise on `u : WordStack A (Fin 2) ι`:

- If `jointProximity` holds, every `γ` gives a δ-close line (by
  `jointProximity_imp_line_close`), so the `epsPG` contribution is 0; `epsCA`'s contribution
  is also 0 (its `if jointProximity` branch).
- Otherwise both contributions collapse to the same `Pr_γ[line δ-close]` because the inner
  expression is syntactically identical and the bad-set conditions both fail or both hold. -/
theorem epsPG_le_epsCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsPG (F := F) (MC : Set (ι → A)) δ ≤ epsCA (F := F) (MC : Set (ι → A)) δ δ := by
  unfold epsPG epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · -- jointProximity ⇒ ∀ γ close (via the helper), so both `if`s pick the 0 branch.
    -- `rw` closes the residual `0 ≤ 0` goal automatically via its built-in `rfl` step.
    have h_all : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ :=
      jointProximity_imp_line_close MC u δ hjp
    rw [if_pos h_all, if_pos hjp]
  · by_cases h_all : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ
    · -- `epsPG` picks 0; `epsCA` picks Pr ≥ 0.
      rw [if_pos h_all, if_neg hjp]
      exact zero_le _
    · -- Both pick the same `Pr_γ[line δ-close]` (same expression inside the `Pr`).
      rw [if_neg h_all, if_neg hjp]

/-- **ABF26 Fact 4.5, second inequality.** `ε_ca ≤ ε_mca` for a `Submodule F (ι → A)`.

Pointwise on `u`:

- If `jointProximity`, `epsCA`'s contribution is 0, ≤ anything.
- Otherwise we apply `Pr_le_Pr_of_implies` with the fact that "line δ-close to `MC`" implies
  `mcaEvent MC δ (u 0) (u 1) γ` (in the `¬jointProximity` regime): the witness set `S` for
  the line-close fact has size `≥ (1-δ)·n` and is automatically *not* a joint-agreement
  set (because if it were, `jointProximity` would hold via the equivalence
  `jointAgreement_iff_jointProximity`). -/
theorem epsCA_le_epsMCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤ epsMCA (F := F) (MC : Set (ι → A)) δ := by
  unfold epsCA epsMCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · rw [if_pos hjp]; exact zero_le _
  · rw [if_neg hjp]
    -- Probability monotonicity: `Pr_γ[line close] ≤ Pr_γ[mcaEvent]` because, in the
    -- `¬jointProximity` regime, "line δ-close to MC" implies `mcaEvent`. The implication
    -- is proved per γ below.
    apply Pr_le_Pr_of_implies
    intro γ h_line
    -- Step 1: unfold the line-close witness. `h_line : δᵣ(line, MC) ≤ δ` gives a codeword `w`
    -- and a finite set `S` on which `line = w` pointwise.
    rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at h_line
    obtain ⟨w, hw_mem, hw_close⟩ := h_line
    rw [relCloseToWord_iff_exists_agreementCols] at hw_close
    obtain ⟨S, hS_card_nat, h_word_agree⟩ := hw_close
    have hS_card_real : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι :=
      (relDist_floor_bound_iff_complement_bound _ _ _).mp hS_card_nat
    -- Step 2: assemble `mcaEvent` with witness `S`, codeword `w` for the line-side, and the
    -- still-to-prove negation on the pair-side.
    refine ⟨S, hS_card_real, ⟨w, hw_mem, fun i hi ↦ ((h_word_agree i).1 hi).symm⟩, ?_⟩
    -- Step 3: ¬ pairJointAgreesOn MC S (u 0) (u 1). Argue by contradiction with `hjp`:
    -- if there were a joint codeword pair agreeing on `S`, `finMapTwoWords` would build a
    -- jointAgreement witness, which `jointAgreement_iff_jointProximity` would lift to
    -- `jointProximity`, contradicting the hypothesis `¬jointProximity`.
    intro h_pair
    apply hjp
    rw [← jointAgreement_iff_jointProximity]
    obtain ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_pair_agree⟩ := h_pair
    refine ⟨S, hS_card_real, finMapTwoWords v₀ v₁, ?_⟩
    intro i
    refine ⟨?_, ?_⟩
    · -- `(finMapTwoWords v₀ v₁) i ∈ MC` by cases on `i : Fin 2`.
      fin_cases i
      · exact hv₀_mem
      · exact hv₁_mem
    · -- `S ⊆ filter (· = u i)` by cases on `i`.
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      fin_cases i
      · exact (h_pair_agree j hj).1
      · exact (h_pair_agree j hj).2

/-- **ABF26 Fact 4.5.** For an `F`-additive code (here: a `Submodule F (ι → A)`):
`ε_pg(C, δ) ≤ ε_ca(C, δ, δ) ≤ ε_mca(C, δ)`. -/
theorem epsPG_le_epsCA_le_epsMCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsPG (F := F) (MC : Set (ι → A)) δ ≤ epsCA (F := F) (MC : Set (ι → A)) δ δ ∧
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤ epsMCA (F := F) (MC : Set (ι → A)) δ :=
  ⟨epsPG_le_epsCA MC δ, epsCA_le_epsMCA MC δ⟩

/-- **ABF26 Remark 4.2 (level-set form).** Because relative Hamming distance only takes
values in `{0, 1/n, ..., 1}`, the predicate `jointProximity C u δ_int` (which is
`δᵣ(⋈|u, C^⋈ 2) ≤ δ_int`) depends on `δ_int` only through `⌊δ_int · n⌋`. Hence
`epsCA C δ_fld δ_int` is constant on every "level set" `[k/n, (k+1)/n)` of `δ_int`.

The paper states this with a "shift by `β, β' ∈ [0, 1/n)`" idiom (`ε_ca(C, δ, δ + β) =
ε_ca(C, δ, δ + β')`); that form follows from this lemma whenever the interval
`[δ + min β β', δ + max β β']` does not cross a multiple of `1/n` — in particular when
`δ` is itself such a multiple. -/
theorem epsCA_eq_of_floor_eq (C : Set (ι → A)) (δ_fld δ_int δ_int' : ℝ≥0)
    (h : Nat.floor (δ_int * Fintype.card ι) = Nat.floor (δ_int' * Fintype.card ι)) :
    epsCA (F := F) C δ_fld δ_int = epsCA (F := F) C δ_fld δ_int' := by
  unfold epsCA
  apply iSup_congr
  intro u
  -- `jointProximity` is determined by `Δ₀ ≤ ⌊δ · n⌋` via
  -- `relDistFromCode_le_iff_distFromCode_le`, so it agrees on `δ_int` and `δ_int'`
  -- whenever the floors agree.
  have h_iff : jointProximity (C := C) (u := u) δ_int ↔
               jointProximity (C := C) (u := u) δ_int' := by
    unfold jointProximity
    rw [relDistFromCode_le_iff_distFromCode_le, relDistFromCode_le_iff_distFromCode_le, h]
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos (h_iff.mp hjp)]
  · rw [if_neg hjp, if_neg (mt h_iff.mpr hjp)]

/-! ## Bridging the predicate-style API in `Basic.lean` to the numeric API here

These iff-lemmas let downstream code that was written against `δ_ε_correlatedAgreement*`
predicates migrate to the numeric `eps*` form (or vice versa) without rewriting proofs. -/

/-- **Bridge.** The predicate `δ_ε_correlatedAgreementAffineLines C δ ε` (from `Basic.lean`)
is equivalent to the numeric inequality `epsCA C δ δ ≤ ε`.

Forward: assume the predicate. For each `u`, the `epsCA` body is either `0` (when
`jointProximity`) or `Pr_γ[line δ-close]`; in the latter case `¬jointAgreement`, so the
predicate's contrapositive gives `Pr ≤ ε`. `iSup_le` concludes.

Backward: assume `epsCA ≤ ε`. For any `u` with `Pr > ε`, the contribution `body u` is at most
`epsCA ≤ ε`. If `¬jointProximity`, `body u = Pr > ε` is a contradiction; so
`jointProximity`, hence `jointAgreement` via the existing equivalence. -/
theorem δ_ε_correlatedAgreementAffineLines_iff_epsCA_le
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineLines (F := F) C δ ε ↔
    epsCA (F := F) C δ δ ≤ (ε : ENNReal) := by
  classical
  constructor
  · intro h_pred
    refine iSup_le fun u ↦ ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]; exact zero_le _
    · rw [if_neg hjp]
      have h_not_ja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]; exact hjp
      by_contra h_gt
      push Not at h_gt
      exact h_not_ja (h_pred u h_gt)
  · intro h_eps u h_pr
    unfold epsCA at h_eps
    -- `iSup_le_iff` turns `⨆ u, body u ≤ ε` into `∀ u, body u ≤ ε`,
    -- then we specialize at this `u`.
    have h_term_le := iSup_le_iff.mp h_eps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]; exact hjp
    · rw [if_neg hjp] at h_term_le
      exact absurd h_pr (not_lt.mpr h_term_le)

/-- **Bridge for curves.** The predicate `δ_ε_correlatedAgreementCurves C δ ε` (from
`Basic.lean`, threshold `k · ε`) is equivalent to the numeric inequality
`epsCA_curves C k δ δ ≤ k · ε`. Same proof recipe as the `AffineLines` bridge. -/
theorem δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le {k : ℕ}
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementCurves (F := F) (k := k) C δ ε ↔
    epsCA_curves (F := F) C k δ δ ≤ ((k * ε : ℝ≥0) : ENNReal) := by
  classical
  constructor
  · intro h_pred
    refine iSup_le fun u ↦ ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]; exact zero_le _
    · rw [if_neg hjp]
      have h_not_ja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]; exact hjp
      by_contra h_gt
      push Not at h_gt
      exact h_not_ja (h_pred u h_gt)
  · intro h_eps u h_pr
    unfold epsCA_curves at h_eps
    have h_term_le := iSup_le_iff.mp h_eps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]; exact hjp
    · rw [if_neg hjp] at h_term_le
      exact absurd h_pr (not_lt.mpr h_term_le)

/-- **Probability union bound for finitely-indexed existentials.** For a `Fin t`-indexed
family of predicates `f k : α → Prop`:

  `Pr_{D}[∃ k, f k r] ≤ ∑ k : Fin t, Pr_{D}[f k r]`.

Used in the proof of ABF26 Lemma 4.7. Local to this file; could be promoted to
`ArkLib/Data/Probability/Instances.lean` if reused elsewhere. -/
theorem Pr_exists_Fin_le_sum {α : Type} (D : PMF α) {t : ℕ} (f : Fin t → α → Prop) :
    Pr_{ let r ← D }[ ∃ k, f k r ] ≤ ∑ k, Pr_{ let r ← D }[ f k r ] := by
  classical
  rw [prob_tsum_form_singleton]
  have h_rhs : (∑ k : Fin t, Pr_{ let r ← D }[ f k r ]) =
               ∑ k : Fin t, ∑' r, D r * (if f k r then (1 : ENNReal) else 0) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    exact prob_tsum_form_singleton _ _
  rw [h_rhs]
  -- Swap finite sum with tsum (Fubini for ENNReal, where summability is automatic).
  rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  -- Pull D r out of the inner finite sum.
  have h_mul : ∀ r, (∑ k : Fin t, D r * (if f k r then (1 : ENNReal) else 0)) =
                    D r * (∑ k : Fin t, if f k r then (1 : ENNReal) else 0) :=
    fun r ↦ Finset.mul_sum _ _ _ |>.symm
  rw [tsum_congr (fun r ↦ h_mul r)]
  -- Pointwise bound: `D r * I[∃ k, f k r] ≤ D r * ∑ k, I[f k r]`.
  apply ENNReal.tsum_le_tsum
  intro r
  apply mul_le_mul_of_nonneg_left _ (zero_le _)
  by_cases h : ∃ k, f k r
  · rw [if_pos h]
    obtain ⟨k₀, hk₀⟩ := h
    calc (1 : ENNReal)
        = if f k₀ r then 1 else 0 := by rw [if_pos hk₀]
      _ ≤ ∑ k : Fin t, if f k r then (1 : ENNReal) else 0 :=
          Finset.single_le_sum (f := fun k ↦ if f k r then (1 : ENNReal) else 0)
            (fun _ _ ↦ zero_le _) (Finset.mem_univ k₀)
  · rw [if_neg h]
    exact zero_le _

/-- **Structural half of ABF26 Lemma 4.6 (provable in-tree).** The `mcaEvent` always entails
that the line `u₀ + γ • u₁` is `δ`-close to `C`: the event's witness set `S` (of size
`≥ (1-δ)·n`) carries a codeword `w ∈ C` that agrees with the line on `S`, so `δᵣ(line, w) ≤ δ`
and hence `δᵣ(line, C) ≤ δ`. (This direction needs no unique-decoding hypothesis; it is the
`mcaEvent`-level analogue of the line-close witness used in `epsCA_le_epsMCA`.) -/
theorem mcaEvent_imp_relCloseToCode
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (h : mcaEvent C δ u₀ u₁ γ) :
    δᵣ(u₀ + γ • u₁, C) ≤ δ := by
  classical
  obtain ⟨S, hS_card, ⟨w, hw_mem, hw_eq⟩, _hpair⟩ := h
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨w, hw_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj ↦ ?_, fun hne hj ↦ ?_⟩
  · -- agreement on `S`: `w j = (u₀ + γ • u₁) j`
    simpa [Pi.add_apply, Pi.smul_apply] using (hw_eq j hj).symm
  · -- contradiction: if `j ∈ S` then `w` agrees with the line at `j`
    exact hne (by simpa [Pi.add_apply, Pi.smul_apply] using (hw_eq j hj).symm)

/-- **Provable per-stack dominance on the non-jointly-close branch (no UDR needed).** For a
fixed stack `u` that is *not* jointly `δ`-close, the `epsMCA` body `Pr_γ[mcaEvent]` is bounded
by the `epsCA` body `Pr_γ[line δ-close]`. This is the pointwise probability monotonicity that
follows directly from `mcaEvent_imp_relCloseToCode` (every `mcaEvent` at `γ` makes the line
`δ`-close), with no unique-decoding hypothesis.

This isolates exactly the half of ABF26 Lemma 4.6's hard direction that *is* a pointwise
`iSup`-monotonicity. The complementary `jointProximity` branch — where the `epsCA` body collapses
to `0` while `Pr_γ[mcaEvent]` may stay positive — is the genuine obstruction (see
`epsMCA_eq_epsCA_below_udr`), and is exactly what this lemma's hypothesis excludes. -/
theorem epsMCA_body_le_epsCA_body_of_not_jointProximity
    (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (_hjp : ¬ jointProximity (C := C) (u := u) δ) :
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ] ≤
      Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] := by
  classical
  exact Pr_le_Pr_of_implies _ _ _ fun γ hγ ↦ mcaEvent_imp_relCloseToCode C δ (u 0) (u 1) γ hγ

open Classical in
/-- **Restricted MCA error: the fully-provable slice of ABF26 Lemma 4.6 (no UDR needed).**

`epsMCA` is `⨆ u, Pr_γ[mcaEvent]`. If we *restrict the supremum to the non-jointly-close
stacks* — i.e. zero out every `u` for which `jointProximity C u δ` already holds — then the
resulting error is `≤ ε_ca(C, δ, δ)`, unconditionally (for any `Set`-code `C`).

Pointwise: on a non-jointly-close `u`, the `epsCA` body is the line-close probability and
`epsMCA_body_le_epsCA_body_of_not_jointProximity` gives the bound; on a jointly-close `u`, the
restricted body is `0`. So this is genuine `iSup`-monotonicity and needs no rearrangement.

The gap between this restricted error and the full `ε_mca` is *exactly* the contribution of the
jointly-close stacks, which is the open part of L4.6 (see `epsMCA_eq_epsCA_below_udr`). -/
theorem epsMCA_restricted_le_epsCA (C : Set (ι → A)) (δ : ℝ≥0) :
    (⨆ u : WordStack A (Fin 2) ι,
      if jointProximity (C := C) (u := u) δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]) ≤
    epsCA (F := F) C δ δ := by
  unfold epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ
  · rw [if_pos hjp, if_pos hjp]
  · rw [if_neg hjp, if_neg hjp]
    exact epsMCA_body_le_epsCA_body_of_not_jointProximity C δ u hjp

/-- **Where Approach A (pointwise event-implication) fails for ABF26 Lemma 4.6 — even in the
unique-decoding regime.** *(Formalization note for the UDR case of WHIR Conjecture 1, cf. WHIR
§4.2 [ACFY24] and the Haböck note [Hab25]; the beyond-UDR case is the open prize territory.)*

A natural attempt at the hard direction `ε_mca ≤ ε_ca` is to prove the *pointwise* event
implication `mcaEvent C δ u₀ u₁ γ → caEvent`, i.e. `mcaEvent γ → ¬ jointProximity C u δ`, which
would give `Pr_γ[mcaEvent] ≤ Pr_γ[line δ-close]` and hence `iSup`-monotonicity. **This implication
is false, even under the UDR hypothesis `2·δ·n < δ_min(C)`**, for the following reason.

Suppose both `mcaEvent` (witness set `S`, codeword `w = u₀ + γ·u₁` on `S`, *no* joint pair on `S`)
and `jointProximity` (witness set `S'`, codewords `p₀, p₁ ∈ C` with `p₀ = u₀`, `p₁ = u₁` on `S'`)
hold. Both `S, S'` have size `≥ (1-δ)·n`, so `|S ∩ S'| ≥ n - 2·δ·n`, whose complement has size
`< δ_min(C)` under UDR. On `S ∩ S'` we have `w = u₀ + γ·u₁ = p₀ + γ·p₁`; both `w` and `p₀ + γ·p₁`
are codewords agreeing off a set smaller than `δ_min(C)`, so `w = p₀ + γ·p₁` **everywhere**.

The trap is at the *extra* positions `i ∈ S \ S'`. There `mcaEvent` only gives the **combined**
equation `(u₀ - p₀) i + γ · (u₁ - p₁) i = 0` (from `w i = u₀ i + γ·u₁ i` and `w i = p₀ i + γ·p₁ i`).
This does **not** force `u₀ i = p₀ i` and `u₁ i = p₁ i` individually. Hence `(p₀, p₁)` need not
agree with `(u₀, u₁)` on all of `S`; and since `S ∩ S'` already pins any agreeing codeword pair to
`(p₀, p₁)` (two codewords agreeing on `≥ n - δ_min(C)` positions coincide), there is *no* joint
pair on `S` — i.e. `mcaEvent` co-occurs with `jointProximity`. The `γ` for which this happens are
exactly the solutions of the per-position linear equations `(u₀ - p₀) i = -γ·(u₁ - p₁) i`, a small
but generally **non-empty** `γ`-set, so `Pr_γ[mcaEvent]` stays positive while the `epsCA` body for
this `u` is `0`.

Consequently the pointwise body inequality `epsMCA_body u ≤ epsCA_body u` is false on
jointly-close stacks `u`, and the true bound only holds after the global
dominance/rearrangement of [ACFY24]/[Hab25] (Guruswami–Sudan list-decoder analysis bounding the
exceptional-`γ` set). The provable residue — dominance off the jointly-close stacks — is
`epsMCA_restricted_le_epsCA` above; the structural half `mcaEvent → δᵣ(line, C) ≤ δ` is
`mcaEvent_imp_relCloseToCode`. The full statement remains the documented external admit in
`epsMCA_eq_epsCA_below_udr`.

The single positive UDR fact that the analysis *does* establish — and that any correct proof of
the hard direction relies on — is the codeword-forcing step: under `2·δ·n < δ_min(C)`, two
codewords within relative distance `δ` coincide. That is the kernel-checked content of
`eq_of_relDist_le_of_two_mul_lt_dist` below. -/
theorem eq_of_relDist_le_of_two_mul_lt_dist
    (C : Set (ι → A)) {w₁ w₂ : ι → A} {δ : ℝ≥0}
    (hw₁ : w₁ ∈ C) (hw₂ : w₂ ∈ C)
    (h_close : δᵣ(w₁, w₂) ≤ δ)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist C : ℝ≥0)) :
    w₁ = w₂ := by
  classical
  -- `δᵣ(w₁, w₂) ≤ δ` gives the absolute bound `Δ₀(w₁, w₂) ≤ ⌊δ·n⌋ ≤ δ·n`.
  have h_abs : (Δ₀(w₁, w₂)) ≤ Nat.floor (δ * Fintype.card ι) :=
    (pairRelDist_le_iff_pairDist_le (u := w₁) (v := w₂) δ).mp h_close
  have h_floor_le : (Nat.floor (δ * (Fintype.card ι : ℝ≥0)) : ℝ≥0) ≤ δ * Fintype.card ι :=
    Nat.floor_le (zero_le _)
  -- `δ·n ≤ 2·δ·n < d`, so `Δ₀(w₁, w₂) < d` and `eq_of_lt_dist` closes it.
  have h_dn_lt : δ * (Fintype.card ι : ℝ≥0) < (Code.dist C : ℝ≥0) := by
    have h_le : δ * (Fintype.card ι : ℝ≥0) ≤ 2 * δ * (Fintype.card ι : ℝ≥0) := by
      have : δ ≤ 2 * δ := by
        have : (1 : ℝ≥0) * δ ≤ 2 * δ := by gcongr; norm_num
        simpa using this
      gcongr
    exact lt_of_le_of_lt h_le h_udr
  have h_lt : Δ₀(w₁, w₂) < Code.dist C := by
    have h1 : (Δ₀(w₁, w₂) : ℝ≥0) ≤ δ * Fintype.card ι :=
      le_trans (by exact_mod_cast h_abs) h_floor_le
    have h2 : (Δ₀(w₁, w₂) : ℝ≥0) < (Code.dist C : ℝ≥0) := lt_of_le_of_lt h1 h_dn_lt
    exact_mod_cast h2
  exact eq_of_lt_dist hw₁ hw₂ h_lt

open Classical in
/-- **Kernel-checked core of the obstruction: in UDR the `mcaEvent` witness is forced.**

Concretely substantiating the prose analysis above. Assume the UDR hypothesis `2·δ·n < δ_min(C)`,
a stack `u` for which `jointProximity C u δ` holds (so `jointAgreement` provides a codeword pair
`p₀, p₁ ∈ C` agreeing with `(u 0, u 1)` on a set `S'` of size `≥ (1-δ)·n`), and an `mcaEvent` at
`γ` with witness set `S` and codeword `w ∈ C`. Then **`w = p₀ + γ·p₁`** — the line's `mcaEvent`
witness coincides with the unique close combined codeword.

Proof: `w = u 0 + γ·(u 1)` on `S` and `p₀ + γ·p₁ = u 0 + γ·(u 1)` on `S'` (because `p₀ = u 0`,
`p₁ = u 1` there). On `S ∩ S'` both codewords equal the line, hence agree; the complement of
`S ∩ S'` is contained in the union of the two `≤ ⌊δ·n⌋`-sized disagreement sets, so
`Δ₀(w, p₀ + γ·p₁) ≤ 2·⌊δ·n⌋ ≤ 2·δ·n < δ_min(C)`, and `eq_of_lt_dist` forces equality.

This is the step common to every correct proof of L4.6's hard direction; what it does *not*
give — and where Approach A dies — is that `(p₀, p₁)` agrees with `(u 0, u 1)` on the *extra*
positions `S \ S'`, since there only the combined equation `w = p₀ + γ·p₁ = u 0 + γ·(u 1)` is
available, not the separate ones. -/
theorem mcaEvent_witness_eq_combined_of_jointProximity_udr
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) (γ : F)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist ((C : Set (ι → A))) : ℝ≥0))
    (h_jp : jointProximity (C := (C : Set (ι → A))) (u := u) δ)
    {S : Finset ι} {w : ι → A}
    (hw_mem : w ∈ (C : Set (ι → A)))
    (hS_card : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (hw_line : ∀ i ∈ S, w i = u 0 i + γ • u 1 i) :
    ∃ p₀ ∈ (C : Set (ι → A)), ∃ p₁ ∈ (C : Set (ι → A)),
      (∀ i ∈ S, w i = u 0 i + γ • u 1 i) ∧ w = p₀ + γ • p₁ := by
  classical
  -- Extract the jointAgreement witnesses `p₀, p₁` on a set `S'`.
  rw [← jointAgreement_iff_jointProximity] at h_jp
  obtain ⟨S', hS'_card, p, hp⟩ := h_jp
  set p₀ := p 0
  set p₁ := p 1
  have hp₀_mem : p₀ ∈ (C : Set (ι → A)) := (hp 0).1
  have hp₁_mem : p₁ ∈ (C : Set (ι → A)) := (hp 1).1
  -- `p₀ = u 0` and `p₁ = u 1` on `S'`.
  have h_agree_S' : ∀ j ∈ S', p₀ j = u 0 j ∧ p₁ j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have : j ∈ Finset.filter (fun k ↦ p 0 k = u 0 k) Finset.univ := (hp 0).2 hj
      exact (Finset.mem_filter.mp this).2
    · have : j ∈ Finset.filter (fun k ↦ p 1 k = u 1 k) Finset.univ := (hp 1).2 hj
      exact (Finset.mem_filter.mp this).2
  refine ⟨p₀, hp₀_mem, p₁, hp₁_mem, hw_line, ?_⟩
  -- `p₀ + γ • p₁ ∈ C` (submodule closure).
  have hcomb_mem : (p₀ + γ • p₁) ∈ (C : Set (ι → A)) := C.add_mem hp₀_mem (C.smul_mem γ hp₁_mem)
  -- Show `w` and `p₀ + γ • p₁` agree on `S ∩ S'`; bound the disagreement set by `2·⌊δ·n⌋`.
  set e : ℕ := Nat.floor (δ * (Fintype.card ι : ℝ≥0)) with he
  -- The complement of `S` has card `≤ e` and likewise for `S'`.
  have hScompl : (Finset.univ \ S).card ≤ e := by
    have hsub : Fintype.card ι - e ≤ S.card := by
      have := (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S.card δ).mpr hS_card
      simpa [he] using this
    have hle : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    omega
  have hS'compl : (Finset.univ \ S').card ≤ e := by
    have hsub : Fintype.card ι - e ≤ S'.card := by
      have := (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S'.card δ).mpr
        hS'_card
      simpa [he] using this
    have hle : S'.card ≤ Fintype.card ι := Finset.card_le_univ S'
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    omega
  -- Disagreement positions of `w` vs `p₀ + γ • p₁` are contained in `(univ\S) ∪ (univ\S')`.
  have h_dis_sub :
      Finset.univ.filter (fun i ↦ w i ≠ (p₀ + γ • p₁) i) ⊆
        (Finset.univ \ S) ∪ (Finset.univ \ S') := by
    intro i hi
    rw [Finset.mem_filter] at hi
    by_contra hni
    rw [Finset.mem_union] at hni
    push Not at hni
    obtain ⟨hiS, hiS'⟩ := hni
    have hiS_mem : i ∈ S := by
      by_contra h; exact hiS (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
    have hiS'_mem : i ∈ S' := by
      by_contra h; exact hiS' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
    -- On `S ∩ S'`: `w i = u 0 i + γ • u 1 i = p₀ i + γ • p₁ i`.
    obtain ⟨hp0i, hp1i⟩ := h_agree_S' i hiS'_mem
    have : w i = (p₀ + γ • p₁) i := by
      rw [hw_line i hiS_mem]
      simp [Pi.add_apply, Pi.smul_apply, hp0i, hp1i]
    exact hi.2 this
  -- Hence `Δ₀(w, p₀ + γ • p₁) ≤ 2·e`.
  have h_ham_le : Δ₀(w, p₀ + γ • p₁) ≤ 2 * e := by
    have h1 : Δ₀(w, p₀ + γ • p₁) ≤ ((Finset.univ \ S) ∪ (Finset.univ \ S')).card := by
      unfold hammingDist
      exact le_trans (Finset.card_le_card h_dis_sub) (le_refl _)
    have h2 : ((Finset.univ \ S) ∪ (Finset.univ \ S')).card ≤ 2 * e := by
      refine le_trans (Finset.card_union_le _ _) ?_
      omega
    exact le_trans h1 h2
  -- `2·e ≤ 2·δ·n < d`, so `Δ₀ < d` and `eq_of_lt_dist` concludes.
  have h_lt : Δ₀(w, p₀ + γ • p₁) < Code.dist (C : Set (ι → A)) := by
    have he_le : (e : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
      rw [he]; exact Nat.floor_le (zero_le _)
    have h2e : (2 * e : ℝ≥0) ≤ 2 * δ * (Fintype.card ι : ℝ≥0) := by
      have : (2 : ℝ≥0) * (e : ℝ≥0) ≤ 2 * (δ * (Fintype.card ι : ℝ≥0)) := by gcongr
      simpa [mul_assoc] using this
    have h2e' : ((Δ₀(w, p₀ + γ • p₁) : ℕ) : ℝ≥0) < (Code.dist (C : Set (ι → A)) : ℝ≥0) := by
      have hcast : ((Δ₀(w, p₀ + γ • p₁) : ℕ) : ℝ≥0) ≤ (2 * e : ℝ≥0) := by exact_mod_cast h_ham_le
      exact lt_of_le_of_lt (le_trans hcast h2e) h_udr
    exact_mod_cast h2e'
  exact eq_of_lt_dist hw_mem hcomb_mem h_lt

open Classical in
/-- **The difference stack of a jointly-proximate stack has a uniformly close line.**

If `jointProximity C u δ` holds (so a codeword pair `p₀, p₁ ∈ C` agrees with `(u 0, u 1)` on a
set `S'` of size `≥ (1-δ)·n`), then the *fixed, `γ`-independent* difference stack
`d := (u 0 - p₀, u 1 - p₁)` has the property that for **every** `γ`, the difference line
`d 0 + γ·d 1 = (u 0 - p₀) + γ·(u 1 - p₁)` is `δ`-close to `C` — in fact close to the zero
codeword.

Proof: on `S'` (size `≥ (1-δ)·n`) we have `p₀ = u 0` and `p₁ = u 1`, so the difference line
vanishes there; `0 ∈ C` and `S'` is large, hence `δᵣ(diff-line, C) ≤ δ`.

This is the structural fact behind the ACFY25/[Hab25] reduction: the codeword pair `(p₀, p₁)`
realizing `jointProximity` is `γ`-independent, so the exceptional `γ` of the `mcaEvent` on a
jointly-close `u` all live inside the (already-`δ`-close) line family of one *fixed* difference
stack. Concretely it shows the difference stack `d` is itself jointly `δ`-close to `C` (witnessed
by the pair `(0,0)` on `S'`), which is exactly *why* the pointwise CA body for `d` collapses to
`0` and the count of exceptional `γ` cannot be read off without the global list-decoding
(GS/PS) machinery — see `epsMCA_le_epsCA_add_jointlyProximateContribution`. -/
theorem jointProximity_diffStack_line_close
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (h_jp : jointProximity (C := (C : Set (ι → A))) (u := u) δ) :
    ∃ p₀ ∈ (C : Set (ι → A)), ∃ p₁ ∈ (C : Set (ι → A)),
      ∀ γ : F, δᵣ((u 0 - p₀) + γ • (u 1 - p₁), (C : Set (ι → A))) ≤ δ := by
  classical
  -- Extract the `γ`-independent jointAgreement witnesses `p₀, p₁` on `S'`.
  rw [← jointAgreement_iff_jointProximity] at h_jp
  obtain ⟨S', hS'_card, p, hp⟩ := h_jp
  set p₀ := p 0 with hp₀_def
  set p₁ := p 1 with hp₁_def
  have hp₀_mem : p₀ ∈ (C : Set (ι → A)) := (hp 0).1
  have hp₁_mem : p₁ ∈ (C : Set (ι → A)) := (hp 1).1
  refine ⟨p₀, hp₀_mem, p₁, hp₁_mem, ?_⟩
  intro γ
  -- On `S'` (size ≥(1-δ)n): `p₀ = u 0`, `p₁ = u 1`, so the difference line vanishes there,
  -- and `0 ∈ C`, giving `δᵣ(diff-line, C) ≤ δ`.
  have h_agree_S' : ∀ j ∈ S', p₀ j = u 0 j ∧ p₁ j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have : j ∈ Finset.filter (fun k ↦ p 0 k = u 0 k) Finset.univ := (hp 0).2 hj
      exact (Finset.mem_filter.mp this).2
    · have : j ∈ Finset.filter (fun k ↦ p 1 k = u 1 k) Finset.univ := (hp 1).2 hj
      exact (Finset.mem_filter.mp this).2
  -- The difference line vanishes on `S'`.
  have h_zero_S' : ∀ j ∈ S', ((u 0 - p₀) + γ • (u 1 - p₁)) j = (0 : ι → A) j := by
    intro j hj
    obtain ⟨h0, h1⟩ := h_agree_S' j hj
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply]
    rw [h0, h1]
    simp
  -- `0 ∈ C` and `S'` is large, so `δᵣ(diff-line, C) ≤ δ`.
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨0, C.zero_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S', (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS'_card, ?_⟩
  intro j
  refine ⟨fun hj ↦ (h_zero_S' j hj), fun hne hj ↦ hne (h_zero_S' j hj)⟩

open Classical in
/-- **Normalization step: jointly-proximate `mcaEvent` reduces to a difference-stack `mcaEvent`
(kernel-checked, UDR).**

For a jointly-`δ`-close stack `u` under UDR there is a *fixed, `γ`-independent* codeword pair
`(p₀, p₁) ∈ C²` (the `jointProximity` witnesses) such that for **every** `γ`,

  `mcaEvent C δ (u 0) (u 1) γ → mcaEvent C δ (u 0 - p₀) (u 1 - p₁) γ`.

i.e. the `mcaEvent` of `u` transfers verbatim to the *difference stack* `d := (u 0 - p₀,
u 1 - p₁)`, which is "close to `0`" (it vanishes on the `jointProximity` set `S'`).

Proof, given an `mcaEvent` at `γ` with witness `S`, codeword `w`:
* **Forcing** (`mcaEvent_witness_eq_combined_of_jointProximity_udr`, needs UDR): `w = p₀ + γ·p₁`
  everywhere. On `S` also `w = u 0 + γ·u 1`, so the difference line
  `d 0 + γ·d 1 = (u 0 + γ·u 1) - (p₀ + γ·p₁) = w - w = 0` on `S`. The zero codeword `0 ∈ C`
  therefore witnesses the line clause for `d` on the *same* `S`.
* **No joint pair for `d` on `S`**: if some `(c₀, c₁) ∈ C²` agreed with `(d 0, d 1)` on `S`, then
  `(p₀ + c₀, p₁ + c₁) ∈ C²` (submodule closure) would agree with `(u 0, u 1)` on `S`
  (`u i = p i + d i = p i + c i` there), contradicting the no-joint-pair clause of the original
  `mcaEvent`.

This is the ACFY25/[Hab25] *normalization* (subtract the unique close codeword pair): it shows
the entire jointly-proximate `mcaEvent` mass is carried by difference stacks `d` whose line
`d 0 + γ·d 1` *vanishes* on a size-`≥ (1-δ)·n` set while `d` is **not** the zero pair there.
Bounding the `γ` for which a nonzero-on-`S` difference line vanishes on `S` is exactly the
list-decoding (Guruswami–Sudan / [Hab25]) root count — the step still missing from the tree, and
the reason the residual `jointlyProximateContribution ≤ ε_ca` cannot yet be closed in-file. -/
theorem jointProximity_mcaEvent_imp_diffStack_mcaEvent_udr
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist ((C : Set (ι → A))) : ℝ≥0))
    (h_jp : jointProximity (C := (C : Set (ι → A))) (u := u) δ) :
    ∃ p₀ ∈ (C : Set (ι → A)), ∃ p₁ ∈ (C : Set (ι → A)),
      ∀ γ : F, mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ →
        mcaEvent (C : Set (ι → A)) δ (u 0 - p₀) (u 1 - p₁) γ := by
  classical
  -- Re-extract the `γ`-independent jointAgreement witnesses `p₀, p₁` on `S'`.
  have h_jp' := h_jp
  rw [← jointAgreement_iff_jointProximity] at h_jp'
  obtain ⟨S', hS'_card, p, hp⟩ := h_jp'
  set p₀ := p 0 with hp₀_def
  set p₁ := p 1 with hp₁_def
  have hp₀_mem : p₀ ∈ (C : Set (ι → A)) := (hp 0).1
  have hp₁_mem : p₁ ∈ (C : Set (ι → A)) := (hp 1).1
  -- Pointwise agreement of `p` with `u` on `S'`.
  have h_agree_S' : ∀ j ∈ S', p₀ j = u 0 j ∧ p₁ j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have : j ∈ Finset.filter (fun k ↦ p 0 k = u 0 k) Finset.univ := (hp 0).2 hj
      exact (Finset.mem_filter.mp this).2
    · have : j ∈ Finset.filter (fun k ↦ p 1 k = u 1 k) Finset.univ := (hp 1).2 hj
      exact (Finset.mem_filter.mp this).2
  refine ⟨p₀, hp₀_mem, p₁, hp₁_mem, ?_⟩
  intro γ h_event
  obtain ⟨S, hS_card, ⟨w, hw_mem, hw_line⟩, hno_pair⟩ := h_event
  -- Forcing for *this* `p`: `w = p₀ + γ•p₁`. Replicate the `eq_of_lt_dist` argument (the content
  -- of `mcaEvent_witness_eq_combined_of_jointProximity_udr`) directly with the `p` witnesses, so
  -- we avoid any `q = p` identification.
  have hcomb_mem : (p₀ + γ • p₁) ∈ (C : Set (ι → A)) := C.add_mem hp₀_mem (C.smul_mem γ hp₁_mem)
  set e : ℕ := Nat.floor (δ * (Fintype.card ι : ℝ≥0)) with he
  have hScompl : (Finset.univ \ S).card ≤ e := by
    have hsub : Fintype.card ι - e ≤ S.card := by
      have := (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S.card δ).mpr hS_card
      simpa [he] using this
    have hle : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    omega
  have hS'compl : (Finset.univ \ S').card ≤ e := by
    have hsub : Fintype.card ι - e ≤ S'.card := by
      have := (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S'.card δ).mpr
        hS'_card
      simpa [he] using this
    have hle : S'.card ≤ Fintype.card ι := Finset.card_le_univ S'
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    omega
  have h_dis_sub :
      Finset.univ.filter (fun i ↦ w i ≠ (p₀ + γ • p₁) i) ⊆
        (Finset.univ \ S) ∪ (Finset.univ \ S') := by
    intro i hi
    rw [Finset.mem_filter] at hi
    by_contra hni
    rw [Finset.mem_union] at hni
    push Not at hni
    obtain ⟨hiS, hiS'⟩ := hni
    have hiS_mem : i ∈ S := by
      by_contra h; exact hiS (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
    have hiS'_mem : i ∈ S' := by
      by_contra h; exact hiS' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
    obtain ⟨hp0i, hp1i⟩ := h_agree_S' i hiS'_mem
    have : w i = (p₀ + γ • p₁) i := by
      rw [hw_line i hiS_mem]
      simp [Pi.add_apply, Pi.smul_apply, hp0i, hp1i]
    exact hi.2 this
  have h_ham_le : Δ₀(w, p₀ + γ • p₁) ≤ 2 * e := by
    have h1 : Δ₀(w, p₀ + γ • p₁) ≤ ((Finset.univ \ S) ∪ (Finset.univ \ S')).card := by
      unfold hammingDist
      exact le_trans (Finset.card_le_card h_dis_sub) (le_refl _)
    have h2 : ((Finset.univ \ S) ∪ (Finset.univ \ S')).card ≤ 2 * e := by
      refine le_trans (Finset.card_union_le _ _) ?_
      omega
    exact le_trans h1 h2
  have h_lt : Δ₀(w, p₀ + γ • p₁) < Code.dist (C : Set (ι → A)) := by
    have he_le : (e : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
      rw [he]; exact Nat.floor_le (zero_le _)
    have h2e : (2 * e : ℝ≥0) ≤ 2 * δ * (Fintype.card ι : ℝ≥0) := by
      have : (2 : ℝ≥0) * (e : ℝ≥0) ≤ 2 * (δ * (Fintype.card ι : ℝ≥0)) := by gcongr
      simpa [mul_assoc] using this
    have h2e' : ((Δ₀(w, p₀ + γ • p₁) : ℕ) : ℝ≥0) < (Code.dist (C : Set (ι → A)) : ℝ≥0) := by
      have hcast : ((Δ₀(w, p₀ + γ • p₁) : ℕ) : ℝ≥0) ≤ (2 * e : ℝ≥0) := by exact_mod_cast h_ham_le
      exact lt_of_le_of_lt (le_trans hcast h2e) h_udr
    exact_mod_cast h2e'
  have hpw : w = p₀ + γ • p₁ := eq_of_lt_dist hw_mem hcomb_mem h_lt
  -- For `d`, build the `mcaEvent`: witness `S`, codeword `0`, no joint pair.
  refine ⟨S, hS_card, ⟨0, C.zero_mem, ?_⟩, ?_⟩
  · -- `0 = (u0-p₀) + γ•(u1-p₁)` on `S`: from `w = u0+γu1` on `S` and `w = p₀+γ•p₁` globally.
    intro i hi
    have hwi : w i = u 0 i + γ • u 1 i := hw_line i hi
    have hwi' : w i = p₀ i + γ • p₁ i := by rw [hpw]; simp [Pi.add_apply, Pi.smul_apply]
    have heq : u 0 i + γ • u 1 i = p₀ i + γ • p₁ i := by rw [← hwi, hwi']
    simp only [Pi.zero_apply, Pi.sub_apply]
    rw [smul_sub]
    -- goal: `0 = (u0 i - p₀ i) + (γ•u1 i - γ•p₁ i)`; rearrange to a difference and use `heq`.
    have hrearr : u 0 i - p₀ i + (γ • u 1 i - γ • p₁ i)
        = (u 0 i + γ • u 1 i) - (p₀ i + γ • p₁ i) := by abel
    rw [hrearr, heq, sub_self]
  · -- No joint pair for `d` on `S`: transfer to a joint pair for `u`, contradicting `hno_pair`.
    intro h_pair_d
    apply hno_pair
    obtain ⟨c₀, hc₀_mem, c₁, hc₁_mem, h_agree_d⟩ := h_pair_d
    refine ⟨p₀ + c₀, C.add_mem hp₀_mem hc₀_mem, p₁ + c₁, C.add_mem hp₁_mem hc₁_mem, ?_⟩
    intro i hi
    obtain ⟨hd0, hd1⟩ := h_agree_d i hi
    -- `(p₀+c₀) i = p₀ i + c₀ i = p₀ i + (u0-p₀) i = u0 i` ; likewise for index 1.
    refine ⟨?_, ?_⟩
    · have hc : c₀ i = u 0 i - p₀ i := by simpa [Pi.sub_apply] using hd0
      simp only [Pi.add_apply]
      rw [hc]; abel
    · have hc : c₁ i = u 1 i - p₁ i := by simpa [Pi.sub_apply] using hd1
      simp only [Pi.add_apply]
      rw [hc]; abel

open Classical in
/-- **The jointly-proximate contribution to `ε_mca`.** Explicit name for the part of the `ε_mca`
supremum that the in-tree machinery cannot bound against `ε_ca`: the worst-case `mcaEvent`
probability over the stacks `u` that *are* jointly `δ`-close to `C` (where the `ε_ca` body is
`0`). On the non-jointly-close stacks the bound `Pr_γ[mcaEvent] ≤ Pr_γ[line δ-close] ≤ ε_ca`
is already proved (`epsMCA_restricted_le_epsCA`); this term isolates exactly the residue.

By `epsMCA_le_epsCA_add_jointlyProximateContribution`,
`ε_mca(C, δ) ≤ ε_ca(C, δ, δ) + jointlyProximateContribution C δ`. ABF26 Lemma 4.6 is the
statement that this contribution is itself `≤ ε_ca` in the UDR (so that the sum collapses back to
`ε_ca`); proving that requires the global Guruswami–Sudan/[Hab25] list-decoding bound on the
exceptional-`γ` set of the fixed difference stack `(u 0 - p₀, u 1 - p₁)` (see
`jointProximity_diffStack_line_close`), which is not yet available in-tree. -/
noncomputable def jointlyProximateContribution (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if jointProximity (C := C) (u := u) δ then
      Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]
    else (0 : ENNReal)

open Classical in
/-- **Kernel-checked per-stack count step for the jointly-proximate `mcaEvent` mass (UDR, the
[AHIV17]/[Hab25] Lemma 1 line-counting argument over symbol space `Σ = Fˢ`).**

For a jointly-`δ`-close stack `u` under UDR (`2·δ·n < δ_min(C)`), with `jointProximity`
witnesses `(p₀, p₁) ∈ C²` on a set `S'` of size `≥ (1-δ)·n`, **every** `γ` carrying an
`mcaEvent` is one of the per-position equations of the *fixed difference stack*
`(d₀, d₁) := (u 0 - p₀, u 1 - p₁)`: there is a coordinate `i ∉ S'` at which `d₁ i ≠ 0` and
`γ • d₁ i = - d₀ i`. There are at most `⌊δ·n⌋` such coordinates (`|univ \ S'| ≤ ⌊δ·n⌋`).

Proof: by `mcaEvent_witness_eq_combined_of_jointProximity_udr`-style forcing the `mcaEvent`
codeword `w` equals `p₀ + γ·p₁` everywhere; the no-joint-pair clause hands a position `i ∈ S`
where `(u 0 i, u 1 i) ≠ (p₀ i, p₁ i)`, necessarily `i ∉ S'`; at `i` the line equality
`w i = u 0 i + γ·u 1 i = p₀ i + γ·p₁ i` rearranges to `d₀ i + γ • d₁ i = 0`, and
`(d₀ i, d₁ i) ≠ (0,0)` forces `d₁ i ≠ 0`.

This is the *coordinate*-level count behind [Hab25] Lemma 1 / [AHIV17, BKS18]: each disagreement
coordinate kills **at most one** `γ` (the solution of its linear functional). The
`NoZeroSMulDivisors F A` instance — automatic for the paper's symbol space `Σ = Fˢ`, a finite
`F`-vector space — is exactly what makes `γ • d₁ i = - d₀ i` have a unique `γ` per coordinate
(used in `jointlyProximate_mcaEvent_Pr_le_card_div_udr`). -/
theorem jointlyProximate_mcaEvent_imp_exists_pos_udr [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist ((C : Set (ι → A))) : ℝ≥0))
    (h_jp : jointProximity (C := (C : Set (ι → A))) (u := u) δ) :
    ∃ S' : Finset ι, ∃ p₀ : ι → A, ∃ p₁ : ι → A,
      (Finset.univ \ S').card ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0)) ∧
      ∀ γ : F, mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ →
        ∃ i ∈ (Finset.univ \ S'),
          (u 1 i - p₁ i ≠ 0) ∧ γ • (u 1 i - p₁ i) = -(u 0 i - p₀ i) := by
  classical
  have h_jp' := h_jp
  rw [← jointAgreement_iff_jointProximity] at h_jp'
  obtain ⟨S', hS'_card, p, hp⟩ := h_jp'
  set p₀ := p 0 with hp₀_def
  set p₁ := p 1 with hp₁_def
  have hp₀_mem : p₀ ∈ (C : Set (ι → A)) := (hp 0).1
  have hp₁_mem : p₁ ∈ (C : Set (ι → A)) := (hp 1).1
  have h_agree_S' : ∀ j ∈ S', p₀ j = u 0 j ∧ p₁ j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have : j ∈ Finset.filter (fun k ↦ p 0 k = u 0 k) Finset.univ := (hp 0).2 hj
      exact (Finset.mem_filter.mp this).2
    · have : j ∈ Finset.filter (fun k ↦ p 1 k = u 1 k) Finset.univ := (hp 1).2 hj
      exact (Finset.mem_filter.mp this).2
  set e : ℕ := Nat.floor (δ * (Fintype.card ι : ℝ≥0)) with he
  have hS'compl : (Finset.univ \ S').card ≤ e := by
    have hsub : Fintype.card ι - e ≤ S'.card := by
      have := (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S'.card δ).mpr
        hS'_card
      simpa [he] using this
    have hle : S'.card ≤ Fintype.card ι := Finset.card_le_univ S'
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    omega
  refine ⟨S', p₀, p₁, hS'compl, ?_⟩
  intro γ h_event
  obtain ⟨S, hS_card, ⟨w, hw_mem, hw_line⟩, hno_pair⟩ := h_event
  have hcomb_mem : (p₀ + γ • p₁) ∈ (C : Set (ι → A)) :=
    C.add_mem hp₀_mem (C.smul_mem γ hp₁_mem)
  have hScompl : (Finset.univ \ S).card ≤ e := by
    have hsub : Fintype.card ι - e ≤ S.card := by
      have := (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S.card δ).mpr
        hS_card
      simpa [he] using this
    have hle : S.card ≤ Fintype.card ι := Finset.card_le_univ S
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    omega
  have h_dis_sub :
      Finset.univ.filter (fun i ↦ w i ≠ (p₀ + γ • p₁) i) ⊆
        (Finset.univ \ S) ∪ (Finset.univ \ S') := by
    intro i hi
    rw [Finset.mem_filter] at hi
    by_contra hni
    rw [Finset.mem_union] at hni
    push Not at hni
    obtain ⟨hiS, hiS'⟩ := hni
    have hiS_mem : i ∈ S := by
      by_contra h; exact hiS (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
    have hiS'_mem : i ∈ S' := by
      by_contra h; exact hiS' (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
    obtain ⟨hp0i, hp1i⟩ := h_agree_S' i hiS'_mem
    have : w i = (p₀ + γ • p₁) i := by
      rw [hw_line i hiS_mem]
      simp [Pi.add_apply, Pi.smul_apply, hp0i, hp1i]
    exact hi.2 this
  have h_ham_le : Δ₀(w, p₀ + γ • p₁) ≤ 2 * e := by
    have h1 : Δ₀(w, p₀ + γ • p₁) ≤ ((Finset.univ \ S) ∪ (Finset.univ \ S')).card := by
      unfold hammingDist
      exact le_trans (Finset.card_le_card h_dis_sub) (le_refl _)
    have h2 : ((Finset.univ \ S) ∪ (Finset.univ \ S')).card ≤ 2 * e := by
      refine le_trans (Finset.card_union_le _ _) ?_
      omega
    exact le_trans h1 h2
  have h_lt : Δ₀(w, p₀ + γ • p₁) < Code.dist (C : Set (ι → A)) := by
    have he_le : (e : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
      rw [he]; exact Nat.floor_le (zero_le _)
    have h2e : (2 * e : ℝ≥0) ≤ 2 * δ * (Fintype.card ι : ℝ≥0) := by
      have : (2 : ℝ≥0) * (e : ℝ≥0) ≤ 2 * (δ * (Fintype.card ι : ℝ≥0)) := by gcongr
      simpa [mul_assoc] using this
    have h2e' : ((Δ₀(w, p₀ + γ • p₁) : ℕ) : ℝ≥0) < (Code.dist (C : Set (ι → A)) : ℝ≥0) := by
      have hcast : ((Δ₀(w, p₀ + γ • p₁) : ℕ) : ℝ≥0) ≤ (2 * e : ℝ≥0) := by exact_mod_cast h_ham_le
      exact lt_of_le_of_lt (le_trans hcast h2e) h_udr
    exact_mod_cast h2e'
  have hpw : w = p₀ + γ • p₁ := eq_of_lt_dist hw_mem hcomb_mem h_lt
  have h_exists_disagree : ∃ i ∈ S, ¬ (p₀ i = u 0 i ∧ p₁ i = u 1 i) := by
    by_contra h_all
    push Not at h_all
    exact hno_pair ⟨p₀, hp₀_mem, p₁, hp₁_mem, fun i hi ↦ h_all i hi⟩
  obtain ⟨i, hiS, hdisagree⟩ := h_exists_disagree
  have hiS' : i ∉ S' := fun h ↦ hdisagree (h_agree_S' i h)
  have hi_mem_T : i ∈ Finset.univ \ S' := Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiS'⟩
  have hwi : w i = u 0 i + γ • u 1 i := hw_line i hiS
  have hwi' : w i = p₀ i + γ • p₁ i := by rw [hpw]; simp [Pi.add_apply, Pi.smul_apply]
  have heq : (u 0 i - p₀ i) + γ • (u 1 i - p₁ i) = 0 := by
    have he0 : u 0 i + γ • u 1 i = p₀ i + γ • p₁ i := by rw [← hwi, hwi']
    rw [smul_sub]
    rw [show u 0 i - p₀ i + (γ • u 1 i - γ • p₁ i)
        = (u 0 i + γ • u 1 i) - (p₀ i + γ • p₁ i) by abel, he0, sub_self]
  have hd1_ne : u 1 i - p₁ i ≠ 0 := by
    intro h0
    apply hdisagree
    rw [h0] at heq
    simp only [smul_zero, add_zero] at heq
    refine ⟨?_, ?_⟩
    · rw [sub_eq_zero] at heq; exact heq.symm
    · rw [sub_eq_zero] at h0; exact h0.symm
  refine ⟨i, hi_mem_T, hd1_ne, ?_⟩
  have hh := heq
  rw [add_comm] at hh
  rw [eq_neg_iff_add_eq_zero]
  exact hh

open Classical in
/-- **Kernel-checked explicit bound on the per-stack jointly-proximate `mcaEvent` mass (UDR).**

For a jointly-`δ`-close stack `u` under UDR, the `mcaEvent` probability is bounded by the
unique-decoding count `⌊δ·n⌋ / |F|`:

  `Pr_γ[mcaEvent C δ (u 0) (u 1) γ] ≤ ⌊δ·n⌋ / |F|`.

This is the in-tree realization of the [AHIV17]/[Hab25] Lemma 1 line-counting bound in the
unique-decoding regime. The bad-`γ` set injects into the (`≤ ⌊δ·n⌋`-many) coordinates outside
the `jointProximity` agreement set `S'` via `jointlyProximate_mcaEvent_imp_exists_pos_udr`: the
choice map `γ ↦ (witnessing coordinate i)` is **injective** because two distinct `γ`'s solving
`γ • d₁ i = - d₀ i` at the *same* coordinate `i` (with `d₁ i ≠ 0`) would coincide
(`NoZeroSMulDivisors F A`, automatic for `Σ = Fˢ`). Hence
`#{γ : mcaEvent} ≤ |univ \ S'| ≤ ⌊δ·n⌋`, and `prob_uniform_eq_card_filter_div_card` gives the
probability bound.

Note this is a *count* of bad `γ`, **not** a pointwise event-implication: the bad set is
genuinely nonempty in general (see the obstruction note at `eq_of_relDist_le_of_two_mul_lt_dist`),
so the bound cannot be improved to `0`. It is the sharpest in-tree statement about the residual;
what it does **not** give is the global dominance `⌊δ·n⌋/|F| ≤ ε_ca` (see
`epsMCA_eq_epsCA_below_udr`). -/
theorem jointlyProximate_mcaEvent_Pr_le_card_div_udr [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist ((C : Set (ι → A))) : ℝ≥0))
    (h_jp : jointProximity (C := (C : Set (ι → A))) (u := u) δ) :
    Pr_{let γ ← $ᵖ F}[mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ] ≤
      ((Nat.floor (δ * (Fintype.card ι : ℝ≥0)) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ENNReal) := by
  classical
  obtain ⟨S', p₀, p₁, hScard, hpos⟩ :=
    jointlyProximate_mcaEvent_imp_exists_pos_udr C δ u h_udr h_jp
  set T : Finset ι := Finset.univ \ S' with hT
  have hchoice : ∀ γ : F, mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ →
      ∃ i ∈ T, (u 1 i - p₁ i ≠ 0) ∧ γ • (u 1 i - p₁ i) = -(u 0 i - p₀ i) := hpos
  have hcard_le :
      (Finset.filter (fun γ ↦ mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ)
        (Finset.univ : Finset F)).card ≤ T.card := by
    have hwit : ∀ γ ∈ Finset.filter (fun γ ↦ mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ)
        (Finset.univ : Finset F),
        ∃ i ∈ T, (u 1 i - p₁ i ≠ 0) ∧ γ • (u 1 i - p₁ i) = -(u 0 i - p₀ i) := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      exact hchoice γ hγ.2
    choose! f hf_mem hf_ne hf_eq using hwit
    apply Finset.card_le_card_of_injOn f
    · intro γ hγ; exact hf_mem γ hγ
    · intro γ₁ h1 γ₂ h2 hf
      have he1 := hf_eq γ₁ h1
      have he2 := hf_eq γ₂ h2
      have hne := hf_ne γ₁ h1
      rw [hf] at he1 hne
      have hsmul_eq : γ₁ • (u 1 (f γ₂) - p₁ (f γ₂)) = γ₂ • (u 1 (f γ₂) - p₁ (f γ₂)) := by
        rw [he1, he2]
      have hsub : (γ₁ - γ₂) • (u 1 (f γ₂) - p₁ (f γ₂)) = 0 := by
        rw [sub_smul, hsmul_eq, sub_self]
      rcases smul_eq_zero.mp hsub with hz | hz
      · exact sub_eq_zero.mp hz
      · exact absurd hz hne
  have hTcard : T.card ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0)) := hScard
  have hcard_le' :
      (Finset.filter (fun γ ↦ mcaEvent (C : Set (ι → A)) δ (u 0) (u 1) γ)
        (Finset.univ : Finset F)).card ≤ Nat.floor (δ * (Fintype.card ι : ℝ≥0)) :=
    le_trans hcard_le hTcard
  rw [prob_uniform_eq_card_filter_div_card]
  gcongr

open Classical in
/-- **Kernel-checked explicit bound on the whole jointly-proximate contribution (UDR).**

`jointlyProximateContribution C δ ≤ ⌊δ·n⌋ / |F|`, the [AHIV17]/[Hab25] Lemma 1 unique-decoding
count. This is the supremum form of `jointlyProximate_mcaEvent_Pr_le_card_div_udr`: every
jointly-close body is bounded by `⌊δ·n⌋/|F|`, every non-jointly-close body is `0`.

This is the sharpest in-tree statement isolating the residual of ABF26 Lemma 4.6: combined with
`epsMCA_le_max_epsCA_jointlyProximateContribution` it gives
`ε_mca(C,δ) ≤ max (ε_ca(C,δ,δ)) (⌊δ·n⌋/|F|)`. The only thing missing for the full equality
`ε_mca = ε_ca` is the **global dominance** `⌊δ·n⌋/|F| ≤ ε_ca(C,δ,δ)` — i.e. that some
*non*-jointly-close stack realizes line-closeness probability at least the per-coordinate bad-`γ`
count. That dominance is precisely the [ACFY25, Lemma 4.10] rearrangement (the Guruswami–Sudan /
[Hab25] analysis bounding the exceptional-`γ` set against the CA error); it is *not* a
consequence of the per-stack count above (`ε_ca` can be strictly smaller than `⌊δ·n⌋/|F|`), and
remains the documented external residual in `epsMCA_eq_epsCA_below_udr`. -/
theorem jointlyProximateContribution_le_card_div_udr [NoZeroSMulDivisors F A]
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist ((C : Set (ι → A))) : ℝ≥0)) :
    jointlyProximateContribution (F := F) (C : Set (ι → A)) δ ≤
      ((Nat.floor (δ * (Fintype.card ι : ℝ≥0)) : ℝ≥0) / (Fintype.card F : ℝ≥0) : ENNReal) := by
  classical
  unfold jointlyProximateContribution
  apply iSup_le
  intro u
  by_cases hjp : jointProximity (C := (C : Set (ι → A))) (u := u) δ
  · rw [if_pos hjp]
    exact jointlyProximate_mcaEvent_Pr_le_card_div_udr C δ u h_udr hjp
  · rw [if_neg hjp]
    exact zero_le _

open Classical in
/-- **Decomposition of `ε_mca` (audited intermediate toward ABF26 Lemma 4.6).**

`ε_mca(C, δ) ≤ ε_ca(C, δ, δ) + jointlyProximateContribution C δ`.

This shrinks the remaining gap of Lemma 4.6 to *exactly* the contribution of the
jointly-`δ`-close stacks, with that contribution given an explicit name. The proof splits the
`ε_mca` supremum body `Pr_γ[mcaEvent]` pointwise into its `jointProximity` and
`¬jointProximity` parts (one of the two is `0`), then applies `iSup_add_le` and bounds the
non-jointly-close part by `ε_ca` via the already-proven `epsMCA_restricted_le_epsCA`.

What remains for the full equality `ε_mca = ε_ca` (in the UDR) is `jointlyProximateContribution
C δ ≤ ε_ca`. The kernel-checked obstruction shows this is *not* a pointwise body bound (on a
jointly-close `u` the `ε_ca` body is `0` while `Pr_γ[mcaEvent]` may be positive); the genuine
content needed is the list-decoding count of the exceptional `γ` of the fixed difference stack
of `jointProximity_diffStack_line_close`, the GS/PS machinery absent from the tree. -/
theorem epsMCA_le_epsCA_add_jointlyProximateContribution (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) C δ ≤
      epsCA (F := F) C δ δ + jointlyProximateContribution (F := F) C δ := by
  classical
  -- Abbreviations for the two gated suprema.
  set notjpSup : ENNReal :=
    (⨆ u : WordStack A (Fin 2) ι,
      if jointProximity (C := C) (u := u) δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]) with h_notjpSup
  have h_notjp_le : notjpSup ≤ epsCA (F := F) C δ δ := epsMCA_restricted_le_epsCA C δ
  unfold epsMCA jointlyProximateContribution
  -- Bound the `ε_mca` supremum body-by-body; each body splits as one of the two gated suprema.
  apply iSup_le
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ
  · -- jointly-close: body `≤ contribution ≤ ε_ca + contribution`.
    refine le_trans ?_ (le_add_left (le_refl _))
    refine le_trans ?_ (le_iSup (fun u : WordStack A (Fin 2) ι ↦
      if jointProximity (C := C) (u := u) δ then
        Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]
      else (0 : ENNReal)) u)
    rw [if_pos hjp]
  · -- non-jointly-close: body `≤ notjpSup ≤ ε_ca ≤ ε_ca + contribution`.
    refine le_trans ?_ (le_add_right h_notjp_le)
    rw [h_notjpSup]
    refine le_trans ?_ (le_iSup (fun u : WordStack A (Fin 2) ι ↦
      if jointProximity (C := C) (u := u) δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]) u)
    rw [if_neg hjp]

open Classical in
/-- **Tight (max-form) decomposition of `ε_mca` (audited intermediate toward ABF26 Lemma 4.6).**

`ε_mca(C, δ) ≤ max (ε_ca(C, δ, δ)) (jointlyProximateContribution C δ)`.

Sharper than the additive `epsMCA_le_epsCA_add_jointlyProximateContribution`: because each
`ε_mca` supremum body is *either* the non-jointly-close gated body (`≤ ε_ca`) *or* the
jointly-close gated body (`≤ jointlyProximateContribution`) — never both at once — the two
contributions combine by `max`, not by `+`. The proof bounds each body by the `max` of the two
gated suprema and uses `iSup_le`.

This is the decomposition that makes ABF26 Lemma 4.6 collapse: the *only* remaining fact is
`jointlyProximateContribution C δ ≤ ε_ca(C, δ, δ)` (in the UDR), after which
`max (ε_ca) (jointlyProximateContribution) = ε_ca` and `ε_mca ≤ ε_ca` follows. That single
remaining inequality is the ACFY25/[Hab25] list-decoding bound on the exceptional `γ` of the
fixed difference stack (`jointProximity_diffStack_line_close`); it is the content not yet
available in-tree. -/
theorem epsMCA_le_max_epsCA_jointlyProximateContribution (C : Set (ι → A)) (δ : ℝ≥0) :
    epsMCA (F := F) C δ ≤
      max (epsCA (F := F) C δ δ) (jointlyProximateContribution (F := F) C δ) := by
  classical
  set notjpSup : ENNReal :=
    (⨆ u : WordStack A (Fin 2) ι,
      if jointProximity (C := C) (u := u) δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]) with h_notjpSup
  have h_notjp_le : notjpSup ≤ epsCA (F := F) C δ δ := epsMCA_restricted_le_epsCA C δ
  unfold epsMCA
  apply iSup_le
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ
  · -- jointly-close body `≤ jointlyProximateContribution ≤ max …`.
    refine le_trans ?_ (le_max_right _ _)
    have h_body_le :
        Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ] ≤
          jointlyProximateContribution (F := F) C δ := by
      unfold jointlyProximateContribution
      refine le_trans ?_ (le_iSup (fun u : WordStack A (Fin 2) ι ↦
        if jointProximity (C := C) (u := u) δ then
          Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]
        else (0 : ENNReal)) u)
      rw [if_pos hjp]
    exact h_body_le
  · -- non-jointly-close body `≤ notjpSup ≤ ε_ca ≤ max …`.
    refine le_trans ?_ (le_max_left _ _)
    refine le_trans ?_ h_notjp_le
    rw [h_notjpSup]
    refine le_trans ?_ (le_iSup (fun u : WordStack A (Fin 2) ι ↦
      if jointProximity (C := C) (u := u) δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]) u)
    rw [if_neg hjp]

/-- **ABF26 Lemma 4.6.** In the unique-decoding regime `δ < δ_min(C)/2`, `ε_mca` and `ε_ca`
coincide: `ε_mca(C, δ) = ε_ca(C, δ)`.

The unique-decoding hypothesis is expressed as `2 · δ · n < δ_min(C) · n = ‖C‖₀` to avoid
fractional arithmetic in ℕ — equivalent to the paper's `δ < δ_min(C)/2`.

The proof is reduced here to **one** inequality. The direction `ε_ca ≤ ε_mca` is the in-tree
`epsCA_le_epsMCA` (no UDR needed). What remains, `ε_mca ≤ ε_ca`, is the genuinely hard
direction:

**Status of the remaining direction: shrunk to ONE explicit inequality.** Via the audited
max-form decomposition `epsMCA_le_max_epsCA_jointlyProximateContribution`,
`ε_mca ≤ max (ε_ca) (jointlyProximateContribution C δ)`. So the whole hard direction now
follows from the *single* residual

  `jointlyProximateContribution C δ ≤ ε_ca(C, δ, δ)`     (the `sorry` below),

after which `max (ε_ca) (jointlyProximateContribution) = ε_ca`. This is strictly less than the
former opaque `ε_mca ≤ ε_ca` admit: the residual is now explicitly the worst-case `mcaEvent`
mass over the *jointly-`δ`-close* stacks only (the `¬jointProximity` part is already discharged
by `epsMCA_restricted_le_epsCA`).

Why even this residual is **not** a pointwise `iSup`-monotonicity ([ACFY25, Lemma 4.10];
footnote 6 in ABF26 notes the proof is for linear codes but generalises to F-additive codes):
for a fixed jointly-close stack `u` the `epsCA` body collapses to `0` while `Pr_γ[mcaEvent]`
can still be **positive** — under UDR the line agrees with the unique close codeword
`p₀ + γ·p₁` on the witness set for the exact `γ` solving the per-position linear equations of
the *fixed difference stack* `(u 0 - p₀, u 1 - p₁)` (see `jointProximity_diffStack_line_close`),
a non-empty `γ`-set. So the bound only holds after the global dominance/rearrangement of ACFY25
(equivalently: the Guruswami–Sudan/[Hab25] list-decoding count of those exceptional `γ`),
machinery not yet in-tree. Tracked in `docs/kb/ABF26_PLAN.md` §6 conjecture ledger. The provable
structural half `mcaEvent → δᵣ(line, C) ≤ δ` is recorded above as `mcaEvent_imp_relCloseToCode`.

**Sharpened residual (kernel-checked).** The residual is now bounded explicitly: for symbol space
`Σ = Fˢ` (i.e. `NoZeroSMulDivisors F A`, the paper's actual setting),
`jointlyProximateContribution_le_card_div_udr` proves
`jointlyProximateContribution C δ ≤ ⌊δ·n⌋/|F|` (the [AHIV17]/[Hab25] Lemma 1 unique-decoding
coordinate count: each disagreement coordinate `i ∉ S'` kills *at most one* exceptional `γ`, the
unique solution of `γ • (u 1 - p₁) i = -(u 0 - p₀) i`, and there are `≤ ⌊δ·n⌋` such coordinates).
Hence `ε_mca ≤ max (ε_ca) (⌊δ·n⌋/|F|)`. The **only** remaining gap is the global dominance
`⌊δ·n⌋/|F| ≤ ε_ca(C, δ, δ)` — that some *non*-jointly-close stack attains line-closeness
probability matching the per-coordinate bad-`γ` count. This is exactly [ACFY25, Lemma 4.10]'s
rearrangement; it does **not** follow from the count bound (`ε_ca` can be strictly below
`⌊δ·n⌋/|F|`), and is the precise external residual kept as the `sorry`. -/
theorem epsMCA_eq_epsCA_below_udr
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (_h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) <
              (Code.dist ((C : Set (ι → A))) : ℝ≥0)) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ =
    epsCA (F := F) (A := A) ((C : Set (ι → A))) δ δ := by
  refine le_antisymm ?_ (epsCA_le_epsMCA C δ)
  -- Reduce the hard direction to the single residual `jointlyProximateContribution ≤ ε_ca`
  -- via the audited max-form decomposition.
  refine le_trans (epsMCA_le_max_epsCA_jointlyProximateContribution
    (F := F) (C := (C : Set (ι → A))) δ) ?_
  rw [max_le_iff]
  refine ⟨le_refl _, ?_⟩
  -- Remaining: `jointlyProximateContribution C δ ≤ ε_ca`. The in-tree
  -- `jointlyProximateContribution_le_card_div_udr` already bounds the LHS by `⌊δ·n⌋/|F|`
  -- (the [AHIV17]/[Hab25] Lemma 1 unique-decoding coordinate count); the *only* missing fact
  -- is the global dominance `⌊δ·n⌋/|F| ≤ ε_ca`, i.e. ACFY25 Lemma 4.10's rearrangement onto a
  -- non-jointly-close stack. It does NOT follow from the count bound (ε_ca can be smaller). See
  -- docstring.
  sorry -- ABF26 L4.6 residual: jointlyProximateContribution ≤ ε_ca (ACFY25 Lemma 4.10 dominance)

/-- Row-extraction: the `k`-th row of a `Fin t → A`-valued word, as an `A`-valued word. -/
private def row_of {ι : Type} {A : Type} {t : ℕ}
    (w : ι → (Fin t → A)) (k : Fin t) : ι → A :=
  fun j ↦ w j k

/-- **ABF26 Lemma 4.7.** For any F-additive code `C` (here: a `Submodule F (ι → A)`) and
`t : ℕ`: `ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)`.

Proof recipe:
1. `mcaEvent` for the interleaved code at `γ` implies `∃ k`, `mcaEvent` for the `k`-th row
   restriction (witness set `S` is shared; if every row admitted a joint codeword pair
   on `S`, assembling them column-by-column would produce a joint codeword pair in
   `C^⋈ (Fin t)` agreeing on `S`, contradicting the interleaved's "no joint pair" clause).
2. `Pr_le_Pr_of_implies` lifts the per-`γ` implication to a probability bound.
3. `Pr_exists_Fin_le_sum` (union bound) splits into a sum over rows.
4. Each row's probability is bounded by `epsMCA C δ` via `le_iSup`.
5. Sum-of-constants reduces to `t · epsMCA C δ`. -/
theorem epsMCA_interleaved_le (C : Submodule F (ι → A)) (t : ℕ) (δ : ℝ≥0) :
    epsMCA (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) δ ≤
    (t : ENNReal) * epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  classical
  unfold epsMCA
  apply iSup_le
  intro u
  -- Step 1: row-decomposition implication.
  have h_imp : ∀ γ : F, mcaEvent ((C : Set (ι → A))^⋈ (Fin t)) δ (u 0) (u 1) γ →
               ∃ k : Fin t,
                 mcaEvent (C : Set (ι → A)) δ (row_of (u 0) k) (row_of (u 1) k) γ := by
    intro γ h_int
    obtain ⟨S, hS_card, ⟨w, hw_mem, hw_eq⟩, h_no_pair_int⟩ := h_int
    by_contra h_all
    push Not at h_all
    -- For each k, ¬ mcaEvent C row k. Specialize at the inherited witness `S`,
    -- noting that the size and line-agreement clauses hold for every row, so the
    -- only way mcaEvent fails for row k is via a joint codeword pair on `S`.
    have h_row_pair :
        ∀ k : Fin t, ∃ v₀ ∈ (C : Set (ι → A)), ∃ v₁ ∈ (C : Set (ι → A)),
                     ∀ j ∈ S, v₀ j = row_of (u 0) k j ∧ v₁ j = row_of (u 1) k j := by
      intro k
      have h_k := h_all k
      -- h_k : ¬ ∃ S', size ∧ line-agree-on-S' ∧ ¬ pair-on-S'.
      -- Specialize at S: ¬ (size_S ∧ line_S ∧ ¬ pair_S). With size_S and line_S
      -- holding (inherited from interleaved), `¬ pair_S` must fail, i.e., pair_S holds.
      have h_neg :
          ¬ ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
             (∃ w' ∈ (C : Set (ι → A)),
                ∀ j ∈ S, w' j = row_of (u 0) k j + γ • row_of (u 1) k j) ∧
             ¬ pairJointAgreesOn (C : Set (ι → A)) S (row_of (u 0) k) (row_of (u 1) k)) :=
        fun h ↦ h_k ⟨S, h.1, h.2.1, h.2.2⟩
      -- size_S inherited from `hS_card`.
      -- line_S: the row-k version of w is in C and agrees on S.
      have h_size : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := hS_card
      have h_line : ∃ w' ∈ (C : Set (ι → A)),
                    ∀ j ∈ S, w' j = row_of (u 0) k j + γ • row_of (u 1) k j := by
        refine ⟨row_of w k, hw_mem k, ?_⟩
        intro j hj
        have := hw_eq j hj
        -- this : w j = u 0 j + γ • u 1 j (as (Fin t → A)). Apply at k.
        have h_pt : w j k = (u 0 j + γ • u 1 j) k := congrArg (· k) this
        -- `(u 0 j + γ • u 1 j) k = u 0 j k + γ • u 1 j k`, which unfolds to
        -- `row_of (u 0) k j + γ • row_of (u 1) k j`.
        simp only [row_of, Pi.add_apply, Pi.smul_apply] at h_pt ⊢
        exact h_pt
      -- So `¬ ¬ pair_S` must hold, i.e., `pair_S` holds (Classical: decidable).
      have h_pair_or :
          pairJointAgreesOn (C : Set (ι → A)) S (row_of (u 0) k) (row_of (u 1) k) := by
        by_contra h_no_pair
        exact h_neg ⟨h_size, h_line, h_no_pair⟩
      obtain ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_agree⟩ := h_pair_or
      exact ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_agree⟩
    -- Assemble row-witnesses into a joint codeword pair in `C^⋈ (Fin t)`, contradicting
    -- the interleaved's "no joint pair" clause.
    apply h_no_pair_int
    choose V₀_fn hV₀_mem V₁_fn hV₁_mem h_V_agree using h_row_pair
    -- V₀_fn : Fin t → ι → A,  V₀_fn k j = row k's first witness at j
    refine ⟨fun j k ↦ V₀_fn k j, ?_, fun j k ↦ V₁_fn k j, ?_, ?_⟩
    · intro k; exact hV₀_mem k
    · intro k; exact hV₁_mem k
    · intro j hj
      refine ⟨?_, ?_⟩
      · funext k; exact (h_V_agree k j hj).1
      · funext k; exact (h_V_agree k j hj).2
  -- Step 2 + 3: chain through Pr_le_Pr_of_implies and the union bound.
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  refine le_trans (Pr_exists_Fin_le_sum _ _) ?_
  -- Step 4: each summand ≤ epsMCA C δ.
  refine le_trans (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin t)))
    (fun k _ ↦ le_iSup
      (fun v : WordStack A (Fin 2) ι ↦
        Pr_{let γ ← $ᵖ F}[mcaEvent (C : Set (ι → A)) δ (v 0) (v 1) γ])
      (fun i j ↦ row_of (u i) k j))) ?_
  -- Step 5: sum-of-constants reduces to t * (epsMCA C δ).
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact le_of_eq (nsmul_eq_mul _ _)

/-- **Bridge for affine spaces.** The predicate `δ_ε_correlatedAgreementAffineSpaces C δ ε`
(from `Basic.lean`, threshold `ε`) is equivalent to `epsCA_affineSpaces C k δ δ ≤ ε`. Same
proof recipe as the `AffineLines` and `Curves` bridges. -/
theorem δ_ε_correlatedAgreementAffineSpaces_iff_epsCA_affineSpaces_le {k : ℕ}
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineSpaces (F := F) (k := k) C δ ε ↔
    epsCA_affineSpaces (F := F) C k δ δ ≤ (ε : ENNReal) := by
  classical
  constructor
  · intro h_pred
    refine iSup_le fun u ↦ ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]; exact zero_le _
    · rw [if_neg hjp]
      have h_not_ja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]; exact hjp
      by_contra h_gt
      push Not at h_gt
      exact h_not_ja (h_pred u h_gt)
  · intro h_eps u h_pr
    unfold epsCA_affineSpaces at h_eps
    have h_term_le := iSup_le_iff.mp h_eps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]; exact hjp
    · rw [if_neg hjp] at h_term_le
      exact absurd h_pr (not_lt.mpr h_term_le)

end

end ProximityGap
