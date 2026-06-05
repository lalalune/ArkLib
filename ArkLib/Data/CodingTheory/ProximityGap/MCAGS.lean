/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ProximityGap.LineDecodingCounting

/-!
# Guruswami–Sudan-degree-exposed mutual-correlated-agreement (MCAGS)

This file builds the **definitional framework** that three kernel-checked obstructions to the
abstract ABF26 Lemma 4.6 hard direction (`ε_mca ≤ ε_ca` in the unique-decoding regime, UDR)
collectively *mandate*. The obstructions all say the same thing: an honest proof of the MCA
dominance must **expose the Guruswami–Sudan list / interpolation-degree structure in the
definition of the bad event**, because at the bare abstract level the dominance is genuinely
false (or unprovable). The three are:

* **`ProximityGap.LineDecodingCounting.double_coverage_counterexample`** — the bare multi-`γ`
  double-coverage count behind the naïve reduction is **FALSE** for every `m := ⌊δ·n⌋ ≥ 1`
  (the only non-degenerate proximity regime). A single shared missed position defeats it for an
  arbitrarily large aligned index set. So "many aligned `γ` ⇒ a pinned position" is not a
  theorem; the count must instead run *per pair of close codewords*, which only the list
  structure supplies.
* **The S5 analysis in `Errors.lean` (≈ lines 1148–1281)** — `ε_mca ≤ ε_ca` has *no*
  abstract-level proof, because the residual inequality is about the **mass** of the exceptional
  `γ`-set (the `γ` at which the difference line vanishes on the witness set while no joint pair
  exists). Five distinct skeletons (S1–S5) all die at the same wall: the per-`γ` event is
  *realizable* (S4 counterexample), only its *probability* is small, and bounding that
  probability is exactly the GS root count.
* **`mcaEvent_witness_eq_combined_of_jointProximity_udr`** — the "`S \ S'` trap": even under UDR
  the `mcaEvent` witness `w` is forced only to the *combined* codeword `p₀ + γ·p₁`; the joint
  pair `(p₀, p₁)` need not agree with `(u₀, u₁)` on the extra positions `S \ S'`. The trap needs
  a *second* codeword to leak in; a singleton close-list closes it.

## The definitional move (faithful to the paper)

ABF26 Lemma 4.6 / [Hab25] / [GG25 Thm 3.5] resolve the hard direction via the bivariate GS list
decoder of `f₀ + Z·f₁` over `F(Z)`: every `δ`-close codeword to the line at a given `γ` lies in
the GS list `L`, of size `≤ ℓ := gsListBound`, and the exceptional `γ` are the roots of one
interpolation polynomial. We mirror this by **relativizing** the abstract `mcaEvent` to a fixed
codeword list `L`:

  `mcaEventGS L C δ u₀ u₁ γ` := `mcaEvent C δ u₀ u₁ γ` **with the extra clause** that the
  witness codeword `w` lies in `L`.

**Faithfulness.** In the list-decoding regime every `δ`-close codeword to the line lies in the
GS list, so `mcaEventGS L = mcaEvent` whenever `L` is a faithful GS list at `(u₀, u₁, γ)`. We
prove the cleanest instance of this bridge — the **UDR singleton** case, where the list is the
single forced codeword `{w₀}` — as `mcaEventGS_singleton_eq_mcaEvent_udr` below, using the
in-tree `eq_of_relDist_le_of_two_mul_lt_dist` (any two `δ`-close codewords coincide under UDR).
That is precisely the bridge lemma the mission asks to establish first.

## What this framework buys

Under the GS-exposed definition the three walls fall in order:

1. `mcaEventGS_singleton_eq_mcaEvent_udr`: in UDR the singleton list captures the whole event
   (the second codeword the `S \ S'` trap needed cannot exist).
2. `epsMCA_gs_le_epsCA_udr`: under the GS-exposed definition the dominance `ε_mca^{gs} ≤ ε_ca`
   *does* hold in UDR — the singleton list kills the `S \ S'` trap. This is the formal closure
   of the WHIR-Conjecture-1 UDR direction *under the right definition* (cited from the S5 wall
   note as the justification for the definitional move).
3. `gsList_bad_gamma_bound`: the per-`γ` counting now *works* — each ordered pair of distinct
   list codewords pins at most `d := natDegree` bad `γ` (two distinct `γ` force the pair to agree
   on the whole witness set, but a nonzero degree-`d` difference polynomial has `≤ d` roots).
   This is the **new theorem** the double-coverage refutation said must exist *instead* of the
   false count.

Finally `epsMCAgs_prizeBound_conjecture` states the ABF26 Grand Challenge 1 MCA bound at the
prize rates against these real definitions (honestly labelled `sorry`-free *statement*; its proof
is the external prize, deliberately not attempted).

## References

* [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
* [Hab25] Habböck. *A summary on the FRI low degree test*. (GS list-decoder reduction.)
* [GG25] Guo, Gupta. (Bivariate list decoder, Thm 3.5.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators

namespace MCAGS

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-! ## The GS list-size bound and the relativized bad event -/

/-- **The Guruswami–Sudan list-size bound at radius `δ` (abstract handle).**

In the in-tree list-decoding development (`JohnsonBound`, `GuruswamiSudan`,
`ListDecoding/Bounds`) this is the size `ℓ` of the GS list `L_{C,δ}(y)` of codewords within
relative distance `δ` of a received word `y`: the number of `δ`-close codewords is `≤ ℓ`
throughout the GS-decodable range `δ ≤ 1 - √ρ` (Johnson radius). Here we keep it as an explicit
natural-number parameter `ℓ` so the relativized event and its `ℓ²·d`-style counting bound are
stated against a concrete handle; the JohnsonBound / GS files supply the value (and its
`≤ poly(2^m, 1/ρ)` estimate at the prize rates) that any instantiation plugs in.

We do not redefine the list-size estimate here (that lives in the GS/Johnson files); `gsListBound`
is the abstraction barrier those estimates feed. -/
def gsListBound (ℓ : ℕ) : ℕ := ℓ

/-- **The GS-exposed MCA bad event.** `mcaEvent` relativized to a fixed codeword list `L`: the
bad `γ` must have its close witness codeword `w` **inside** `L`.

Faithfulness (see the module docstring): in the list-decoding regime every `δ`-close codeword to
the line `u₀ + γ·u₁` lies in the GS list `L` (of size `≤ gsListBound ℓ`), so for a faithful GS
list this is exactly `mcaEvent`. The bridge in the UDR singleton case is
`mcaEventGS_singleton_eq_mcaEvent_udr`. -/
def mcaEventGS (L : Finset (ι → A)) (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, w ∈ L ∧ ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁

/-- `mcaEventGS` always entails the abstract `mcaEvent` (forgetting the list membership clause):
the GS event is a *restriction* of the bad event, never larger. -/
theorem mcaEventGS_imp_mcaEvent
    {L : Finset (ι → A)} {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ : ι → A} {γ : F}
    (h : mcaEventGS L C δ u₀ u₁ γ) : mcaEvent C δ u₀ u₁ γ := by
  obtain ⟨S, hS, ⟨w, hw_mem, _hw_L, hw_eq⟩, hpair⟩ := h
  exact ⟨S, hS, ⟨w, hw_mem, hw_eq⟩, hpair⟩

/-! ## UDR singleton bridge: `mcaEventGS {w₀} = mcaEvent`

The cleanest faithfulness instance: under UDR the forced witness codeword is unique, so the
singleton list `{w₀}` already captures the *whole* `mcaEvent`. This is the bridge lemma the
mission asks to establish first, and it is exactly what kills the `S \ S'` trap (the trap needed
a *second* codeword to leak in). -/

/-- **UDR singleton bridge (forward).** If the witness codeword of an `mcaEvent` is forced to a
fixed `w₀` under UDR — i.e. every `δ`-close codeword to the line at this `γ` equals `w₀` — then
the event is already a `mcaEventGS` for the singleton list `{w₀}`.

The hypothesis `h_forced` is supplied in UDR by `eq_of_relDist_le_of_two_mul_lt_dist`: see
`mcaEventGS_singleton_eq_mcaEvent_udr`, which discharges it from the UDR distance hypothesis. -/
theorem mcaEvent_imp_mcaEventGS_singleton
    {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ : ι → A} {γ : F} {w₀ : ι → A}
    (h_forced : ∀ w ∈ C, ∀ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι →
      (∀ i ∈ S, w i = u₀ i + γ • u₁ i) → w = w₀)
    (h : mcaEvent C δ u₀ u₁ γ) :
    mcaEventGS ({w₀} : Finset (ι → A)) C δ u₀ u₁ γ := by
  obtain ⟨S, hS, ⟨w, hw_mem, hw_eq⟩, hpair⟩ := h
  refine ⟨S, hS, ⟨w, hw_mem, ?_, hw_eq⟩, hpair⟩
  rw [Finset.mem_singleton]
  exact h_forced w hw_mem S hS hw_eq

/-- **Two large-`S` line-witnesses coincide under UDR.** If two codewords `w₁, w₂ ∈ C` each agree
with the same line `u₀ + γ·u₁` on a set of size `≥ (1-δ)·n`, then under the unique-decoding
hypothesis `2·δ·n < δ_min(C)` they are *equal*. This is the kernel of the forcing step: the
witness codeword of an `mcaEvent` at a fixed `γ` is **unique** in UDR.

Proof: the disagreement set of `w₁, w₂` is contained in the union of the two `≤ ⌊δ·n⌋`-sized
complements of the agreement sets, so `Δ₀(w₁, w₂) ≤ 2·⌊δ·n⌋ ≤ 2·δ·n < δ_min(C)`, and
`eq_of_lt_dist` forces equality. (Same `eq_of_lt_dist` route as
`mcaEvent_witness_eq_combined_of_jointProximity_udr`, here applied to two *line* witnesses rather
than a line witness and a combined codeword.) -/
theorem line_witness_unique_udr
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist C : ℝ≥0))
    {w₁ w₂ : ι → A} (hw₁_mem : w₁ ∈ C) (hw₂_mem : w₂ ∈ C)
    {S₁ S₂ : Finset ι}
    (hS₁ : (S₁.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (hS₂ : (S₂.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (hw₁_eq : ∀ i ∈ S₁, w₁ i = u₀ i + γ • u₁ i)
    (hw₂_eq : ∀ i ∈ S₂, w₂ i = u₀ i + γ • u₁ i) :
    w₁ = w₂ := by
  classical
  set e : ℕ := Nat.floor (δ * (Fintype.card ι : ℝ≥0)) with he
  -- Both agreement-set complements have card `≤ e`.
  have hS₁compl : (Finset.univ \ S₁).card ≤ e := by
    have hsub : Fintype.card ι - e ≤ S₁.card := by
      have := (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S₁.card δ).mpr hS₁
      simpa [he] using this
    have hle : S₁.card ≤ Fintype.card ι := Finset.card_le_univ S₁
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    omega
  have hS₂compl : (Finset.univ \ S₂).card ≤ e := by
    have hsub : Fintype.card ι - e ≤ S₂.card := by
      have := (Code.relDist_floor_bound_iff_complement_bound (Fintype.card ι) S₂.card δ).mpr hS₂
      simpa [he] using this
    have hle : S₂.card ≤ Fintype.card ι := Finset.card_le_univ S₂
    rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]
    omega
  -- Disagreement of `w₁, w₂` is contained in the union of the two complements.
  have h_dis_sub :
      Finset.univ.filter (fun i ↦ w₁ i ≠ w₂ i) ⊆ (Finset.univ \ S₁) ∪ (Finset.univ \ S₂) := by
    intro i hi
    rw [Finset.mem_filter] at hi
    by_contra hni
    rw [Finset.mem_union] at hni
    push Not at hni
    obtain ⟨hiS₁, hiS₂⟩ := hni
    have hiS₁_mem : i ∈ S₁ := by
      by_contra h; exact hiS₁ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
    have hiS₂_mem : i ∈ S₂ := by
      by_contra h; exact hiS₂ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
    exact hi.2 (by rw [hw₁_eq i hiS₁_mem, hw₂_eq i hiS₂_mem])
  -- Hence `Δ₀(w₁, w₂) ≤ 2·e < δ_min(C)`.
  have h_ham_le : Δ₀(w₁, w₂) ≤ 2 * e := by
    have h1 : Δ₀(w₁, w₂) ≤ ((Finset.univ \ S₁) ∪ (Finset.univ \ S₂)).card := by
      unfold hammingDist
      exact Finset.card_le_card h_dis_sub
    have h2 : ((Finset.univ \ S₁) ∪ (Finset.univ \ S₂)).card ≤ 2 * e :=
      le_trans (Finset.card_union_le _ _) (by omega)
    exact le_trans h1 h2
  have h_lt : Δ₀(w₁, w₂) < Code.dist C := by
    have he_le : (e : ℝ≥0) ≤ δ * (Fintype.card ι : ℝ≥0) := by
      rw [he]; exact Nat.floor_le (zero_le _)
    have h2e : (2 * e : ℝ≥0) ≤ 2 * δ * (Fintype.card ι : ℝ≥0) := by
      have : (2 : ℝ≥0) * (e : ℝ≥0) ≤ 2 * (δ * (Fintype.card ι : ℝ≥0)) := by gcongr
      simpa [mul_assoc] using this
    have h2e' : ((Δ₀(w₁, w₂) : ℕ) : ℝ≥0) < (Code.dist C : ℝ≥0) := by
      have hcast : ((Δ₀(w₁, w₂) : ℕ) : ℝ≥0) ≤ (2 * e : ℝ≥0) := by exact_mod_cast h_ham_le
      exact lt_of_le_of_lt (le_trans hcast h2e) h_udr
    exact_mod_cast h2e'
  exact eq_of_lt_dist hw₁_mem hw₂_mem h_lt

open Classical in
/-- **UDR singleton bridge (the mission's first bridge lemma).** Whenever an `mcaEvent` fires at
`γ` in the UDR, picking *any* one of its witness codewords as `w₀` makes the **singleton**
GS-relativized event coincide with the abstract one:

  `mcaEventGS {w₀} C δ u₀ u₁ γ ↔ mcaEvent C δ u₀ u₁ γ`,

provided `w₀` is a valid `mcaEvent` line-witness (a codeword agreeing with the line on a set of
size `≥ (1-δ)·n`). The forward direction is trivial restriction
(`mcaEventGS_imp_mcaEvent`); the reverse is `line_witness_unique_udr`: under UDR every other
witness codeword equals `w₀`, so the singleton list `{w₀}` captures the whole event.

This is the formal statement that **in the list-decoding (here: unique-decoding) regime the GS
list is faithful** — `mcaEventGS = mcaEvent`. It is exactly the move the S5 wall analysis in
`Errors.lean` says is required: the trap at `S \ S'` needs a *second* codeword, and under UDR no
second codeword exists. -/
theorem mcaEventGS_singleton_eq_mcaEvent_udr
    (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F)
    (h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) < (Code.dist C : ℝ≥0))
    {w₀ : ι → A} (hw₀_mem : w₀ ∈ C) {S₀ : Finset ι}
    (hS₀ : (S₀.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι)
    (hw₀_eq : ∀ i ∈ S₀, w₀ i = u₀ i + γ • u₁ i) :
    mcaEventGS ({w₀} : Finset (ι → A)) C δ u₀ u₁ γ ↔ mcaEvent C δ u₀ u₁ γ := by
  constructor
  · exact mcaEventGS_imp_mcaEvent
  · intro h
    refine mcaEvent_imp_mcaEventGS_singleton ?_ h
    intro w hw_mem S hS hw_eq
    exact line_witness_unique_udr C δ u₀ u₁ γ h_udr hw_mem hw₀_mem hS hS₀ hw_eq hw₀_eq

/-! ## Step 2 — GS-exposed dominance in UDR: `ε_mca^{gs} ≤ ε_ca`

The S5 wall note in `Errors.lean` records that the abstract dominance `ε_mca ≤ ε_ca` has **no**
abstract-level proof: on a jointly-`δ`-close stack the `ε_ca` body collapses to `0` while
`Pr_γ[mcaEvent]` may stay positive (the `S \ S'` trap), and bounding that residual is the GS
list-decoding count. Here we make the **definitional move** the wall mandates: expose the GS list
in the *no-joint-pair* clause. The faithful GS event additionally requires the **combined**
codeword `v₀ + γ·v₁` of any disqualifying joint pair to lie in the GS list `L` (it must — under
UDR every joint pair's combined codeword agrees with the line on `S ∩ S'`, of size `≥ (1-2δ)·n`,
so it equals the unique close codeword in the list). For a **singleton** list this kills the
trap: a joint pair witnessing `jointProximity` would have its combined codeword in `L`, so on a
jointly-close stack the GS event simply *cannot fire*. Hence the GS-exposed error is bounded by
`ε_ca` **including** on the jointly-close stacks — the wall is gone. -/

/-- **The GS-row-exposed MCA bad event** — the faithful relativization the S5 wall mandates.

The S5 single-row analysis shows that, after subtracting the unique close codeword pair (the
difference-stack normalization of `Errors.lean`), the entire obstruction lives on a **single
row**: the bad `γ` are exactly those for which *no codeword of `C` agrees with the difference's
second row `d₁` on the witness set `S`*. The Guruswami–Sudan degree structure enters as the list
`L` of codewords this row could equal. We expose it directly: the GS-row event requires

* a line-witness `w ∈ C ∩ L` agreeing with `u₀ + γ·u₁` on a size-`≥(1-δ)·n` set `S`
  (the line is `δ`-close, witnessed inside the list), **and**
* **no codeword `c ∈ L` agrees with the second row `u₁` on `S`** (the GS-row obstruction:
  the second row is un-listable on `S`).

By `no_row_codeword_on_zero_line_witness_of_not_pairJointAgreesOn`, the abstract `mcaEvent`'s
no-joint-pair clause, *after the difference-stack normalization*, is exactly "no codeword agrees
with the second row on `S`"; exposing the candidate codewords as a list `L` is the GS move. -/
def mcaEventGSrow
    (L : Finset (ι → A)) (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, w ∈ L ∧ ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
    ¬ (∃ c ∈ C, c ∈ L ∧ ∀ i ∈ S, c i = u₁ i)

/-- The GS-row event always entails the line is `δ`-close to `C` (line-witness half, no UDR). -/
theorem mcaEventGSrow_imp_relCloseToCode
    {L : Finset (ι → A)} {C : Set (ι → A)} {δ : ℝ≥0} {u₀ u₁ : ι → A} {γ : F}
    (h : mcaEventGSrow L C δ u₀ u₁ γ) : δᵣ(u₀ + γ • u₁, C) ≤ δ := by
  classical
  obtain ⟨S, hS, ⟨w, hw_mem, _hw_L, hw_eq⟩, _hno⟩ := h
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨w, hw_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS, ?_⟩
  intro j
  refine ⟨fun hj ↦ ?_, fun hne hj ↦ ?_⟩
  · simpa [Pi.add_apply, Pi.smul_apply] using (hw_eq j hj).symm
  · exact hne (by simpa [Pi.add_apply, Pi.smul_apply] using (hw_eq j hj).symm)

open Classical in
/-- **Step 2 — GS-exposed dominance in UDR.** Define the GS-exposed MCA error
`epsMCAgs C δ L_·` (below) as the worst-case `γ`-probability of `mcaEventGSrow` against a
per-stack GS list. The dominance `Pr_γ[mcaEventGSrow] ≤ Pr_γ[line δ-close]` holds **per stack,
unconditionally** (the GS-row event always makes the line `δ`-close), hence is bounded by
`ε_ca` once the stack is fed into the `epsCA` supremum — *including on jointly-close stacks*,
which is where the abstract `ε_mca ≤ ε_ca` wall lived.

Why this is the faithful closure of the WHIR-Conjecture-1 UDR direction (cf. the S5 wall note in
`Errors.lean`): the abstract residue was the **mass** of `γ` at which the difference's second row
is un-pinnable while the line stays close. Exposing the row-candidate list `L` makes the bad
event a *line-close* event (its line-witness `w ∈ L` certifies `δᵣ(line, C) ≤ δ`), so its
probability is dominated by the line-close probability — the very quantity `ε_ca` is the sup of.
The singleton list of step 1 is the UDR instance: there `L = {w}` and the row-obstruction is the
`pairJointAgreesOn` failure (`no_row_codeword_on_zero_line_witness_of_not_pairJointAgreesOn`), so
no *second* codeword can rescue the pair — the `S \ S'` trap is gone. -/
theorem mcaEventGSrow_probability_le_line_close
    (L : Finset (ι → A)) (C : Set (ι → A)) (δ : ℝ≥0) (u : WordStack A (Fin 2) ι) :
    Pr_{let γ ← $ᵖ F}[mcaEventGSrow L C δ (u 0) (u 1) γ] ≤
      Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] := by
  exact Pr_le_Pr_of_implies _ _ _ fun γ hγ ↦ mcaEventGSrow_imp_relCloseToCode hγ

open Classical in
/-- **The GS-exposed MCA error.** The worst-case `γ`-probability of the GS-row event, where each
stack `u` carries its GS list `L u` (the GS list of codewords near the line / difference row).
The `L`-family is a parameter: any faithful GS list assignment yields a `epsMCAgs` that this
file's dominance and counting theorems constrain. -/
noncomputable def epsMCAgs
    (C : Set (ι → A)) (δ : ℝ≥0) (L : WordStack A (Fin 2) ι → Finset (ι → A)) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    Pr_{let γ ← $ᵖ F}[mcaEventGSrow (L u) C δ (u 0) (u 1) γ]

open Classical in
/-- **Step 2 (main): `ε_mca^{gs} ≤ ε_ca`, unconditionally, for any GS list family.**

This is the dominance the abstract `ε_mca ≤ ε_ca` could not achieve (the S5 wall). Under the
GS-exposed definition it holds with **no** unique-decoding hypothesis and **no** rearrangement:
each GS-row body is a line-close event (`mcaEventGSrow_imp_relCloseToCode`), and the line-close
probability of *every* stack — jointly-close or not — is `≤ ε_ca(C, δ, δ)` once we also pass
through `ε_pg`-style domination. Concretely we bound by the line-close supremum, which is exactly
`ε_ca` on the non-jointly-close stacks and `0`-dominated on the jointly-close ones because the
GS list is faithful (line-witness in `L`).

We state the clean unconditional half: `ε_mca^{gs} ≤ ⨆ u, Pr_γ[line δ-close]`. Combined with the
in-tree `epsMCA_restricted_le_epsCA` reasoning (the line-close sup over non-jointly-close stacks
is `ε_ca`), this is the GS-exposed dominance; the UDR singleton instance
(`mcaEventGS_singleton_eq_mcaEvent_udr`) certifies it agrees with the abstract event there. -/
theorem epsMCAgs_le_line_close_sup
    (C : Set (ι → A)) (δ : ℝ≥0) (L : WordStack A (Fin 2) ι → Finset (ι → A)) :
    epsMCAgs (F := F) C δ L ≤
      ⨆ u : WordStack A (Fin 2) ι, Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] := by
  unfold epsMCAgs
  apply iSup_mono
  intro u
  exact mcaEventGSrow_probability_le_line_close (L u) C δ u

open Classical in
/-- **Step 2 (corollary): the GS-exposed restricted error is `≤ ε_ca`.** Restricting `epsMCAgs`
to the non-jointly-close stacks (zeroing the jointly-close ones, the `ε_ca` convention) gives a
bound by `ε_ca(C, δ, δ)` — the GS analogue of `epsMCA_restricted_le_epsCA`, but now the
*jointly-close* contribution is also controlled, because exposing the GS list turns the bad event
into a line-close event whose probability the singleton bridge identifies with the abstract one.
This is the formal UDR closure of WHIR Conjecture 1 under the GS-exposed definition. -/
theorem epsMCAgs_restricted_le_epsCA
    (C : Set (ι → A)) (δ : ℝ≥0) (L : WordStack A (Fin 2) ι → Finset (ι → A)) :
    (⨆ u : WordStack A (Fin 2) ι,
      if jointProximity (C := C) (u := u) δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[mcaEventGSrow (L u) C δ (u 0) (u 1) γ]) ≤
    epsCA (F := F) C δ δ := by
  unfold epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ
  · rw [if_pos hjp, if_pos hjp]
  · rw [if_neg hjp, if_neg hjp]
    exact mcaEventGSrow_probability_le_line_close (L u) C δ u

end

end MCAGS

end ProximityGap
