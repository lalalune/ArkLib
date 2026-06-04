/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.ProofSystem.ToyProblem.Definitions

/-!
# Toy problem soundness bounds (ABF26 §6)

Statement-layer for the §6 soundness bounds that do **not** depend on a
formal protocol object. The three protocol-level soundness lemmas
(`L6.6`, `L6.8`, `L6.10`) live alongside the protocol definitions in
`ToyProblem/Spec/General.lean` (C6.2) and
`ToyProblem/Spec/SimplifiedIOR.lean` (C6.9).

Items in this file:

* `ToyProblem.additive_code_supports_erasure_correction_grs25`
   — Lemma 6.5 [GRS25]: every additive code supports erasure correction
   with correction time `O((s · n)^3)`.

* `ToyProblem.simplified_iop_soundness_listDecoding_lb`
   — Lemma 6.12 [ABF26]: list-decoding-based lower bound on the
   soundness error of the simplified IOR `T'[C, t]` (Construction 6.9).
   Uses Claim B.1 via `Probability.exists_large_image_of_pairwise_collision_bound`.

* `ToyProblem.simplified_iop_soundness_ca_lb`
   — Lemma 6.13 [ABF26]: correlated-agreement-based lower bound on the
   soundness error of `T'[C, t]`.

All three are tagged sorries, but of two distinct kinds:

* **L6.5** is `external admit [GRS25]` — a classical result imported from
  another work; admitting it is acceptable for a survey formalization.
* **L6.12 and L6.13** are `paper-proof-owed` — ABF26's OWN results, proved
  in full in §6.4.1/§6.4.2. They are **in-tree provable now** (L6.12's key
  lemma Claim B.1 is already closed); the sorries are unfinished work, not
  external dependencies. They are stated in coding-theory form (direct
  cardinality bounds on `winningSet`); their protocol-level reading bounds
  the soundness of `ToyProblem.SimplifiedIOR.reduction` from below.

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26]
* [Guruswami, V., Rudra, A., Sudan, M., *Essential Coding Theory*][GRS25]
-/

namespace ToyProblem

open Code InterleavedCode ListDecodable ProximityGap ProbabilityTheory
open scoped NNReal ENNReal ProbabilityTheory

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

/-- **Finite-domain `iSup` attainment helper.** Over a finite domain, a
`⨆` into a conditionally-complete linear order with a bottom (here `ℕ∞`/
`ENNReal`) is attained at some point. Used to extract the CA- / list-maximiser
in `simplified_iop_soundness_ca_lb` and `simplified_iop_soundness_listDecoding_lb`. -/
lemma finite_iSup_eq_apply {α : Type*} [Finite α] [Nonempty α] {β : Type*}
    [ConditionallyCompleteLinearOrderBot β] (g : α → β) :
    ∃ a, (⨆ x, g x) = g a := by
  classical
  obtain ⟨a, ha⟩ := Finite.exists_max g
  exact ⟨a, le_antisymm (ciSup_le ha) (le_ciSup (Set.Finite.bddAbove (Set.finite_range g)) a)⟩

omit [Field F] [Fintype F] in
/-- **Lemma 6.5 of [ABF26]** (= [GRS25]).

Every `F`-additive code `C : F^k → (F^s)^n` supports erasure correction
(in the sense of `CodingTheory.SupportsErasureCorrection`) with correction
time `O((s · n)^3)`. Equivalently: the predicate
`CodingTheory.SupportsErasureCorrection C ecor` holds for some
`ecor ≤ K · (s · n)^3`. We state the more permissive
"some `ecor` works" form here; pinning down the constant `K` requires
modelling the encoder concretely.

PROVEN (existence form). The paper's L6.5 / [GRS25] content is the
*polynomial running time* `O((s·n)^3)`; the `SupportsErasureCorrection`
predicate carries `ecor` as an inert numeric parameter (`_ecor`), so the
*existence* of a correct (not necessarily efficient) erasure-decoder is an
unconditional, in-tree fact: when fewer than `minDist C` symbols are erased
the agreeing codeword is unique (two such codewords would differ only on
the erased coordinates, giving Hamming distance `< minDist C`, forcing
equality), so a classical decoder choosing that witness is well-defined.
We take `ecor = 0` (the numeric time bound is not operationally modelled). -/
theorem additive_code_supports_erasure_correction_grs25
    (C : Set (ι → F)) :
    ∃ ecor : ℕ, CodingTheory.SupportsErasureCorrection C ecor := by
  classical
  -- The "good witness" predicate: a codeword agreeing with `f` off the
  -- erasures, with strictly fewer than `minDist C` erasures.
  set erasureCard : (ι → Option F) → ℕ :=
    fun f ↦ (Finset.univ.filter (fun i ↦ f i = none)).card with hEC
  let good : (ι → Option F) → (ι → F) → Prop :=
    fun f u ↦ u ∈ C ∧ (∀ i, f i = some (u i) ∨ f i = none) ∧ erasureCard f < Code.minDist C
  -- Uniqueness: two good witnesses for the same `f` coincide.
  have huniq : ∀ (f : ι → Option F) (u u' : ι → F), good f u → good f u' → u = u' := by
    intro f u u' ⟨huC, hua, hue⟩ ⟨hu'C, hu'a, _⟩
    by_contra hne
    -- The disagreement set of `u, u'` is contained in the erasure set of `f`.
    have hsub : (Finset.univ.filter (fun i ↦ u i ≠ u' i)) ⊆
        (Finset.univ.filter (fun i ↦ f i = none)) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      -- if `f i ≠ none` then `f i = some (u i) = some (u' i)`, so `u i = u' i`.
      rcases hua i with hfi | hfi
      · rcases hu'a i with hfi' | hfi'
        · exact absurd (Option.some.inj (hfi.symm.trans hfi')) hi
        · rw [hfi] at hfi'; exact absurd hfi' (by simp)
      · exact hfi
    have hdist_le : Δ₀(u, u') ≤ erasureCard f := by
      rw [hEC]; exact Finset.card_le_card hsub
    -- But distinct codewords are `≥ minDist C` apart.
    have hge : Code.minDist C ≤ Δ₀(u, u') := by
      have hd : ‖C‖₀ ≤ Δ₀(u, u') := pairDist_ge_code_mindist_of_ne huC hu'C hne
      rwa [dist_eq_minDist] at hd
    exact absurd (lt_of_le_of_lt (le_trans hge hdist_le) hue) (lt_irrefl _)
  -- The decoder: pick the (unique) good witness when one exists, else `none`.
  let E : (ι → Option F) → Option (ι → F) :=
    fun f ↦ if h : ∃ u, good f u then some h.choose else none
  refine ⟨0, E, fun f ↦ ⟨?_, ?_⟩⟩
  · -- (i) recovery clause
    intro u huC hagree hsmall
    have hgood : good f u := ⟨huC, hagree, hsmall⟩
    have hex : ∃ u, good f u := ⟨u, hgood⟩
    change E f = some u
    simp only [E, dif_pos hex]
    exact congrArg some (huniq f hex.choose u hex.choose_spec hgood)
  · -- (ii) failure clause
    intro hno
    have : ¬ ∃ u, good f u := by
      rintro ⟨u, huC, hagree, hsmall⟩
      exact hno ⟨u, huC, hagree, hsmall⟩
    change E f = none
    simp only [E, dif_neg this]

omit [DecidableEq F] in
/-- **Lemma 6.12 of [ABF26]** (list-decoding lower bound on the simplified IOR).

Coding-theory form: if `|F| > binomial(|Λ(C^{≡2}, δ)|, 2)`, then there
exist witnesses `(v, μ_1, μ_2, f_1, f_2)` with `(f_1, f_2)` lying outside
the relaxed relation `R̃_{C,δ}^2`, for which the winning challenge set
`Ω^{f_1,f_2}_{v,μ_1,μ_2}` (Definition 6.11) has at least
`|Λ(C^{≡2}, δ)| · |F| / (|F| + |Λ(C^{≡2}, δ)| - 1)` elements.

The protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9, `ToyProblem.SimplifiedIOR.reduction`) is
at least `|Λ(C^{≡2}, δ)| / (|F| + |Λ(C^{≡2}, δ)| - 1)`.

## Proof recipe (ABF26 §6.4.1, with B.1 now machine-checked)

The bound `N · F / (F + N − 1)` (writing `N := |Λ(C^{≡2}, δ)|`,
`F := |F|`) is exactly the conclusion of Claim B.1 specialised to
`|S| = N`, `|T| = F`, `ε = 1/F`:
```
N / (1 + (N − 1) · (1/F)) = N · F / (F + N − 1)
```
so the proof skeleton is:

1. **Build the list.** Enumerate `Λ(C^{≡2}, δ)` as `λ : Fin N → ι → F × ι → F`,
   pairs `(W₀(λ), W₁(λ))` of `δ`-close codewords in `C` (paper writes
   `(v_0(λ), v_1(λ))`). Pick any `v ∈ F^k` and define the "evaluation"
   function `φ_v : Fin N → F × F` by `λ ↦ (⟨W₀(λ), v⟩, ⟨W₁(λ), v⟩) — μ`-pair shape.

2. **Pairwise collision bound.** For `λ ≠ λ'` with `(W₀(λ), W₁(λ)) ≠
   (W₀(λ'), W₁(λ'))`, the linear functional `⟨·, v⟩` collides on the
   distinct difference vector with probability `1/F` over a uniform
   `v ←$ F^k`. This is the in-tree predicate
   `Pr_{ let v ←$ᵖ (Fin k → F) }[(decide (φ_v λ = φ_v λ') : Prop)] ≤ 1/F`.
   Unfold via [`ProbabilityTheory.Pr_decide_eq_tsum_indicator`] from
   [`Probability/Notation.lean`](../../Data/Probability/Notation.lean).

3. **Apply B.1.** Feed steps 1 + 2 into
   [`Probability.exists_large_image_of_pairwise_collision_bound`]
   (`ArkLib/Data/Probability/Combinatorial.lean`) to obtain a
   `v* ∈ F^k` whose induced `φ_{v*}` has image size at least
   `N · F / (F + N − 1)` in `F × F`.

4. **Convert to winning set.** Each distinct `(μ₁, μ₂) ∈ image φ_{v*}`
   corresponds to a `γ ∈ winningSet` via the list-decoding bijection
   (paper §6.4.1 — `μ_i = ⟨W_i(λ), v*⟩` for some `λ`, and the constraint
   `μ_new = μ₁ + γ · μ₂` admits a unique `γ` per such pair under the
   `|F| > binom(N, 2)` regime). The witness `(v*, μ₁, μ₂, f₁ := W₀,
   f₂ := W₁)` for some chosen `λ₀ ∈ Λ` exits the proof.

## Audit revision (2026-06): the residual is NOT "step 4 only"

A prior disposition claimed steps 1–3 were "in scope" and only the step-4
bijection remained. Probing the actual definitions shows THREE open
sub-problems beyond B.1, each substantial and without an in-tree helper:

  * **Step 1 (iSup maximizer extraction).** `Lambda C δ = ⨆ f, (close…).ncard`
    is `ℕ∞`-valued. The outer `iSup` over `f : ι → F` is over a FINITE type
    (good — the max is attained), but there is no `Lambda`-attainment lemma
    and the `ℕ∞`/`.toNat` bookkeeping (including the `Lambda = ⊤` branch,
    where `.toNat = 0` makes the bound trivial) is unwritten. Enumerating
    `Λ(C^{≡2}, δ)` as `λ : Fin N → …` then needs `Set.Finite.toFinset` +
    an explicit `Fin N` indexing of the maximizing list.

  * **Step 2 (collision probability) is OPEN.** The needed bound
    `Pr_{v ←$ F^k}[⟨W₀(λ)−W₀(λ'),v⟩ = 0 ∧ ⟨W₁(λ)−W₁(λ'),v⟩ = 0] ≤ 1/F`
    for distinct codeword pairs is a linear-functional non-degeneracy fact
    (a nonzero linear form vanishes on a `1/|F|` fraction of `F^k`). There
    is NO in-tree lemma for this; only the generic
    `Pr_decide_eq_tsum_indicator` unfolder exists. It is a real
    finite-field linear-algebra argument (kernel of a nonzero functional has
    index `|F|`).

  * **Step 4 (`relation` linear-encode existential) — undocumented wall.**
    `winningSet`/`relaxedRelation (ℓ=1)` requires `relation C v μ Wstar`,
    which existentially demands `Wstar = encode(M)` for an `F`-LINEAR
    `encode : (Fin k → F) →ₗ[F] (ι → F)` with `image ⊆ C` — STRICTLY
    STRONGER than `Wstar ∈ C`. The list-decoding codewords `W_i(λ) ∈ C` do
    NOT, for an arbitrary `Set` `C`, come with such a linear encoder, so
    "γ winning ⟸ image point" does not close without a linearity/encoder
    hypothesis on `C` (the paper takes `C` as the image of an explicit
    additive encoder; the Lean `Set`-form `relation` faithfully encodes that
    but does not let an arbitrary close codeword satisfy it). This is a
    statement-level gap, not just proof effort.

Tagged sorry (`paper-proof-owed` — ABF26's OWN result, proved in §6.4.1).
B.1 (step 3) is closed, but steps 1, 2, 4 above are each open; step 4 in
particular needs a linear-code/encoder hypothesis added to the statement
(or a `relation`-from-membership bridge lemma) before it is provable. -/
theorem simplified_iop_soundness_listDecoding_lb {k : ℕ}
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    (_hF : (Fintype.card F : ℝ) >
      ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat).choose 2) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ((winningSet C δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) ≥
        (((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
            * Fintype.card F)
          / (Fintype.card F
              + ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ) - 1) := by
  -- ABF26-L6.12; paper-proof-owed [ABF26 §6.4.1]. Paper's OWN result with a
  -- full elementary proof; IN-TREE PROVABLE NOW — its key lemma Claim B.1
  -- (`Probability.exists_large_image_of_pairwise_collision_bound`) is already
  -- closed. Follow §6.4.1: build the collision map `φ_v` and apply B.1.
  sorry

/-- **Lemma 6.13 of [ABF26]** (correlated-agreement lower bound on the simplified IOR).

Coding-theory form: there exist `(v, μ_1, μ_2, f_1, f_2)` with
`(f_1, f_2)` outside the relaxed relation `R̃_{C,δ}^2` whose winning
challenge set has size at least `ε_ca(C, δ) · |F|`.

Protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9) is at least `ε_ca(C, δ)`.

Proof sketch: take `f_1, f_2` maximising the CA error; then
`f_1 + γ·f_2` is `δ`-close to `C` precisely on a set `S` of size
`ε_ca · |F|`, and `S` is contained in the winning set
`Ω^{f_1,f_2}_{0^k, 0, 0}` of Definition 6.11.

## Documented statement repair (2026-06): linear-encoder hypothesis on `C`

The prior audit identified a *statement-level* wall, not mere proof effort.
`epsCA C δ δ = ⨆ u : WordStack F (Fin 2) ι, if jointProximity … then 0 else
Pr_{γ}[…]`, and the conclusion bounds `|winningSet C δ 0 0 0 f₁ f₂|` from
below. Membership `γ ∈ winningSet C δ 0 0 0 f₁ f₂` unfolds (Definition 6.11,
`ℓ = 1`, `v = μ₁ = μ₂ = 0`) to `relaxedRelation C δ 0 0 (f₁ + γ·f₂)`, i.e.
`∃ Wstar, relation C 0 0 Wstar ∧ (f₁+γ·f₂) δ-close to Wstar`. From
`δᵣ(f₁+γ·f₂, C) ≤ δ` one extracts a close codeword `c ∈ C`, but `relation`
additionally demands `c = encode(M)` for an `F`-LINEAR `encode : (Fin k → F)
→ₗ[F] (ι → F)` with `image ⊆ C` — STRICTLY STRONGER than `c ∈ C` for an
arbitrary `Set C`.

ABF26 take `C` as the image of an explicit `F`-additive encoder; the Lean
`Set`-form `relation` faithfully encodes that but cannot let an arbitrary
close codeword satisfy it. We therefore repair the statement (in-file
precedent: the `relation`/`relaxedRelation` definitions themselves carry the
encoder existential) by hypothesising that `C` IS the image of an `F`-linear
encoder, via `hEnc`. This is exactly the regime in which the toy-problem
relation is intended (Definition 6.1: "the chosen encoding is a bijection
from `Fin k → F` onto `C`"). Under `hEnc`, `relation C 0 (fun _ ↦ 0) (fun _
↦ c)` holds for *every* `c ∈ C` (take `M` a pre-image of `c`; the linear
constraint `∑_j M·0 = 0 = μ` is vacuous at `μ = 0`), closing the wall.

Tagged proof (`paper-proof` — ABF26's OWN result, proved in §6.4.2).
The bound is in terms of `ε_ca` (correlated agreement) rather than `ε_mca`
(mutual correlated agreement); the latter would be qualitatively stronger
but no attack reaching `ε_mca > ε_ca` is currently known (Remark 6.14). -/
theorem simplified_iop_soundness_ca_lb {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    -- Statement repair: `C` is the image of an `F`-linear encoder (ABF26's
    -- standing assumption; `relation` demands this encoder, see docstring).
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ((winningSet (k := k) C δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal)
        ≥ epsCA (F := F) (A := F) C δ δ * (Fintype.card F : ENNReal) := by
  classical
  -- ABF26-L6.13 [§6.4.2]. The CA-maximising `(f₁,f₂)` makes the winning set
  -- (at `v=μ₁=μ₂=0`) contain `S = {γ : δᵣ(f₁+γ·f₂,C) ≤ δ}`, of size `ε_ca·|F|`.
  obtain ⟨encode, hEnc_mem, hEnc_surj⟩ := hEnc
  -- `relation`-from-membership bridge under the encoder hypothesis: every
  -- codeword `c ∈ C` is a valid `relation C 0 (fun _ ↦ 0)` witness stack.
  have hrel_of_mem : ∀ c : ι → F, c ∈ C →
      relation (k := k) (ℓ := 1) C (0 : Fin k → F) (fun _ ↦ (0 : F)) (fun _ ↦ c) := by
    intro c hc
    obtain ⟨m, hm⟩ := hEnc_surj c hc
    exact ⟨fun _ ↦ m, ⟨encode, hEnc_mem, fun _ ↦ hm.symm⟩, by intro i; simp⟩
  -- Step 1: extract a maximizer of the finite `⨆` defining `epsCA`.
  -- `epsCA` is an `iSup` over the Fintype `WordStack F (Fin 2) ι`.
  set g : WordStack F (Fin 2) ι → ENNReal := fun u =>
    if jointProximity C (u := u) δ then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] with hg_def
  have hepsCA_eq : epsCA (F := F) (A := F) C δ δ = ⨆ u, g u := rfl
  obtain ⟨u₀, hu₀⟩ := finite_iSup_eq_apply g
  rw [hepsCA_eq, hu₀]
  -- Witness: `v = 0`, `μ₁ = μ₂ = 0`, `f₁ = u₀ 0`, `f₂ = u₀ 1`.
  refine ⟨(0 : Fin k → F), 0, 0, u₀ 0, u₀ 1, ?_⟩
  -- Case on the `jointProximity` branch of `g u₀`.
  by_cases hjp : jointProximity C (u := u₀) δ
  · -- Trivial branch: `g u₀ = 0`, bound is `≥ 0`.
    simp only [hg_def, hjp, if_true, zero_mul, ge_iff_le, zero_le]
  · -- Main branch: `g u₀ = Pr_{γ}[δᵣ(u₀ 0 + γ • u₀ 1, C) ≤ δ]`.
    simp only [hg_def, hjp, if_false]
    -- The winning set contains `S = {γ : δᵣ(u₀ 0 + γ • u₀ 1, C) ≤ δ}`.
    set S : Finset F := Finset.univ.filter
      (fun γ => δᵣ(u₀ 0 + γ • u₀ 1, C) ≤ δ) with hS_def
    -- `Pr · |F| = |S|`.
    have hPr : Pr_{let γ ← $ᵖ F}[δᵣ(u₀ 0 + γ • u₀ 1, C) ≤ δ] =
        (((S.card : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) := by
      rw [prob_uniform_eq_card_filter_div_card (F := F)
        (P := fun γ => δᵣ(u₀ 0 + γ • u₀ 1, C) ≤ δ)]
      norm_cast
    -- `S ⊆ winningSet C δ 0 0 0 (u₀ 0) (u₀ 1)`.
    have hsub : ↑S ⊆ winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u₀ 0) (u₀ 1) := by
      intro γ hγ
      simp only [hS_def, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hγ
      -- `δᵣ(u₀ 0 + γ • u₀ 1, C) ≤ δ` gives a close codeword `c ∈ C`.
      rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at hγ
      obtain ⟨c, hc_mem, hc_dist⟩ := hγ
      -- Build `relaxedRelation`: `c` is the relation witness, agreement set from closeness.
      refine ⟨fun _ => c, ?_, ?_⟩
      · -- `relation C 0 (fun _ ↦ μ₁+γμ₂ = 0) (fun _ ↦ c)`.
        simpa using hrel_of_mem c hc_mem
      · -- Agreement set of size `(1-δ)·|ι|` from `δᵣ(u₀ 0 + γ • u₀ 1, c) ≤ δ`.
        rw [relCloseToWord_iff_exists_agreementCols] at hc_dist
        obtain ⟨T, hT_card, hT_agree⟩ := hc_dist
        refine ⟨T, ?_, ?_⟩
        · -- `(1-δ)·|ι| ≤ |T|`.
          have hcomp := (relDist_floor_bound_iff_complement_bound (Fintype.card ι) T.card δ).mp
            hT_card
          -- hcomp : (1 - δ) * (card ι : ℝ≥0) ≤ (T.card : ℝ≥0) in ℝ≥0; cast to ℝ.
          have hδle : δ ≤ 1 := le_of_lt _hδ_lt
          have hcompR : ((1 - δ : ℝ≥0) : ℝ) * (Fintype.card ι : ℝ) ≤ (T.card : ℝ) := by
            have := (NNReal.coe_le_coe.mpr hcomp)
            rwa [NNReal.coe_mul, NNReal.coe_natCast] at this
          rwa [NNReal.coe_sub hδle, NNReal.coe_one] at hcompR
        · -- Agreement: on `T`, `(u₀ 0 + γ • u₀ 1) j = c j`.
          intro i j hj
          have := (hT_agree j).1 hj
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    -- Conclude: `|winningSet| ≥ |S| = Pr · |F|`.
    rw [hPr]
    have hwin_fin : (winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u₀ 0) (u₀ 1)).Finite :=
      Set.toFinite _
    have hcard_le : (S.card : ℕ) ≤
        (winningSet (k := k) C δ (0 : Fin k → F) 0 0 (u₀ 0) (u₀ 1)).ncard := by
      rw [← Set.ncard_coe_finset S]
      exact Set.ncard_le_ncard hsub hwin_fin
    -- `Pr · |F| = |S| ≤ |winningSet|` in ENNReal.
    have hcardF_ne : (Fintype.card F : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    have heq : (((S.card : ℝ≥0) / (Fintype.card F : ℝ≥0) : ℝ≥0) : ENNReal) *
        (Fintype.card F : ENNReal) = (S.card : ENNReal) := by
      rw [← ENNReal.coe_natCast (Fintype.card F), ← ENNReal.coe_mul,
        div_mul_cancel₀ _ hcardF_ne, ENNReal.coe_natCast]
    rw [heq]
    exact_mod_cast hcard_le

end ToyProblem
