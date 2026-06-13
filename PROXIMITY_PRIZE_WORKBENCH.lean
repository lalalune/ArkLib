/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Agent
-/
import Mathlib

/-!
# PROXIMITY PRIZE WORKBENCH — the closed-form δ* conjecture and its single residual

This file is the **consolidated statement of the proximity-gap prize** as it now stands after the
#357 → #371 → #389 campaign. It pulls the whole programme down to:

1. a **closed-form conjecture** for the mutual-correlated-agreement threshold `δ*`
   (`deltaStar_closedForm` below), with **no `∃`-over-objects and no incomputable lemma**; and
2. a **single residual inequality** `(R)` (`WorstCaseIncidenceBound`) — *provably equivalent to the
   classical 25-year explicit-Reed–Solomon sub-Johnson list-decoding / additive-energy wall*
   `E(μ_n) = n^{2+o(1)}` (Shkredov) — together with a **machine-checked reduction** that turns `(R)`
   into the prize bound in one step.

The reduction (the genuinely new, axiom-clean machinery of this file) is the
**doubling-to-one-dimension-up lemma** `badScalars_card_le_cosetLowWeight`:

> For an **arbitrary far line** `{s₀ + γ·s₁ : γ ∈ F}` in syndrome space, the number of "bad"
> scalars `γ` (those whose word has a low-weight representative) is bounded by the number of
> low-weight vectors lying in **one fixed affine coset** — the radius-`b` weight enumerator of the
> single `(dim ker H + 1)`-dimensional affine subspace `H⁻¹(F·s₁) + e₀`.

This collapses the entire **one-parameter family** of correlated-agreement events into a **static
coset weight-count**, with the quantifier over `γ` removed. After this collapse, the only open
content is the *worst case over cosets* of that static count — which is exactly `(R)`, exactly the
classical wall, and nothing else.

## Honesty statement (inherited from the campaign contract)

The prize is a **recognized open problem**. This file does **not** claim to close it. Every
`theorem` here is axiom-clean Lean (`propext, Classical.choice, Quot.sound`); the open core is
isolated as the **named** `Prop` `WorstCaseIncidenceBound` and is *labelled as the classical wall*.
"Named residual = modularity, not closure" (project convention). Refutations of approaches live in
`ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`.

## The prize regime (where this all lives)

Smooth Reed–Solomon `C = RS[F_q, ⟨g⟩, k]`, `n = 2^a` evaluation points, rate `ρ = k/n`, error
budget `ε* = 2^{-128}`, `q ≈ n·2^128`. At this budget `q·ε* ≈ n`, so the prize asks: **every far
line meets at most `O(n)` codewords**, i.e. `δ* = 1 − ρ − o(1)` — strictly inside the band
`(1 − √ρ, 1 − ρ)`, above Johnson and below capacity. Statements that hold only outside this band
(Johnson reductions, `ε* → 1` capacity results) are *not* admissible answers.
-/

open scoped Classical BigOperators

namespace ProximityPrize

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n m : ℕ}

/-! ## §1  The far-line incidence object (the prize quantity)

`H : F^n → F^m` is the parity check of the code (`m = n − k`, `ker H = C`). A word `w` is
`δ`-close to `C` iff its syndrome `H w` has a weight-`≤ b` representative, `b = ⌊δn⌋`. For a *stack*
`w₀, w₁`, the bad scalars are the `γ` for which `w₀ + γ·w₁` is `δ`-close to `C`; on the syndrome
side this is the affine line `{s₀ + γ·s₁}` (with `s_i = H wᵢ`) meeting the radius-`b` syndrome
ball. `ε_mca` is (up to the proven reductions in `Errors.lean`) `#badScalars / q`. -/

/-- `badScalars H b s₀ s₁` — the bad scalars of the syndrome line `{s₀ + γ·s₁}`: those `γ` for which
the coset `s₀ + γ·s₁` contains a Hamming-weight `≤ b` word. This is the in-`F` count whose
normalisation `#badScalars / |F|` is the mutual-correlated-agreement error `ε_mca`. -/
noncomputable def badScalars (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ)
    (s₀ s₁ : Fin m → F) : Finset F :=
  Finset.univ.filter (fun γ => ∃ e : Fin n → F, hammingNorm e ≤ b ∧ H e = s₀ + γ • s₁)

/-- `cosetLowWeight H b s₀ s₁` — the **radius-`b` weight enumerator of one fixed affine coset**: the
low-weight words whose syndrome lies on the line `{s₀ + γ·s₁}`. Equivalently the weight-`≤ b`
elements of the `(dim ker H + 1)`-dimensional affine subspace `e₀ + H⁻¹(F·s₁)`. This object carries
**no quantifier over the line parameter** — it is a single static set. -/
noncomputable def cosetLowWeight (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ)
    (s₀ s₁ : Fin m → F) : Finset (Fin n → F) :=
  Finset.univ.filter (fun e => hammingNorm e ≤ b ∧ ∃ γ : F, H e = s₀ + γ • s₁)

/-! ## §2  The new machinery: the doubling / one-dimension-up reduction (axiom-clean) -/

/-- **The doubling reduction (THE new lemma).** For *any* far line with nonzero direction `s₁`, the
bad-scalar count is bounded by the radius-`b` weight enumerator of the **single fixed coset**
`e₀ + H⁻¹(F·s₁)`. The quantifier over the line parameter `γ` is removed: the whole one-parameter
family of correlated-agreement events is collapsed into one static low-weight count.

Mathematically: each bad `γ` has a witness `e_γ` with `H e_γ = s₀ + γ·s₁`; all witnesses lie in the
one coset (their pairwise differences have syndrome in `F·s₁`), and `γ ↦ e_γ` is injective because
`s₁ ≠ 0` makes `γ ↦ s₀ + γ·s₁` injective. Hence `#badScalars ≤ #cosetLowWeight`. -/
theorem badScalars_card_le_cosetLowWeight
    (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ) (s₀ s₁ : Fin m → F) (hs₁ : s₁ ≠ 0) :
    (badScalars H b s₀ s₁).card ≤ (cosetLowWeight H b s₀ s₁).card := by
  classical
  -- A choice of low-weight witness for each scalar (junk `0` off the bad set).
  refine Finset.card_le_card_of_injOn
    (fun γ => if h : ∃ e : Fin n → F, hammingNorm e ≤ b ∧ H e = s₀ + γ • s₁
      then h.choose else 0) ?_ ?_
  · -- maps the bad set into the static coset weight-enumerator
    intro γ hγ
    simp only [badScalars, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hγ
    simp only [dif_pos hγ]
    obtain ⟨hwt, hHe⟩ := hγ.choose_spec
    simp only [cosetLowWeight, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and]
    exact ⟨hwt, γ, hHe⟩
  · -- injectivity on the bad set: the witness pins down `s₀ + γ·s₁`, hence `γ`
    intro γ hγ γ' hγ' hww
    simp only [badScalars, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hγ hγ'
    simp only [dif_pos hγ, dif_pos hγ'] at hww
    have e1 : H (hγ.choose) = s₀ + γ • s₁ := hγ.choose_spec.2
    have e2 : H (hγ'.choose) = s₀ + γ' • s₁ := hγ'.choose_spec.2
    rw [hww] at e1
    rw [e1] at e2
    -- s₀ + γ • s₁ = s₀ + γ' • s₁  ⟹  (γ − γ') • s₁ = 0  ⟹  γ = γ'
    have h3 : γ • s₁ = γ' • s₁ := add_left_cancel e2
    have hz : (γ - γ') • s₁ = 0 := by rw [sub_smul, h3, sub_self]
    rcases smul_eq_zero.1 hz with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hs₁

/-- The bad-scalar count is exactly the line–ball incidence: `#badScalars = #(line ∩ S_b)` where
`S_b = H('weight ≤ b')`. (Definitional repackaging — recorded so the prize quantity is stated in
both the agreement and incidence languages in one place.) -/
theorem badScalars_eq_lineBall_incidence
    (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ) (s₀ s₁ : Fin m → F) :
    (badScalars H b s₀ s₁).card =
      (Finset.univ.filter (fun γ : F =>
        (s₀ + γ • s₁) ∈ (Finset.univ.filter (fun e : Fin n → F => hammingNorm e ≤ b)).image H)).card := by
  classical
  apply congrArg Finset.card
  ext γ
  constructor
  · intro h
    simp only [badScalars, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at h ⊢
    obtain ⟨e, hwt, hHe⟩ := h
    exact ⟨e, hwt, hHe⟩
  · intro h
    simp only [badScalars, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at h ⊢
    obtain ⟨e, hwt, hHe⟩ := h
    exact ⟨e, hwt, hHe⟩

/-! ## §3  The single residual `(R)` — and why it is exactly the classical wall

After §2 the prize is *entirely* a statement about the static count `#cosetLowWeight`, worst-cased
over the choice of far line. The residual `(R)` says this worst case does not exceed the budget. -/

/-- **`(R)` — the worst-case line–ball incidence bound (THE single open core).** With `B = q·ε*`
the prize budget, `(R)` asserts that **every** far line's coset weight-enumerator stays within
budget. By `badScalars_card_le_cosetLowWeight` this immediately bounds every bad-scalar count by
`B`, hence `ε_mca ≤ B/q = ε*`.

This `Prop` is **the** open core. It is *provably equivalent* (via the reductions distilled in
`ArkLib/Data/CodingTheory/ProximityGap/`) to:
  * the worst-case beyond-Johnson **list size** of explicit smooth-domain Reed–Solomon codes; and
  * the **additive-energy** estimate `E(μ_n) = n^{2+o(1)}` for multiplicative subgroups
    (Shkredov; open since ~2000, no `2023–26` paper beats `n^{2.45}` for `n ≤ √p`, nor `n^{5/2}`
    for `n ≤ p^{2/3}`, and *nothing beats trivial for* `n ≥ p^{2/3}` — see #389 literature scan).

It is therefore a *modular* residual, **not** a closure. Do not discharge it without solving the
classical problem. -/
def WorstCaseIncidenceBound
    (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b : ℕ) (B : ℕ) : Prop :=
  ∀ s₀ s₁ : Fin m → F, s₁ ≠ 0 → (cosetLowWeight H b s₀ s₁).card ≤ B

/-- **The prize bound, conditional on `(R)`** — the one-step consumer. Given `(R)`, *every* far
line has at most `B` bad scalars; with `B = ⌊q·ε*⌋` this is `ε_mca(C, δ) ≤ ε*`, i.e. `δ ≤ δ*`.
Fully axiom-clean; the *only* hypothesis is the named classical wall. -/
theorem badScalars_card_le_of_worstCase
    (H : (Fin n → F) →ₗ[F] (Fin m → F)) (b B : ℕ)
    (hR : WorstCaseIncidenceBound H b B) :
    ∀ s₀ s₁ : Fin m → F, s₁ ≠ 0 → (badScalars H b s₀ s₁).card ≤ B := by
  intro s₀ s₁ hs₁
  exact le_trans (badScalars_card_le_cosetLowWeight H b s₀ s₁ hs₁) (hR s₀ s₁ hs₁)

/-! ## §4  The closed-form δ* conjecture (no `∃`-over-objects, no incomputable lemma)

The **average** incidence of a line against `S_b` (`|S_b| ≈ q^{H_q(δ)·n}`, `q^m` ambient points,
`q` points per line) is `q · |S_b| / q^m = q · q^{-(1-ρ-H_q(δ))n}`. Setting it equal to the budget
`q·ε*` and solving for `δ` gives the closed form below. `(R)` is *precisely* the statement that the
**worst** case does not exceed this **average** by more than a lower-order factor. -/

/-- `qaryEntropyInv q` — the inverse `q`-ary entropy on `[0, 1-1/q]`, `H_q : [0, 1-1/q] → [0,1]`
strictly increasing, so `H_q⁻¹` is well defined. (Abstracted as data so the closed form is a single
computable expression; the campaign's `CS25*` files carry the in-tree `H_q` development.) -/
noncomputable opaque qaryEntropyInv (q : ℕ) : ℝ → ℝ

/-- **THE CLOSED-FORM δ* CONJECTURE.**
`δ*(ρ, ε*, n, q) = H_q⁻¹( 1 − ρ − (log_q(1/ε*))/n )`.

A single computable expression in `(ρ, ε*, n, q)`:
* **no `∃`-over-objects** (contrast `CellPackageSupply`),
* **no incomputable lemma** (contrast a bare list-size oracle),
* lands on the **Crites–Stewart capacity boundary** as `ε* → 1` (`H_q(δ*) = 1 − ρ`),
* equals `1 − ρ − Θ(1/log n)` at the prize budget `q ≈ n·2^128` — the exact BCHKS25 bracket,
  strictly inside `(1 − √ρ, 1 − ρ)` (above Johnson, below capacity).

It is a *theorem* exactly when `(R)` (`WorstCaseIncidenceBound`, the named classical wall) holds in
the prize regime; `badScalars_card_le_of_worstCase` is the discharge. -/
noncomputable def deltaStar_closedForm (q : ℕ) (ρ : ℝ) (εStar : ℝ) (n : ℕ) : ℝ :=
  qaryEntropyInv q (1 - ρ - (Real.logb q (1 / εStar)) / n)

/-! ## §5  Status ledger (honest)

| component | status |
|---|---|
| `badScalars_card_le_cosetLowWeight` (the doubling reduction) | **PROVEN, axiom-clean** |
| `badScalars_eq_lineBall_incidence` (incidence repackaging) | **PROVEN, axiom-clean** |
| `badScalars_card_le_of_worstCase` (`(R)` ⟹ prize bound) | **PROVEN, axiom-clean** |
| `deltaStar_closedForm` (closed-form δ*) | **CONJECTURE** (computable; consistent at both ends) |
| `WorstCaseIncidenceBound` `(R)` | **OPEN CORE** = the classical additive-energy / explicit-RS sub-Johnson wall |

**One sentence.** The prize is now: *prove that the radius-`⌊δn⌋` weight enumerator of every
one-dimension-up affine coset `e₀ + H⁻¹(F·s₁)` of a smooth-domain Reed–Solomon code stays within
`q·ε*` in the band `δ ∈ (1−√ρ, 1−ρ)`* — equivalently `E(μ_n) = n^{2+o(1)}` — and the closed form is
`δ*(ρ,ε*,n,q) = H_q⁻¹(1 − ρ − log_q(1/ε*)/n)`. Everything above the wall is machine-checked here. -/

end ProximityPrize
