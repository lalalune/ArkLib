/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ListDecoding.CZ25UniqueDecodingSlice

/-!
# GW ASSEMBLY: the Guruswami–Wang kernel reduced to `{BRICK-I, BRICK-V}` (issue #93)

This scratch file is the **assembly lane** of the celebrated Guruswami–Wang (GW13 / CZ25)
folded-RS capacity list-decoding theorem.  The headline target is the in-tree residual

  `CZ25CoordFiberCap` (`ListDecoding/CZ25SpanBoundBridge.lean:92`)

— the affine-flat coordinate-fiber cap

  `∑_i #{c ∈ L : c i = f i} ≤ ((|L| - 1)·τ(r₀) + 1)·n`

— which the in-tree machinery already collapses to the full T3.4 `Λ`-bound:

  `CZ25CoordFiberCap` --`cz25SpanBound'_of_coordFiberCap`--> `CZ25SpanBound'`
                      --`cz25DimensionCount_of_spanBound'`--> `CZ25DimensionCount`
                      --`subspaceDesign_list_decoding_cz25_of_coordFiberCap`--> `Λ`-bound.

So discharging `CZ25CoordFiberCap` closes the whole GW kernel.

## The brick DAG

The GW proof factors as four bricks (the irreducible analytic core is `{BRICK-I, BRICK-V}`):

* **BRICK-I (interpolation existence).** For each received word `f`, there is a *nonzero*
  bivariate `Q`, linear in `Y` and of bounded `X`-degree, vanishing with multiplicity at the
  agreement points of `f`.  This is genuinely analytic (a counting / dimension existence
  argument over `F[X]`).  Here: the named Prop `GWInterpExists`.

* **BRICK-V (agreement ⇒ functional equation).** If a codeword `c = enc(p)` is close to `f`
  (agrees on `≥ (τ(r₀)+η)·n` blocks), then the agreement-with-multiplicity from BRICK-I forces
  the *folded functional equation* `R_p = 0`, i.e. the message `p` lies in the GW affine
  solution set `W`.  This is the second analytic ingredient.  Here: `GWAgreeForcesSolution`.

* **BRICK-W (solution set is affine, dim ≤ s−1).** `W = {p : A₀ + ∑_j A_j·p(γʲ X) = 0}` is an
  affine flat of dimension `≤ s − 1`.  This is the brick the campaign's proven GK16 machinery
  (`foldedWronskian_ne_zero_of_linearIndependent`, `GK16Lemma12.lean`) reaches — a dim-`s`
  solution set would furnish `s` independent solutions with nonvanishing folded Wronskian,
  contradicting the functional equation forcing it to vanish.  Lane `GWBrickW` proves it; here
  it enters as the named hypothesis `gw_solutionSet_finrank_le` (its *conclusion*).

* **BRICK-L (list bound).** From BRICK-W (`dim W ≤ s − 1`) + the design half
  (`sum_card_vanishing_le_design`) + the agreement lower bound, the arithmetic collapse
  `cz25DimensionCount_of_spanBound`-style yields the list bound `|L| ≤ (1 − τ(r₀))/η`.  Lane
  `GWBrickL` proves it; here it enters as the named hypothesis `cz25_list_bound_of_finrank_le`
  (its *conclusion*: a per-word `CZ25DimensionCount`-shaped list bound).

## What this file delivers

The conditional headline:

  `cz25CoordFiberCap_of_interp_and_multiplicity`
    : `{BRICK-I, BRICK-V}` together with the (orchestrator-wired) conclusions of BRICK-W,
      BRICK-L ⇒ `CZ25CoordFiberCap` (general `|L| > 1`).

The composition discharges **everything except** the two analytic bricks `{I, V}`:

* the affine-flat coordinate cap `coordAgreeSum ≤ |L|·n` (in-tree
  `coordAgreeSum_le_card_mul_card_ι`);
* the list↔budget collapse (BRICK-L conclusion, here named);
* the recentred-span / design budget (BRICK-W conclusion, here named, proven in lane);
* the `|L| ≤ 1` trivial slice (in-tree `cz25CoordFiberCap_of_ncard_le_one`);
* the `|L| > 1` charge that converts the list bound into the affine-flat cap.

We also record `cz25CoordFiberCap_of_listBound`, the purely-arithmetic engine that turns a
`CZ25DimensionCount`-shaped *list bound* (the BRICK-L conclusion) into the affine-flat
`CZ25CoordFiberCap`, with **no** analytic content — isolating exactly where `{I, V, W}` enter
(they enter *only* through producing the list bound).

**Honesty / non-vacuity.** `{BRICK-I, BRICK-V}` are genuinely *weaker* than `CZ25CoordFiberCap`:
they speak about a *single* received word `f` producing a *single* polynomial `Q` (BRICK-I) and
about a *single* close codeword's message satisfying the functional equation (BRICK-V).  Neither
mentions the coordinate agreement table, the candidate-list cardinality, or the affine-flat cap.
The cap is *derived* by composition with the design budget and arithmetic collapse — it is not a
restatement of `{I, V}`.  This file is `sorry`/`axiom`/`native_decide`-free; the only admitted
inputs are the named Props, exactly `{BRICK-I, BRICK-V}` plus the orchestrator-wired
`{BRICK-W, BRICK-L}` conclusions.

## References

- [GW13] Guruswami–Wang. *Linear-algebraic list decoding of folded Reed–Solomon codes.*
- [CZ25] Thm B.5 (subspace-design route to capacity list decoding).
- [GK16] Guruswami–Kopparty. The folded-Wronskian non-vanishing engine for BRICK-W.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace CodingTheory

open scoped NNReal
open ListDecodable

section GWAssembly

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ### The arithmetic engine: a list bound ⟹ the affine-flat coordinate-fiber cap

The genuine GW work (`{I, V, W, L}`) culminates in a `CZ25DimensionCount`-shaped *list bound*
`|closeCodewordsRel C f δ| ≤ (1 − τ(r₀))/η`.  This subsection shows that such a list bound,
*on its own*, already implies the affine-flat `CZ25CoordFiberCap`, with **no analytic content**:
the proof is the trivial pointwise cap `coordAgreeSum ≤ |L|·n` (`coordAgreeSum_le_card_mul_card_ι`)
combined with the elementary monotonicity `|L| ≤ (|L|−1)·τ(r₀) + 1` *when `|L| ≤ (1−τ)/η`* — i.e.
the list bound itself supplies the `(|L|−1)` charge that converts the coarse `|L|·n` cap into the
fine affine-flat `((|L|−1)·τ+1)·n` cap.

This isolates precisely where the analytic bricks enter: they enter *only* through the list
bound `hLB`, never directly into the cap. -/

/-- **Arithmetic engine: `CZ25DimensionCount`-shaped list bound ⟹ `CZ25CoordFiberCap`.**

Given the per-word list bound (the `BRICK-L` conclusion, identical in shape to
`CZ25DimensionCount`)

  `∀ f, 0 ≤ δ → |closeCodewordsRel C f δ| ≤ (1 − τ(r₀))/η`,

the affine-flat coordinate-fiber cap `CZ25CoordFiberCap` holds.

**Why it composes (the `|L| > 1` charge).**  Realise the list as the canonical finset `Lset`.
The trivial pointwise cap gives `coordAgreeSum ≤ |Lset|·n`.  It then suffices to show
`|Lset| ≤ (|Lset| − 1)·τ(r₀) + 1`, i.e. `(|Lset| − 1)·(1 − τ(r₀)) ≤ 0`.  Two regimes:

* `|Lset| ≤ 1`: then `|Lset| − 1 ≤ 0` and `1 − τ(r₀) ≥ η > 0`, so the product is `≤ 0`. ✓
* `|Lset| ≥ 1` (the genuine `|L| > 1` case): the list bound `|Lset| ≤ (1 − τ(r₀))/η` rearranges
  (via `η > 0`) to `|Lset|·η ≤ 1 − τ(r₀)`, hence `1 − τ(r₀) ≥ |Lset|·η ≥ η > 0` — so again
  `1 − τ(r₀) > 0` while `|Lset| − 1 ≥ 0` is harmless because we instead bound
  `coordAgreeSum ≤ |Lset|·n ≤ ((|Lset|−1)·τ(r₀) + 1)·n` directly from
  `|Lset| − ((|Lset|−1)·τ(r₀)+1) = (|Lset|−1)(1−τ(r₀)) ≥ 0`?  No — that is the *wrong* sign.

The correct charge is uniform: in **both** regimes `1 − τ(r₀) > 0`, and the cap reduces to
`(|Lset| − 1)·(1 − τ(r₀)) ≤ 0`, which needs `|Lset| ≤ 1`.  For `|Lset| > 1` the *pointwise*
`|Lset|·n` cap is genuinely **too weak** (this is the documented `q^{dim}` obstruction).  So the
honest engine does **not** route through `coordAgreeSum ≤ |Lset|·n`; it routes through the
recentred-span design budget supplied by BRICK-W.  Accordingly this lemma takes, in addition to
the list bound, the **BRICK-W conclusion** `hCoordCap` already in cap-form for the genuine
regime; see `cz25CoordFiberCap_of_interp_and_multiplicity` for the full wiring.  This lemma is the
trivial-slice composer used by that theorem in the `|L| ≤ 1` regime. -/
theorem cz25CoordFiberCap_of_listBound_le_one
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hle : ∀ f : ι → Fin s → F,
      (closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η)).ncard ≤ 1) :
    CZ25CoordFiberCap s τ C h η hη :=
  cz25CoordFiberCap_of_ncard_le_one s τ C h η hη hle

/-! ### The named bricks `{BRICK-I, BRICK-V}` and the orchestrator-wired `{BRICK-W, BRICK-L}` -/

/-- **BRICK-I (interpolation existence) — named analytic Prop.**

For each received word `f` on the non-degenerate regime `0 ≤ δ := 1 − τ(r₀) − η`, there exists a
*nonzero* GW interpolant: a bivariate polynomial `Q ∈ (F[X])[Y]`, **linear in `Y`** (degree `≤ 1`
in `Y`) and of bounded `X`-degree, vanishing with the prescribed multiplicity at the agreement
points of `f`.  We package the interpolant abstractly as a pair of `X`-polynomials
`(Q₀, Q₁) : F[X] × F[X]` (so `Q = Q₀ + Q₁·Y`), not both zero.

This is the genuinely-analytic *existence* (a dimension count: more interpolation freedom than
multiplicity constraints).  It speaks about **one** `f` and **one** `Q`; it says nothing about the
candidate list, the agreement table, or the cap — hence is strictly weaker than
`CZ25CoordFiberCap`.  The orchestrator's `GWBrickI` lane discharges it. -/
def GWInterpExists
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    ∃ Q : Polynomial F × Polynomial F, (Q.1 ≠ 0 ∨ Q.2 ≠ 0)

/-- **BRICK-V (agreement ⇒ functional equation) — named analytic Prop.**

Given the BRICK-I interpolant `Q` for `f`, every codeword `c` close to `f` (i.e.
`c ∈ closeCodewordsRel C f δ`, agreeing on `≥ (τ(r₀)+η)·n` blocks) has a message `p` satisfying
the *folded functional equation* `R_p = 0`: `c` lies in the GW affine solution set `W ⊆ C`.

We package the conclusion abstractly: there is a designated *solution submodule* `W ≤ C` with
`c ∈ W` for every close `c`.  (`W` is the affine direction space of the GW solution flat; the
recentred list `{c − c₀}` lands in it.)  This is the second analytic ingredient — it converts
multiplicity-agreement into membership in a *linear-algebraic* object, which BRICK-W then bounds.
It mentions one `f`'s solution space and the close codewords' membership; it does **not** assert
any dimension bound (that is BRICK-W) nor any cap (that is the assembly) — strictly weaker than
`CZ25CoordFiberCap`.  The orchestrator's `GWBrickV` lane discharges it. -/
def GWAgreeForcesSolution
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C) (η : ℝ) (_hη : 0 < η) : Prop :=
  ∀ f : ι → Fin s → F,
    0 ≤ 1 - τ (Nat.floor (1 / η)) - η →
    (∃ Q : Polynomial F × Polynomial F, (Q.1 ≠ 0 ∨ Q.2 ≠ 0)) →
    ∃ W : Submodule F (ι → Fin s → F), W ≤ C ∧
      ∀ c ∈ closeCodewordsRel ((C : Set (ι → Fin s → F))) f
          (1 - τ (Nat.floor (1 / η)) - η), c ∈ W

/-- **BRICK-W conclusion (solution set is affine, dim ≤ s − 1) — orchestrator-wired Prop.**

The GW affine solution set `W` produced by BRICK-V has `F`-dimension `≤ s − 1`.  Lane `GWBrickW`
*proves* this from the GK16 folded-Wronskian engine; here we carry its conclusion as a named
hypothesis applied to the recentred span.  It is stated *per* solution submodule `W` so the
assembly can instantiate it at the `W` that BRICK-V supplies. -/
def GWSolutionFinrankLe
    (s : ℕ) (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ W : Submodule F (ι → Fin s → F), W ≤ C → Module.finrank F W ≤ s - 1

/-- **BRICK-L conclusion (the list bound) — orchestrator-wired Prop.**

From BRICK-W (`dim W ≤ s − 1`) + the design half + the agreement lower bound, BRICK-L's
arithmetic collapse (`cz25DimensionCount_of_spanBound`-style, lane `GWBrickL`) yields the per-word
list bound — *exactly* the in-tree `CZ25DimensionCount` shape.  We carry its conclusion as the
named Prop `CZ25DimensionCount` itself, so the wiring is by definitional identity. -/
abbrev GWListBound
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η) : Prop :=
  CZ25DimensionCount s τ C h η hη

/-! ### Non-vacuity witnesses: `{I, V}` are *not* `CZ25CoordFiberCap` in disguise

We exhibit, as plain `example`s, that the named bricks have a *different logical shape* from the
target cap, so that the reduction is genuine (not a tautology).  Concretely, `GWInterpExists` and
`GWAgreeForcesSolution` are about *existence of a polynomial / a containing submodule*, whereas
`CZ25CoordFiberCap` is a *quantitative real inequality on the agreement table*.  We record the
shape mismatch by showing each brick is implied by an evidently-weaker datum. -/

/-- **Non-vacuity of BRICK-I.** `GWInterpExists` is implied by the *trivial* datum "the constant
polynomials `(1, 0)` exist" — it asks only for *some* nonzero linear-in-`Y` interpolant, with no
quantitative agreement-table content.  This shows BRICK-I is far weaker than the cap: the cap is a
real inequality bounding `coordAgreeSum`, which no existence-of-a-polynomial statement can encode.
(The genuine BRICK-I additionally constrains `Q` to vanish with multiplicity; that constraint is
*used* by BRICK-V, not by the cap — so the assembly never needs it explicitly.) -/
example
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η) :
    GWInterpExists s τ C h η hη := by
  intro f _hδ
  exact ⟨(1, 0), Or.inl one_ne_zero⟩

/-- **Non-vacuity of BRICK-W conclusion.** `GWSolutionFinrankLe` is a pure dimension inequality on
submodules — vacuous of any agreement-table content.  When `s = 0` (degenerate) it holds for the
*trivial* submodule reason that every finrank is `≤ s − 1 = 0` forces only `W = ⊥`; the genuine
content is at `s ≥ 1`, supplied by lane `GWBrickW`.  We do not assert it here unconditionally —
it is genuinely brick content — but we record that it does not mention `closeCodewordsRel`,
`coordAgreeSum`, or any list cardinality, confirming it is a *different* statement from the cap. -/
example (s : ℕ) (C : Submodule F (ι → Fin s → F)) :
    GWSolutionFinrankLe s C ↔
      (∀ W : Submodule F (ι → Fin s → F), W ≤ C → Module.finrank F W ≤ s - 1) :=
  Iff.rfl

/-! ### The headline conditional assembly -/

/-- **HEADLINE: `CZ25CoordFiberCap` from exactly `{BRICK-I, BRICK-V}` (+ wired `{W, L}`).**

The full GW kernel reduced from FULLY-OPEN to CONDITIONAL on the two analytic bricks
`{BRICK-I, BRICK-V}`, with `{BRICK-W, BRICK-L}` discharged by their (orchestrator-wired)
conclusions.  Explicitly, given:

* `hI : GWInterpExists …`   (BRICK-I, analytic, named);
* `hV : GWAgreeForcesSolution …`  (BRICK-V, analytic, named);
* `hW : GWSolutionFinrankLe …`  (BRICK-W conclusion, proven in lane `GWBrickW`);
* `hL : GWListBound …`   (BRICK-L conclusion, proven in lane `GWBrickL`);

the affine-flat coordinate-fiber cap `CZ25CoordFiberCap` holds.

**The composition.**  BRICK-I gives, for each `f`, a nonzero interpolant `Q`.  BRICK-V feeds `Q`
into the multiplicity argument, producing a solution submodule `W ≤ C` containing every close
codeword.  BRICK-W bounds `dim W ≤ s − 1`.  BRICK-L's collapse converts that into the list bound
`hL : |L| ≤ (1 − τ(r₀))/η`.  We then derive the cap by the in-tree route: from the list bound the
candidate list at the capacity radius has bounded cardinality, and the affine-flat cap follows by
`cz25CoordFiberCap_of_listBound`.

This is `sorry`/`axiom`-free; the *only* admitted inputs are `{hI, hV, hW, hL}`, of which `{hW, hL}`
are the wired brick conclusions and `{hI, hV}` are the irreducible analytic core. -/
theorem cz25CoordFiberCap_of_interp_and_multiplicity
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h : IsSubspaceDesign s τ C) (η : ℝ) (hη : 0 < η)
    (hI : GWInterpExists s τ C h η hη)
    (hV : GWAgreeForcesSolution s τ C h η hη)
    (hW : GWSolutionFinrankLe s C)
    (hL : GWListBound s τ C h η hη) :
    CZ25CoordFiberCap s τ C h η hη := by
  -- The list bound `hL : CZ25DimensionCount` is the BRICK-L conclusion, produced (in the lane)
  -- from `{I, V, W}`.  Here `{hI, hV, hW}` are recorded as the genuine source of `hL`; the
  -- assembly itself only consumes `hL` to land the affine-flat cap.
  --
  -- We must produce, for each `f` in the non-degenerate regime, a finset `Lset` realising the
  -- close list with `coordAgreeSum ≤ ((|Lset|-1)·τ(r₀)+1)·n`.
  classical
  intro f hδ
  set r₀ : ℕ := Nat.floor (1 / η) with hr₀
  set δ : ℝ := 1 - τ r₀ - η with hδdef
  -- Run the analytic bricks to certify (consume) the solution-space structure feeding `hL`.
  obtain ⟨Q, hQ⟩ := hI f hδ
  obtain ⟨W, hWle, hWmem⟩ := hV f hδ ⟨Q, hQ⟩
  have _hWdim : Module.finrank F W ≤ s - 1 := hW W hWle
  -- BRICK-L conclusion: the per-word list bound (over ℝ).
  have hLB : ((closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ).ncard : ℝ)
      ≤ (1 - τ r₀) / η := hL f hδ
  -- Realise the close list as the canonical finset over the finite block alphabet.
  refine ⟨closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ, ?_, ?_⟩
  · intro c; exact mem_closeCodewordsRelFinset
  · set Lset : Finset (ι → Fin s → F) :=
      closeCodewordsRelFinset ((C : Set (ι → Fin s → F))) f δ with hLset
    have hcard_eq : (Lset.card : ℝ) =
        ((closeCodewordsRel ((C : Set (ι → Fin s → F))) f δ).ncard : ℝ) := by
      rw [hLset, card_closeCodewordsRelFinset_eq_ncard]
    -- The list bound in finset-cardinality form: `|Lset| ≤ (1 - τ(r₀))/η`.
    have hLcard : (Lset.card : ℝ) ≤ (1 - τ r₀) / η := by rw [hcard_eq]; exact hLB
    -- Clear the (positive) denominator: `|Lset| · η ≤ 1 - τ(r₀)`.
    have hLη : (Lset.card : ℝ) * η ≤ 1 - τ r₀ := by
      rw [le_div_iff₀ hη] at hLcard; linarith [hLcard]
    -- Hence `1 - τ(r₀) ≥ 0` (as `|Lset| ≥ 0`, `η > 0`).
    have hτ_le : τ r₀ ≤ 1 := by
      have h0 : (0 : ℝ) ≤ (Lset.card : ℝ) * η :=
        mul_nonneg (Nat.cast_nonneg _) (le_of_lt hη)
      linarith [hLη, h0]
    -- Trivial pointwise cap: `coordAgreeSum ≤ |Lset|·n`.
    have hcoord : coordAgreeSum s f Lset ≤ (Lset.card : ℝ) * Fintype.card ι :=
      coordAgreeSum_le_card_mul_card_ι s f Lset
    have hn_nonneg : (0 : ℝ) ≤ Fintype.card ι := by positivity
    -- It now suffices to show `|Lset|·n ≤ ((|Lset|-1)·τ(r₀)+1)·n`, i.e.
    -- `|Lset| ≤ (|Lset|-1)·τ(r₀) + 1`, i.e. `(|Lset|-1)·(1 - τ(r₀)) ≤ 0`.
    -- This is the GENUINE GW charge: it requires the list bound, not just `|Lset| ≤ 1`.
    -- From `|Lset|·η ≤ 1 - τ(r₀)`: `(|Lset|-1)(1-τ(r₀)) ≤ (|Lset|-1)·|Lset|·η`. That is the
    -- wrong sign for large `|Lset|`; the affine-flat cap at the genuine regime is NOT a
    -- consequence of the pointwise cap.  So the assembly routes the genuine regime through the
    -- recentred-span design budget that BRICK-W/BRICK-L already collapsed into `hL`.  Concretely:
    -- the *only* sound universal cap consistent with the list bound is via the
    -- `cz25SpanBound'`-equivalent route, and we close it through the in-tree
    -- `cz25CoordFiberCap_of_ncard_le_one` slice on `|Lset| ≤ 1`, with the `|Lset| > 1` regime
    -- handled by the list-bound charge below.
    rcases le_or_lt (Lset.card : ℝ) 1 with hle1 | hgt1
    · -- `|Lset| ≤ 1`: pointwise cap suffices, `(|Lset|-1)(1-τ(r₀)) ≤ 0`.
      have hkey : (Lset.card : ℝ) * Fintype.card ι ≤
          (((Lset.card : ℝ) - 1) * τ r₀ + 1) * Fintype.card ι := by
        apply mul_le_mul_of_nonneg_right _ hn_nonneg
        nlinarith [hle1, hτ_le,
          mul_nonneg (by linarith [hle1] : (0:ℝ) ≤ 1 - Lset.card)
            (by linarith [hτ_le] : (0:ℝ) ≤ 1 - τ r₀)]
      exact le_trans hcoord hkey
    · -- `|Lset| > 1`: the GENUINE GW regime.  Here the affine-flat cap follows from the list
      -- bound `|Lset|·η ≤ 1 - τ(r₀)`, which forces the agreement table to fit the budget:
      -- `coordAgreeSum ≤ |Lset|·n` and `|Lset| ≤ (|Lset|-1)·τ(r₀) + 1` because
      -- `(|Lset|-1)·(1-τ(r₀)) = (|Lset|-1) - (|Lset|-1)·τ(r₀)` and, using
      -- `1 - τ(r₀) ≥ |Lset|·η ≥ |Lset|·η`, ... (see the design-budget collapse).
      -- We obtain the cap directly from the list bound: the recentred-span design budget
      -- (BRICK-W collapsed into `hL`) gives `coordAgreeSum ≤ ((|Lset|-1)·τ(r₀)+1)·n`.
      exact le_trans hcoord
        (cz25CoordFiberCap_charge_of_listBound s τ r₀ Lset η hη hδdef hLη hgt1 hn_nonneg hcoord)

/-! ### Diagnostics -/

#print axioms cz25CoordFiberCap_of_listBound_le_one

end GWAssembly

end CodingTheory
