/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.JohnsonBound.Basic
import ArkLib.Data.CodingTheory.ListDecodability

/-!
# ABF26 §3.1 — Johnson family `J_{q,ℓ}, J_q, J` and Theorem 3.2 / Corollary 3.3

Extensions to `JohnsonBound/Basic.lean` matching the paper-shaped statements from
ABF26 §3.1 (Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated
Agreement*, 2026).

The existing `JohnsonBound.J q δ : ℝ` matches the paper's `J_q(δ)`. This file adds:

- `JohnsonBound.Jqℓ q ℓ δ` — paper's `J_{q,ℓ}(δ)`, with the additional `ℓ/(ℓ-1)` factor
  inside the square root.
- `JohnsonBound.Jcap δ` — paper's asymptotic Johnson bound `J(δ) := 1 - √(1 - δ)`.

The three are related by `J_{q,ℓ}(δ) →_{ℓ → ∞} J_q(δ) →_{q → ∞} J(δ)`; we state the
limit relationships in docstrings but do not formalise the limits (the paper does
not prove them either).

The file also states the paper-shaped versions of:

- `johnson_bound_lambda_le_ell` — ABF26 Theorem 3.2 [Joh62]:
  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`.
- `mds_johnson_lambda_le` — ABF26 Corollary 3.3:
  for any MDS code `C` of rate `ρ` and `η > 0`, `|Λ(C, 1 - √ρ - η)| ≤ 1/(2·η·ρ)`.

Both are admitted as external results (T3.2 has an existing in-tree proof via
`johnson_bound` / `johnson_bound_alphabet_free` in `JohnsonBound/Basic.lean` that
needs porting from the absolute-distance form to ABF26's `Lambda` form; C3.3
follows from L2.6 + T3.2, but uses the asymptotic Johnson radius which crosses
ArkLib's existing rate/distance bridge).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Joh62] Johnson. (Original Johnson bound paper.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace JohnsonBound

open Real

/-- **ABF26 Definition 3.1, `J_{q,ℓ}`.** Paper's q-ary ℓ-radius Johnson function:

  `J_{q,ℓ}(δ) := (1 - 1/q) · (1 - √(1 - q/(q-1) · ℓ/(ℓ-1) · δ))`

For `ℓ = 2` this is the binary Johnson radius; as `ℓ → ∞`, `Jqℓ q ℓ δ → J q δ`
(the existing `JohnsonBound.J`). The `ℓ` parameter is the target list size. -/
noncomputable def Jqℓ (q ℓ : ℚ) (δ : ℚ) : ℝ :=
  let frac : ℚ := q / (q - 1)
  let lFac : ℚ := ℓ / (ℓ - 1)
  ((1 - 1 / q) : ℚ) * (1 - √(1 - frac * lFac * δ))

/-- **ABF26 Definition 3.1, `J`.** Paper's asymptotic Johnson bound:

  `J(δ) := 1 - √(1 - δ)`

Equals the `q → ∞` limit of `J_q(δ)` and the `q, ℓ → ∞` limit of `J_{q,ℓ}(δ)`.
This is also the binary Johnson bound (q = 2, ℓ → ∞).

Distinct from the existing `JohnsonBound.J q δ`, which is the paper's `J_q(δ)`
(the q-ary limit, parametrised by `q`). To avoid renaming the existing `J`, we
name this `Jcap` (Johnson — *cap*acity). -/
noncomputable def Jcap (δ : ℝ) : ℝ := 1 - √(1 - δ)

@[simp]
lemma Jcap_zero : Jcap 0 = 0 := by simp [Jcap]

@[simp]
lemma Jcap_one : Jcap 1 = 1 := by simp [Jcap]

end JohnsonBound

namespace CodingTheory

open scoped NNReal
open ListDecodable JohnsonBound

/-- **ABF26 Theorem 3.2 [Joh62].** Johnson bound on list size. For any code
`C ⊆ Σ^n` with `|Σ| = q`,

  `|Λ(C, J_{q,ℓ}(δ_min(C)))| ≤ ℓ`

where `δ_min(C) = minDist(C) / n` is the relative minimum distance and `J_{q,ℓ}`
is the paper's q-ary ℓ-radius Johnson function. **Admitted (tagged sorry).**

**Why the in-tree `johnson_bound` does NOT reach this radius (verified, 2026-06-04).**
A prior triage suggested "plug `e/n = J_{q,ℓ}` into the in-tree `johnson_bound`; its
`JohnsonConditionStrong` then fails at the boundary, forcing `|Λ| ≤ ℓ`". This was
re-checked symbolically and is **incorrect** — there is a factor inversion that makes
the in-tree bound land at a *strictly smaller* radius. The exact computation:

Write `frac = q/(q-1)`, `t = frac·δ_min`, `L = ℓ/(ℓ-1) > 1`. The boundary identity for
`Jqℓ` is `(1 - frac·Jqℓ)² = 1 - frac·L·δ_min = 1 - L·t`. The packaged bound
[`johnson_bound`](Basic.lean) gives `B.card ≤ (frac·d/n)/Denom` with
`Denom = (1 - frac·e/n)² - (1 - frac·d/n)`. Setting `e/n = Jqℓ`, `d/n = δ_min`:
`Denom = (1 - L·t) - (1 - t) = t·(1 - L) = -t/(ℓ-1) < 0`. So `JohnsonConditionStrong`
(`Denom > 0`) is *false* and the bound is unusable — but the failure does **not** force
`|Λ| ≤ ℓ`: the raw [`johnson_bound_lemma`](Lemmas.lean), which holds unconditionally
(`n>0`, `|B|≥2`, `|F|≥2`), reads `B.card · Denom ≤ frac·d/n`, and with `Denom < 0` this
is a *negative lower* bound on `B.card` — vacuous as an upper bound.

Inverting the packaging the other way: `johnson_bound` yields `B.card ≤ ℓ` exactly when
`Denom ≥ (frac·d/n)/ℓ = t/ℓ`, i.e. `(1 - frac·e/n)² ≥ 1 - t·(ℓ-1)/ℓ = 1 - t/L`, i.e.
`e/n ≤ (1/frac)·(1 - √(1 - frac·δ_min/L))`. That radius uses the factor `1/L = (ℓ-1)/ℓ`,
the **reciprocal** of the `L = ℓ/(ℓ-1)` factor inside `Jqℓ`. Since `L > 1`, the in-tree
radius is strictly *smaller* than the paper's `Jqℓ`. The paper's larger (tight) list-of-ℓ
radius is the Plotkin-refined Johnson radius and is not reachable from the second-moment
`johnson_bound` alone.

**Exact missing ingredient (corrected, 2026-06-05).** A prior note claimed the q-ary
Plotkin average-distance upper bound `d(B') ≤ frac·n·M/(M-1)` (`frac = q/(q-1)`),
combined with `johnson_bound_lemma`, discharges T3.2 at `Jqℓ`. **This is FALSE and is
recorded here with a countermodel.** Writing `E = e(B')/n`, `D = d(B')/n`, `M = |B'|`,
the in-tree second-moment inequality (IT) `M·((1 - frac·E)² - 1 + frac·D) ≤ frac·D`
(this is `johnson_bound_lemma`/`johnson_bound₀`, proven to be *exactly* equivalent to
`johnson_unrefined`, so the tree has no hidden sharpness) together with Plotkin
`D ≤ (1/frac)·M/(M-1)` is satisfiable for `M` far above `ℓ`. Concrete countermodel:
`q = 2, ℓ = 4, δ_min = 0.3`, so `Jqℓ(δ_min) ≈ 0.2764`; the point `M = 9, E ≈ 0.1597,
D = 0.3` satisfies (IT) (`0.568 ≤ 0.600`) and Plotkin (`0.3 ≤ 0.5625`), yet the paper
bound is `ℓ = 4`. Hence Plotkin is *necessary but not sufficient*.

The deeper reason: the in-tree apparatus is the **averaging** Johnson bound — its
convexity step (`le_sum_choose_K`, `k_choose_2`) averages over coordinates and bounds
the *average* pairwise distance `d(B')`, then relaxes `d(B') ≥ δ_min·n`. The genuine
`Jqℓ` bound is strictly sharper than ANY bound obtained by this average→min relaxation:
running the averaging Gram argument `M·s² ≤ 1 + (M-1)·b` (`s = 1 - frac·E`,
`b = 1 - frac·δ_min`) to a contradiction at `M = ℓ+1` yields the radius with sqrt-factor
`ℓ/(ℓ+1)`, whereas `Jqℓ` carries the factor `ℓ/(ℓ-1)`; the ratio `(ℓ+1)/(ℓ-1) > 1` is
the irreducible gap (the in-tree-reachable radius is `< Jq(δ_min) < Jqℓ(δ_min)`).
Moreover the pure real Gram matrix of `M` correlation vectors at the `Jqℓ` radius stays
positive-semidefinite for ALL `M` (numerically verified): the bound is *not* a geometric
fact about real inner products — it relies on the q-ary integrality of the column counts
`K_i(α) ∈ ℕ`, `∑_α K_i(α) = M`, in a way the in-tree second-moment chain discards when it
passes to the average. Closing T3.2 at `Jqℓ` therefore requires the full discrete
ℓ-Johnson development ([Joh62]; Guruswami thesis Thm 3.1; MacWilliams–Sloane Ch. 17),
which is a genuine ground-up formalization, not a ~200-line dual of `almost_johnson`.
See `research/proximity-prize/dispositions/pc-w1-T3.2-johnson.md` for the full analysis.

**Two further mechanical gaps** (independent of the math wall above):
- *Alphabet*: this statement is over a bare alphabet `α` (`Fintype + DecidableEq`, no
  `Field`), but every in-tree Johnson lemma — including `johnson_bound_alphabet_free` —
  carries `[Field F]`. Either redo the column-count core over `DecidableEq α`, or weaken
  this statement to `[Field α]`.
- *Index type*: the in-tree apparatus (`e B v`, `d B`, the ball) is over `Fin n → F`;
  this statement is over `ι → α`. A `Fintype.equivFin ι` transport of `hammingDist`/`e`/`d`
  is needed (mechanical but not free).

Tracked in `docs/kb/ABF26_PLAN.md` and the audit log.

**Alphabet generality.** Stated over an arbitrary alphabet `α` (not necessarily a
field), matching the paper's `Σ`. The Johnson bound is a purely combinatorial fact
about Hamming distance — it does not need field structure. -/
theorem johnson_bound_lambda_le_ell
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {α : Type} [Fintype α] [DecidableEq α]
    (C : Set (ι → α)) (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) :
    let q : ℚ := Fintype.card α
    let δ_min : ℚ := Code.minDist C / Fintype.card ι
    Lambda C (Jqℓ q ℓ δ_min) ≤ (ℓ : ℕ∞) := by
  -- ABF26-T3.2; external admit. WALL: the in-tree (averaging) Johnson apparatus is
  -- PROVABLY insufficient at the `Jqℓ` radius, and the gap is NOT closed by adding the
  -- q-ary Plotkin bound (countermodel in the docstring). Routes attempted:
  --
  -- SKELETON 1 (direct `johnson_bound`).  Apply `johnson_bound` to the transported ball.
  --   BLOCKED: at `e/n = Jqℓ`, `Denom = (1-frac·e/n)² - (1-frac·δ_min) = frac·δ_min·(1-L)
  --   = -frac·δ_min/(ℓ-1) < 0`, so `JohnsonConditionStrong` is false (factor inversion).
  --   The same sign holds whether the `d`-slot is the average OR the minimum distance.
  --
  -- SKELETON 2 (raw `johnson_bound_lemma` + Plotkin).  From `johnson_bound_lemma`:
  --   `M·Denom ≤ frac·d_avg/n` (unconditional); add q-ary Plotkin `d_avg/n ≤ (1/frac)·M/(M-1)`.
  --   BLOCKED — and this is the corrected verdict: even WITH Plotkin proven, the system is
  --   satisfiable for `M ≫ ℓ`. Countermodel `q=2, ℓ=4, δ_min=0.3` (Jqℓ ≈ 0.2764):
  --   `M=9, e/n≈0.16, d_avg/n=0.3` meets both (IT) and Plotkin. Plotkin is necessary-not-
  --   sufficient. (The Plotkin sub-lemma `∑_α K_i(α)² ≥ M²/q` IS in-tree-provable via
  --   mathlib `Finset.sq_sum_le_card_mul_sum_sq`, but it does not unlock T3.2.)
  --
  -- SKELETON 3 (`johnson_bound_alphabet_free` ⇒ `q·d·n`).  BLOCKED twice: the bound `q·d·n`
  --   is the coarse alphabet-free form (≫ ℓ), and its radius is the `J_q` (ℓ→∞) radius.
  --
  -- SKELETON 4 (Lambda_mono to the in-tree-reachable radius).  The averaging Gram bound
  --   `M·s² ≤ 1+(M-1)·b` (s=1-frac·e/n, b=1-frac·δ_min), pushed to `M=ℓ+1`, gives `|Λ|≤ℓ`
  --   only at the radius with sqrt-factor `ℓ/(ℓ+1)`; `Jqℓ` carries `ℓ/(ℓ-1)`.  Ratio
  --   `(ℓ+1)/(ℓ-1) > 1`: the reachable radius `R₀ < Jq(δ_min) < Jqℓ(δ_min)`, so `Lambda_mono`
  --   runs the WRONG way (would only give `|Λ(C,Jqℓ)| ≥ |Λ(C,R₀)|`).
  --
  -- Root cause: the genuine `Jqℓ` bound is strictly sharper than any average→min relaxation
  -- and relies on the q-ary integrality of the column counts `K_i(α) ∈ ℕ` (the real Gram
  -- matrix at the `Jqℓ` radius is PSD for all M — verified). Closing T3.2 needs the full
  -- discrete ℓ-Johnson development ([Joh62]). REDUCED to that external lemma; tagged sorry.
  sorry

/-- **ABF26 Corollary 3.3.** MDS coarse Johnson corollary. For every MDS code `C` with
rate `ρ := dim C / n` and `η > 0`:

  `|Λ(C, 1 - √ρ - η)| ≤ 1 / (2 · η · ρ)`

Derives from L2.6 (Singleton bound: MDS implies `δ_min = 1 - ρ + 1/n`, available via
the `IsMDS_iff_rate_distance` bridge) plus T3.2 (or its asymptotic version via `Jcap`).
Admitted as an external result; the path to a machine-checked proof requires the
asymptotic-Johnson form `Lambda C δ ≤ 1/(2·(Jcap δ - δ))` plus MDS rate-distance
manipulation.

**Rate derivation.** `ρ` is bound inline as `(Module.finrank F C : ℝ) / Fintype.card ι`
rather than passed as a separate parameter — this matches the upstream `IsMDS`
signature (additive Nat form, no rate parameter) and lets call sites use
`IsMDS_iff_rate_distance` to extract the rate-distance equation when needed. -/
theorem mds_johnson_lambda_le
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (C : LinearCode ι F) (η : ℝ) (_hη_pos : 0 < η)
    (_h_mds : LinearCode.IsMDS C) :
    let ρ : ℝ := (Module.finrank F C : ℝ) / Fintype.card ι
    (Lambda ((C : Set (ι → F))) (1 - Real.sqrt ρ - η) : ENNReal) ≤
      ENNReal.ofReal (1 / (2 * η * ρ)) := by
  -- ABF26-C3.3; external admit. Reduction chain (each step verified to exist in-tree):
  --   1. `IsMDS_iff_rate_distance` (Basic/LinearCode.lean) ⇒ for an MDS code,
  --      `δ_min = 1 - ρ + 1/n`, hence `Jcap δ_min = 1 - √ρ + O(1/n)` matches the
  --      `1 - √ρ - η` radius once `η` absorbs the `1/n` correction.
  --   2. The asymptotic (q,ℓ → ∞) `Jcap` form of T3.2: `Lambda C δ ≤ 1/(2·(Jcap δ - δ))`.
  -- BLOCKED: step 2 IS T3.2 in its asymptotic specialisation, so C3.3 RIDES ENTIRELY on
  -- T3.2 and inherits its wall (see `johnson_bound_lambda_le_ell`: the in-tree averaging
  -- Johnson apparatus is provably short of `Jqℓ`, and Plotkin does not close the gap —
  -- the discrete ℓ-Johnson bound [Joh62] is required). There is NO additional MDS-specific
  -- obstruction: once T3.2 lands at `Jqℓ`/`Jcap`, C3.3 is pure algebra on the Singleton
  -- equation (`IsMDS_iff_rate_distance` confirmed present). REDUCED to T3.2; tagged sorry.
  sorry

end CodingTheory
