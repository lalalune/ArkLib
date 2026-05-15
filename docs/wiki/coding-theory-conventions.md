# CodingTheory naming and convention guide

Local conventions used in `ArkLib/Data/CodingTheory/` and its subdirectories.
These are not enforced by tooling but they are followed consistently across the
ABF26 statement layer (`ProximityGap/Errors.lean`,
`ProximityGap/CapacityBounds.lean`, `ListDecoding/Bounds.lean`,
`Connections/*`, `JohnsonBound/Family.lean`, etc.) and reviewers should look
for them.

## Theorem naming

Statement-level theorems that bound an ε-error or list-size for a specific code
family follow the pattern:

```
<codeFamily>_<quantity>_<regime>_<authors><year>
```

Examples:

| Lean name | Reads as |
|---|---|
| `linear_epsCA_1_5_johnson_bgks20` | linear-code `ε_ca` bound in the 1.5-Johnson regime, from BGKS20 |
| `rs_epsMCA_johnson_range_bchks25` | Reed-Solomon `ε_mca` bound in the Johnson range, from BCHKS25 |
| `rs_epsCA_breakdown_cs25` | Reed-Solomon `ε_ca` breakdown bound, from CS25 |
| `linear_lambda_ge_elias_volume_eli57` | linear-code list-size lower bound from Elias volume bound |
| `rs_lambda_high_rate_jh01` | Reed-Solomon list-size bound in the high-rate regime, from JH01 |

Slots:

- **`<codeFamily>`** — `linear`, `rs`, `frs`, `irs`, `subspaceDesign`, `mds`, etc.
- **`<quantity>`** — `epsCA`, `epsMCA`, `epsPG`, `lambda` (list size), `dim`,
  `johnson_bound`.
- **`<regime>`** — e.g. `unique_decoding`, `johnson_range`, `capacity`,
  `breakdown`, `lower_capacity`. Skip when there's no regime distinction.
- **`<authors><year>`** — lowercase author initials + 2-digit year (`bchks25`,
  `gg25`, `eli57`). For two-paper joint citations: `bchks25_kk25`.

The pattern keeps names searchable, indicates the source paper at a glance, and
disambiguates the same quantity bounded under different regimes (e.g.
`rs_epsCA_breakdown_cs25` vs `rs_epsCA_bchks25_item2`).

## Definition naming

| Kind | Convention | Examples |
|---|---|---|
| Paper-named function | Lean-id close to paper notation | `qEntropy`, `Jqℓ`, `Jcap`, `epsCA`, `epsMCA`, `Lambda`, `Lambda_at` |
| Descriptive function | snake_case describing the math | `restrictedRelHammingDist`, `hammingBallVolume`, `frsEvalOnPoints` |
| Predicate / property | `IsX` style | `IsMDS`, `IsSubspaceDesign`, `IsFAdditive`, `LineDecodable`, `Admissible` |
| Structure | PascalCase | `ExtensionFieldPresentation`, `WordStack`, `InterleavedWord` |
| Code family | namespaced + `Code` suffix | `ReedSolomon.code`, `ReedSolomon.Folded.frsCode`, `ReedSolomon.Interleaved.irsCode` |

## Notation

Globally declared (inside `namespace Code`, visible everywhere):

- `Δ₀(u, v)` — `hammingDist u v` (absolute Hamming distance).
- `Δ₀(u, C)` — `distFromCode u C` (absolute distance to a code).
- `‖C‖₀` — `Code.minDist C` (absolute minimum distance).
- `δᵣ(u, v)` — `relHammingDist u v` (relative Hamming distance, `ℚ≥0`-valued).
- `δᵣ(u, C)` — `relDistFromCode u C` (relative distance to a code, `ENNReal`-valued).
- `Λ(C, δ, f)` — `Lambda_at C δ f` (codewords within radius `δ` of `f`).
- `Λ(C, δ)` — `Lambda C δ` (block-maximised list size, `ℕ∞`-valued).

Scoped:

- `^⋈ κ` — `CodeInterleavable.interleaveCode _ κ` (interleaved code).
- `ρ C` — `LinearCode.rate C` (rate, `ℚ≥0`-valued). Use the `&` form so `ρ` can
  also be used as a local variable name.

The paper's `RS[F, L, k]`, `IRS[F, L, k, s]`, `FRS[F, L, k, s, ω]`,
`UM[F, L, k, s]` shortcuts are *not* introduced as Lean notation. Per design
decision (polish-plan D2): descriptive names like `ReedSolomon.code`,
`ReedSolomon.Folded.frsCode` are preferred for navigability. Revisit if a
downstream proof becomes hard to read because of this choice.

## Type conventions

| Quantity | Type | Where it shows up |
|---|---|---|
| Hamming distance (absolute) | `ℕ` | `Code.minDist`, `hammingDist` |
| Distance to code (absolute, may be `⊤`) | `ℕ∞` | `Code.distFromCode` |
| Relative Hamming distance | `ℚ≥0` | `relHammingDist`, `δᵣ(u, v)` |
| Relative distance to code | `ENNReal` | `relDistFromCode`, `δᵣ(u, C)` |
| Restricted relative Hamming distance | `ℝ≥0` | `restrictedRelHammingDist` |
| Code rate | `ℚ≥0` | `LinearCode.rate` |
| Proximity radius `δ` argument | `ℝ≥0` (preferred) or `ℝ` | `epsCA`, `epsMCA`, `Lambda` |
| Paper-style real-valued bounds | `ℝ` (then wrapped) | RHS of capacity-bound theorems |
| ε-errors (`ε_pg`, `ε_ca`, `ε_mca`) | `ENNReal` | `epsCA`, `epsMCA`, `epsPG` |
| Probabilities | `ENNReal` | `Pr_{...}[...]` notation |
| List sizes | `ℕ∞` (then cast to `ENNReal` for bounds) | `Lambda` |
| Polynomial degree-bound | `Polynomial.degreeLT F k : Submodule F F[X]` | `ReedSolomon.code`, `Folded.frsCode` |
| Linear code carrier | `Submodule F (ι → A) = ModuleCode ι F A` | `ReedSolomon.code`, `Interleaved.irsCode`, `Folded.frsCode` |
| Non-linear code carrier | `Set (ι → A) = Code ι A` | `extensionCode`, theorems over arbitrary alphabets |

### Coercion conventions

- `ENNReal.ofReal x` when the source `x : ℝ` may be negative (truncates to 0).
  Used for the RHS of capacity-bound theorems.
- Direct cast `(x : ENNReal)` when the source `x : ℝ≥0` / `ℕ` is non-negative.
- `x.toNNReal` for `ℝ → ℝ≥0` conversions; each call site should be either
  provably non-negative under hypotheses or intentionally aligned with the
  paper's stated regime (so truncation matches a vacuous case).
- `Real.rpow x y` for non-integer real exponents; `^` desugars to this when
  both base and exponent are `ℝ`.

## Tagged sorry comments

External-admit theorems use the canonical comment shape:

```
sorry -- ABF26-X.Y; <classification> [Citation].
```

- `<classification>` ∈ `{external admit, bridge, derived, in-tree admit}`.
- `[Citation]` matches the paper-bibliography key (`[GG25 Cor 4.9]`,
  `[BCHKS25 Thm 1.3]`, etc.). For derived items, the antecedent IDs
  (`derived from R4.2 + T4.9.2`).

Every tagged sorry maps 1-to-1 to a row in
[`../kb/audits/open-problems-list-decoding-and-correlated-agreement.md`](../kb/audits/open-problems-list-decoding-and-correlated-agreement.md).
Reviewers should expect the `ABF26-X.Y` tag in the comment to match an audit-doc
row.

## File and namespace layout (target after Phase 2 of the integration plan)

See [`../../ABF26_INTEGRATION_PLAN.md`](../../ABF26_INTEGRATION_PLAN.md) §3 for
the full proposed tree. Briefly:

- `CodingTheory.*` for non-RS-specific definitions and predicates
  (`qEntropy`, `IsSubspaceDesign`, `IsMDS`, `LineDecodable`,
  `ExtensionFieldPresentation`, `extensionCode`).
- `ReedSolomon.*` for RS variants and sub-namespaces
  (`ReedSolomon.Interleaved.irsCode`, `ReedSolomon.Folded.frsCode`,
  `ReedSolomon.Folded.Admissible`, `ReedSolomon.Multiplicity.umCode`).
- `ProximityGap.*` for ε-errors, grand challenges, and predicate-style
  proximity material.

Theorems (admitted external results) stay in `CodingTheory.*` where they
operate on general codes, `ReedSolomon.*` where RS-specific, or
`ProximityGap.*` where they bound an `ε`-error.
