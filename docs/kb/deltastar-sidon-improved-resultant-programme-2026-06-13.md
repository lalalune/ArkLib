# δ* KB — The Parseval-Sharpened Small-Subgroup Sidon Programme (2026-06-13)

Distilled record of a complete, axiom-clean, in-tree programme that de-vacuates and then sharpens
the small-subgroup Sidon route of #389. **Honest scope up front:** this is the energy/Sidon/resultant
cone. It is *provably the wrong lever for the δ\* prize* — see "Boundary" below — but it is a
complete, novel, deployed, quantified result in its own regime, and the machinery (general DFT
Parseval, AM-GM product bound, F_p↔ℂ distinctness transfer) is reusable.

## The vacuity that started it

The committed `SidonLiftClosed.prime_le_of_parallelogram` / `resultant_fourTerm_ne_zero` were gated on
`hne : ∀ ζ:ℂ, ζ^n=1 → ζ^i+ζ^j−ζ^k−ζ^l ≠ 0`. **Unsatisfiable** (at ζ=1: `1+1−1−1=0`), so those
theorems were axiom-clean but *vacuous as bricks*. Recorded as `allRoots_hne_false`. Lesson: an
axiom-clean `#print axioms` does NOT certify usability — instantiate the hypotheses (here at ζ=1).
The resultant `Res(Φ_n,f)=∏_{ζ prim}f(ζ)` only needs the *primitive*-root condition, which IS
satisfiable. (A sibling independently de-vacuated `SidonLiftClosed` in place.)

## The files (all axiom-clean: propext, Classical.choice, Quot.sound; on fork/main)

| file | content |
|---|---|
| `SidonLiftDevacuated` | `resultant_fourTerm_ne_zero'`, `fourTerm_natDegree_map` (discharges `hfdeg`: \|leadcoeff\|≤2<p), `prime_le_of_parallelogram'`, the field-independent exponent bridge (`primitiveRoot_pow_eq_iff`/`_pow_half`/`_sum_eq_zero_iff`), `sidonModNeg_rootsOfUnity`, `rootsOfUnity_additiveEnergy_eq_sidon` (E=3n²−3n for p>2ⁿ) |
| `SidonGVClosure` | GV supply wall closes (`gvRepBound_rootsOfUnity`), sharp `repCount_le_two_of_sidonModNeg` → `GVRepBound(μ_n) 2` |
| `SidonGaussSum4thMoment` | `∑_b‖η_b‖⁴ = q·(3n²−3n)` (character-sum kernel pinned) |
| `SidonParsevalBound` | **`parseval_fourTerm`** (DFT 2nd moment) + **`prod_le_of_sum_le`** (AM-GM `∏xᵢ≤Bᵏ` from `∑xᵢ≤k·B`) |
| `SidonParsevalGeneral` | **`parseval_general`**: `∑ₜ‖∑ₐsₐvₐᵗ‖² = n·∑ₐ‖sₐ‖²` for distinct unit roots, ANY complex coeffs |
| `SidonParsevalNthRoots` | Parseval over `nthRootsFinset` (the resultant's domain) |
| `SidonResultantImproved` | **`abs_resultant_fourTerm_sq_le`: `\|Res\|² ≤ 8^{φ(n)}` (= 2^{3n/4})**, S=4 case |
| `SidonDoubledBound` | `abs_resultant_doubled_sq_le`: `\|Res\|² ≤ 12^{φ(n)}`, S=6 (doubled `2X^i−X^k−X^l`) case |
| `SidonThresholdImproved` / `SidonDoubledThreshold` | `prime_sq_le_of_parallelogram` (p²≤8^{φ}), `prime_sq_le_doubled` (p²≤12^{φ}) |
| `SidonInjTransfer` | `pow_inj_transfer` (F_p↔ℂ distinctness), `inj3`/`inj4` (matrix injectivity from pairwise ≠) |
| `SidonModNegImproved` | **CAPSTONE `sidonModNeg_rootsOfUnity_improved`**: μ_n Sidon-mod-neg for p>12^{n/4}; `improved_threshold_strict` (12^{φ}<4ⁿ); `rootsOfUnity_additiveEnergy_eq_improved` (E=3n²−3n at p>12^{n/4}) |

## The mathematical core

The committed `|Res(Φ_n,fourTerm)| ≤ 4^{φ(n)} = 2^n` uses the **pointwise** `‖f(ζ)‖ ≤ 4`. Probe
(`probe_resultant_bound`) shows the true `max|Res|` over genuine four-terms is `(2S)^{φ(n)/2}` with
`S=∑|coeff|²∈{4,6}` — TIGHT at `2^{3n/4}` for S=4. Replace pointwise by the **ℓ² (Parseval) average**:
`∑_{ζ:ζ^n=1}‖f(ζ)‖² = n·S` (off-diagonals cancel by root-of-unity orthogonality), restrict to the
`φ(n)=n/2` primitive roots, AM-GM ⟹ `|Res|² = ∏_{prim}‖f(ζ)‖² ≤ (2S)^{φ(n)}`. So `p>(2S)^{n/4}`
forbids the parallelogram. The full SidonModNeg case-splits genuine coincidences into S=4 (all
distinct) and S=6 (doubled, `j=i` or `k=l`); worst case S=6 ⟹ **threshold `p>12^{n/4}≈2^{0.896n}`**,
a 33%-larger unconditional Sidon regime than the committed `p>2ⁿ`.

## The energy-extremality characterization (added 2026-06-13)

Three more axiom-clean files complete the additive-energy theory of the negation-closed `G ∌ 0`
(char `≠ 2`) into a self-contained **triple equivalence** (the char-0 minimal energy is attained
exactly at the Sidon-modulo-negation sets):

> **`E(G) = 3|G|² − 3|G|   ↔   SidonModNeg G   ↔   ∀ c ≠ 0, repCount G c ≤ 2`**

| file | content |
|---|---|
| `AdditiveEnergyLowerBound` | **`additiveEnergy_ge`**: `E(G) ≥ 3|G|² − 3|G|` for *every* negation-closed `G` (the trivial pair-match + zero-sum coincidences alone force it) — the matching lower bound to the existing Sidon equality. Helpers `structuredInner_eq` (structural inner sum `= 3|G|−3`, unconditional) + `repCount_ge_structured` (each pair `{a,b}` always represents `a+b`). |
| `AdditiveEnergyCharacterization` | **`sidonModNeg_of_additiveEnergy_eq`** (energy-minimal ⟹ Sidon: equality in the lower bound forces, pointwise via `Finset.sum_eq_sum_iff_of_le`, exactly the two trivial reps) + **`additiveEnergy_eq_iff_sidonModNeg`** (the first `↔`). |
| `SidonRepCountCharacterization` | **`sidonModNeg_of_repCount_le_two`** (a genuine coincidence `a+b=c+d` yields a *third* distinct rep of `a+b`, `card_eq_three` on `{a,b,c}`/`{a,c,d}`) + **`sidonModNeg_iff_repCount_le_two`** (the second `↔`). |

These sharpen the picture but live in the **same energy/Sidon cone** — still the wrong lever for δ*
(see Boundary).  Reusable: `additiveEnergy_ge` is a clean "Sidon is the minimum energy" bound usable
wherever a negation-closed additive-energy lower bound is needed.

## Boundary — why this is NOT the δ* prize, and what is

- **Regime:** Sidon holds only for `n < (4/3)·log₂p / log₂12·… ≈ 1.12·log₂p` (small subgroups). At
  the prize NTT length `n~2^20` and `p~2^128`, `12^{n/4}` is astronomically beyond `p`, so μ_n is
  NOT Sidon — `E=n^{2+o(1)}` is the recognized-OPEN large-`n` additive-energy conjecture (best known
  Shkredov n^{2.44}).
- **Fatal coupling:** even a perfect energy bound feeds the *supply*, not the *line-incidence* that
  δ* is `sup{δ: max-line-incidence ≤ q·ε*}`. The supply→incidence bridge loses a √ (even `E=n²` gives
  list `n^{3/2}` = sub-Johnson, NOT capacity). Confirmed independently in
  `memory issue389-additive-energy-crux`.
- **The actual prize route** is the GG25 **curve-decodability** lane (`CurveDecodability`,
  `GG25MCAFromCurveDecodability` Thm 3.3 = curve-decodability⟹MCA, already complete in-tree). Its
  open input — curve-decodability for explicit constant-rate RS (GG25 §4.3) — IS the recognized open
  core (actively built by a sibling). The δ* prize stays open until past-Johnson literature for
  explicit codes lands.

## Reusable lemmas (beyond #389)

`parseval_general` (general finite DFT Parseval over roots of unity), `prod_le_of_sum_le` (uniform
AM-GM product bound), `pow_inj_transfer`/`inj3`/`inj4` (root-of-unity distinctness machinery),
`primitiveRoot_pow_eq_iff`/`_sum_eq_zero_iff` (field-independent exponent congruences). All
axiom-clean, all general.

Lean gotchas logged in `memory issue389-sidon-devacuation`.
