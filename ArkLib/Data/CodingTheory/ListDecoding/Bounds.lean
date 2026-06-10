/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecoding.Bounds.General
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.RandomAndReedSolomon
import ArkLib.Data.CodingTheory.ListDecoding.Bounds.SubspaceDesign

/-!
# List-decoding bounds from ABF26 §3

External *proposition statements* for the §3 list-decoding bounds from ABF26
(Arnon-Boneh-Fenzi, *Open Problems in List Decoding and Correlated Agreement*, 2026).
The external-paper results are recorded as named `Prop` definitions, not as proved
theorems, so downstream developments must take them as explicit hypotheses until the
paper proofs are formalized. The statements use the
`ListDecodable.Lambda` function (block-maximised list size) introduced in
`ListDecodability.lean`, plus `qEntropy` from `Basic/Entropy.lean` and
`hammingBallVolume` from `HammingBallVolume.lean`.

These bounds sit immediately above the Grand List Decoding Challenge in ABF26 §1:
upper bounds (T3.2, C3.3) give candidate witnesses `δ_C*` for `|Λ(C^≡m, δ_C*)| ≤ ε*·|F|`,
while lower bounds (L3.7, C3.8, T3.9–T3.14) rule out witnesses above a threshold.

## Quantification conventions

The §3.2 / §3.2 RS theorems quantify over "infinitely many `q`", existentially-bound
codes, and "sufficiently large `n`". We capture these uniformly as follows:

- *Type-level data* (alphabet `F`, index type `ι`) is **universally** quantified at the
  theorem's outermost binder. The user instantiates at the call site.
- *Numeric quantifiers* ("there exists `α > 0`", "there exists `γ > 0`",
  "for infinitely many `q`") stay inside the theorem body using `∃` on numeric data.
- *Sufficiently large `n`* is captured as an explicit existential threshold `n₀ : ℕ`
  followed by `n₀ ≤ Fintype.card ι`. This matches Mathlib's `Filter.eventually`
  shape without dragging filters into a pure statement.
- *Infinitely many `q`* is captured as `∃ qs : ℕ → ℕ, StrictMono qs ∧ ∀ i, P (qs i)`.

## Main statements (external admits)

### Lower bounds — general codes (§3.2)

- `linear_lambda_ge_elias_volume_eli57` — ABF26 L3.7 [Eli57]: `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^{n-k}`.
- `linear_lambda_ge_entropy_volume` — ABF26 C3.8: `|Λ(C, δ)| ≥ q^{n(ρ-1+H_q(δ))} / √(8nδ(1-δ))`.
- `linear_C_le_generalized_singleton_st20` — ABF26 T3.9 [ST20 Thm 1.2]: bound on `|C|`
  when `|Λ(C, δ)| ≤ ℓ`.
- `large_alphabet_barrier_bdg24_agl23` — ABF26 T3.10: any code attaining the generalized
  Singleton bound requires exponential-in-`1/η` alphabet.
- `random_linear_lambda_lower_glmrsw22` — ABF26 T3.11 [GLMRSW22 Thm 4.1]: random linear
  code of appropriate rate has list size lower-bounded with high probability.

### Lower bounds — Reed-Solomon (§3.2)

- `rs_lambda_superpoly_extension_bkr06` — ABF26 T3.12 [BKR06 Cor 2.2]: superpolynomial
  list-size for RS over extension fields.
- `rs_lambda_large_prime_ghsz02` — ABF26 T3.13 [GHSZ02 Cor 20]: large list-size for RS
  over prime fields.
- `rs_lambda_high_rate_jh01` — ABF26 T3.14 [JH01 Thm 2]: large-rate RS list-size
  separation.

### Subspace-design upper bounds (§3.1)

- `subspaceDesign_list_decoding_cz25` — ABF26 T3.4 [CZ25 Thm B.5]: τ-subspace-design
  codes are list-decodable up to capacity.
- `frs_list_decoding_capacity_cz25` — ABF26 C3.5 [CZ25 Cor 2.21]: folded RS codes
  are list-decodable up to capacity (corollary of T3.4 via T2.18).
- `random_rs_list_decoding` — ABF26 T3.6 [AGL24 Thm 1.1]: random Reed-Solomon
  domains are list-decodable near capacity with high probability, stated over
  `Probability.uniformSizeSubsetOfLe`.

## Deferred statements

- ABF26 T3.15 [CW07] — algorithmic hardness barrier (discrete-log reduction). Out of
  scope per `docs/kb/ABF26_PLAN.md` §7 D2 (we formalise combinatorial statements only).

## Disposition ledger (issue #54)

Per-paper status of the §3 list-decoding family carried by this file.  This is the §3
list-bounds workstream, distinct from Johnson (#49), GGR11 interleaving (#50), and GK16/CZ25
subspace-design (#53); the CZ25 §3.1 upper bounds below are tracked under **#53**, not here.

*PROVEN in-tree* (`theorem`, `sorry`-free, axiom-clean):

- `linear_lambda_ge_elias_volume_eli57` (L3.7 [Eli57]) — Elias volume list-size lower bound.
- `linear_lambda_ge_entropy_volume` (C3.8) — entropy-volume lower bound (MS77 Hamming-ball
  volume via Robbins–Stirling, all in-tree).
- `linear_C_le_generalized_singleton_st20` (T3.9 [ST20 Thm 1.2]) — the generalized Singleton
  bound.  **The ST20 puncturing/coset pigeonhole core that issue #54 flags as the optional
  in-tree target is complete**: `exists_representative_center_sum_hammingDist_le` (plurality
  averaging) + helpers `st20_kernel_extract` / `st20_dist_bound` / `st20_nat_ineq` /
  `st20_ncard_eq` assemble the full proof under the faithful lattice (`hlat`) and
  range (`ha_le`) hypotheses documented at the theorem.
- `rs_lambda_high_rate_jh01` (T3.14 [JH01 Thm 2]) — high-rate RS list-size separation
  (interpolation construction in `ListDecoding.JH01`).

*EXTERNAL ADMIT, NEEDS_CLASSICAL* (`def … : Prop`; no in-tree route — genuine paper content):


- `random_linear_lambda_lower_glmrsw22` (T3.11 [GLMRSW22 Thm 4.1]) — the random generator
  matrix probability space is in-tree; the GLMRSW22 first-moment count over it is absent.
- `random_rs_list_decoding` (T3.6 [AGL24 Thm 1.1]) — random-domain RS list-decoding
  bound absent in-tree; the probability space is now the canonical
  `Probability.uniformSizeSubsetOfLe`.

*EXTERNAL ADMIT, COUNTING DISCHARGED — narrowed to an irreducible geometric/asymptotic core*
(`def … : Prop` + proven `_of_residuals` reduction; the arithmetic side conditions issue #54
asks to close where feasible are **already closed in-tree**):

- `large_alphabet_barrier_bdg24_agl23` (T3.10 [BDG24, AGL23]) — reduction proven in
  `AGL23.large_alphabet_barrier_of_counting`; residual = the `AGL23CountingExtraction`
  geometric counting inequality.
- `rs_lambda_superpoly_extension_bkr06` (T3.12 [BKR06 Cor 2.2]) — the roots→`q^d` cardinality
  arithmetic is discharged by `rs_lambda_superpoly_extension_bkr06_of_residuals` (via the
  proven `BKR06.subspacePoly_natDegree_ge_target` bridge) and the fiber-count form
  `_of_family`; residual = the BKR06 Lemma 3.5 roots→distinct-close-codewords *encoding* at
  the genuine extension parameters (a `W ≤ F` form is parameter-degenerate, see the in-file
  PARAMETER DEFECT note — use `_of_family`).
- `rs_lambda_large_prime_ghsz02` (T3.13 [GHSZ02 Cor 20]) — reduction proven in
  `rs_lambda_large_prime_ghsz02_of_residuals`; residual = the `GHSZ02LargeN` asymptotic input
  (`ToMathlib/GHSZ02Cor20.lean`).

*TRACKED UNDER #53 (GK16/CZ25), recorded here for completeness*:

- `subspaceDesign_list_decoding_cz25` (T3.4 [CZ25 Thm B.5]) — admit; design→Λ dimension count.
- `frs_list_decoding_capacity_cz25` (C3.5 [CZ25 Cor 2.21]) — admit + proven
  `frs_list_decoding_capacity_cz25_of_residuals_prop`; corollary of T3.4 via T2.18.

**No statement in this file is disproven, and the file is `sorry`-free** (every "sorry"
token is inside a docstring describing the *missing external proof*, never a proof term):
the external results are recorded as `def … : Prop` admit-statements with explicit
"Missing ingredient" notes, and each reducible one carries a proven `_of_residuals` bridge.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026.
- [Eli57] Elias. (Lemma 3.7 in ABF26 cites the original Elias paper).
- [ST20] Shangguan-Tamo. Theorem 1.2.
- [BDG24], [AGL23] (Theorem 3.10 in ABF26).
- [GLMRSW22] (Theorem 4.1, source of T3.11).
- [BKR06] Cor 2.2, source of T3.12.
- [GHSZ02] Cor 20, source of T3.13.
- [JH01] Theorem 2, source of T3.14.
-/
