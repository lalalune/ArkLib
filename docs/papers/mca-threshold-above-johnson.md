# The Mutual Correlated Agreement Threshold of Reed–Solomon Codes Above the Johnson Radius: A Machine-Checked Theory

**ArkLib contributors** · 2026-06-12 · all results formalized in Lean 4 over Mathlib;
every theorem cited below is axiom-clean (`[propext, Classical.choice, Quot.sound]`),
in-tree under `ArkLib/Data/CodingTheory/ProximityGap/`, and was developed on the
issue threads #357 → #371 → #389 of `lalalune/ArkLib`.

## Abstract

Mutual correlated agreement (MCA, [ABF26] Definition 4.3) is the correlated-agreement
property underlying the soundness of FRI-style proximity tests: for a code `C ⊆ F^n`,
radius `δ`, and a pair of words `(u₀, u₁)`, a scalar `γ` is *bad* when the line
`u₀ + γ·u₁` is explained by a codeword on a witness set `S` of size `≥ (1−δ)n` on which
no joint pair of codewords explains `(u₀, u₁)`. The quantity `ε_mca(δ)` is the maximal
bad-scalar fraction over word pairs, and the threshold `δ*(ε*)` — the largest radius at
which `ε_mca ≤ ε*` — is open between the Johnson radius `1 − √ρ` and capacity `1 − ρ`.

We develop a complete machine-checked theory of the *failure side* of this question for
smooth-domain Reed–Solomon codes. The main results:

1. **The boundary band is solved exactly.** In the deepest radius band before capacity
   (`k < (1−δ)n ≤ k+1`), the supremum of the bad-scalar count over *all* word pairs
   equals `C(n, k+1)` when `C(n,k+1)² ≤ q`, attained by an explicit stack; and is
   `≈ q` (complete failure) unconditionally when `C(n,k+1) ≫ q`.
2. **The first fully determined threshold curve.** For the *ladder stack*
   `(x^{k+1}, x^k)`, the bad-scalar count is identically `0` below the boundary band and
   exactly the subset-sum spectrum mass `Σ_{a∈A(h,k+1)} 2^a·C(h,a)` inside it.
3. **The modular census.** Every far-stack bad set is, exactly, a set of remainder-
   coefficient ratios in `F[X]/P_S` — reducing all threshold counts to polynomial
   arithmetic.
4. **The capacity-failure bandwidth law.** At every band `(1−δ)n ≤ k+m+1`, some stack
   has `C(n,k+m+1)·q ≤ #bad·((1 + C(k+m+1,k+1)C(n,m))·q^{m+1} + C(n,k+m+1))`; hence
   wherever `C(n,k+m+1) ≥ (1 + C(k+m+1,k+1)C(n,m))·q^{m+1}`, at least half the field is
   bad. This quantifies the *width* of the capacity-failure region:
   `Θ(n·H(ρ)/log q)` bands at production parameters.
5. **Two-sided band brackets and the reduction of the remaining question.** Between the
   failure zone and the Johnson radius, the bad count is bracketed by an attainable
   lower construction and a packing upper bound, and the residual gap is reduced — by
   an exact fiber-structure theorem — to the classical sub-Johnson list-size question
   for Reed–Solomon codes.

The positive side (that MCA *holds* above Johnson at radii outside the failure zone)
remains the open conjecture; our results pin exactly where any proof of it must live.

---

## 1. Setting and definitions

Throughout, `F` is a finite field of size `q`, `dom : Fin n ↪ F` an injective
evaluation domain, and `rsCode dom k` the Reed–Solomon code of evaluations of
polynomials of degree `< k` (file `GranularityLadderRS.lean`). The MCA event
(`Errors.lean`, after [ABF26] Def. 4.3):

```
mcaEvent C δ u₀ u₁ γ ⟺ ∃ S, |S| ≥ (1−δ)·n ∧
                         (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ·u₁ i) ∧
                         ¬∃ v₀ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i
```

We write `badSet(u₀,u₁,δ) := {γ : mcaEvent γ}` and study `#badSet`. A *band* is a
maximal radius range with a fixed minimal witness size: band `m` is
`k+m < (1−δ)n ≤ k+m+1` (band `0`, the *boundary band*, is the deepest before
capacity). A direction `u₁` is *strongly far* when every codeword agrees with it on at
most `k` points; for `u₁ = x^k` this holds automatically
(`agreeSet_card_le_of_natDegree_eq`, `BoundarySliceUnconditional.lean`).

## 2. The interpolation-residual engine

The bordered Vandermonde residual `e_t(y) := det[1, x, …, x^{k−1}, y]_{t}` of a
`(k+1)`-tuple `t` (file `OwnershipBound.lean`) satisfies three laws that drive
everything:

- **Affinity**: `e_t(u₀ + γu₁) = e_t(u₀) + γ·e_t(u₁)` (`residual_line`);
- **Vanishing on extensions**: if `y` agrees with a degree-`<k` polynomial on `t`,
  then `e_t(y) = 0` (`residual_eq_zero_of_extends`), with the converse for injective
  tuples (`extension_of_residual_eq_zero`, `GeneralKMultiplicity.lean`);
- **Determination**: a tuple inside a witness with `e_t(u₁) ≠ 0` pins
  `γ = −e_t(u₀)/e_t(u₁)` (`gamma_eq_of_owned`).

**Theorem 2.1 (boundary-slice exact law; `boundary_slice_badSet_eq`,
`BoundarySliceExact.lean`).** At the boundary band, for strongly far `u₁`,

```
badSet = { −e_t(u₀)/e_t(u₁) : t an injective (k+1)-tuple }   — both inclusions.
```

**Theorem 2.2 (master modular reduction; `residual_eq_remainder_coeff`,
`ResidualModularReduction.lean`).** For any polynomial `Q` and any tuple `t` with node
polynomial `P_t = ∏(X − xᵢ)`:

```
e_t(Q ∘ dom) = (Q mod P_t).coeff k · e_t(x^k).
```

Hence (`boundary_slice_badSet_modular_of_natDegree`) for every stack `(Q₀, Q₁)` with
`deg Q₁ = k`, the boundary bad set is exactly the set of *modular Wronskian ratios*
`−(Q₀ mod P_S).coeff k / (Q₁ mod P_S).coeff k` over `(k+1)`-subsets `S` — the entire
census is arithmetic in `F[X]/P_S`, and the threshold value is an image-size count.

**Theorem 2.3 (universal ceiling; `universal_badSet_card_le`,
`UniversalBoundaryBound.lean`).** For *every* stack — no hypotheses — and every radius
below capacity, `#badSet ≤ C(n, k+1)`. The proof introduces the *gluing lemma*
(`explainable_of_tuple_residuals_zero`): a witness all of whose tuples kill the
direction residual admits a single explaining codeword, which assembles a joint pair
and contradicts badness; and the set-functoriality of the ratio
(`residual_comp_perm`: row permutations scale both determinants by the same sign).

## 3. The boundary band, solved

**Theorem 3.1 (generic-far pin; `exists_genericFar_badSet_card`,
`GenericFarPin.lean`).** If `C(n,k+1)² ≤ q`, there exists `Q₀` with
`#badSet(Q₀, x^k) = C(n,k+1)` at the boundary band — the universal ceiling is
attained. The proof shows the modular Wronskian functionals
`L_S(W) = (W mod P_S).coeff k` are pairwise distinct on degree `< 2k+2`
(`coeffFn_separation`, via the Lagrange divided-difference form `coeffFn_lagrange`
and a Vandermonde-kernel argument `coeffFn_vanishing`), so each subset pair kills only
a `q^{2k+1}`-hyperplane of the coefficient space (`card_linearKernel`), and a union
bound yields a collision-free stack.

**Theorem 3.2 (all-stacks solution; `boundary_allStacks_solution`,
`UniversalBoundaryBound.lean`).** Under `C(n,k+1)² ≤ q`, the boundary-band sup over
all stacks equals `C(n,k+1)` exactly.

**Theorem 3.3 (production failure; `boundary_production_failure`,
`ProductionBoundaryFailure.lean`).** Unconditionally,
`∃ Q₀ : C(n,k+1)·q ≤ #badSet·(q + C(n,k+1) − 1)`. When `C(n,k+1) ≫ q` (production
parameters), `#badSet ≈ q`: essentially every scalar is bad — the exact-form analogue
of the KKH26 failure-close-to-capacity phenomenon, with explicit constants, proven by
first-moment averaging plus Cauchy–Schwarz over value fibers.

## 4. The ladder curve, fully determined

For the *ladder stack* `(x^{k+1}, x^k)` over an antipodally closed power domain
(`dom i = gⁱ`, `n = 2h`, `g^h = −1`):

**Theorem 4.1 (Schur-ladder law; `residual_ladder_schur`, `ladder_ratio_eq`,
`LadderSchurReduction.lean`).** `e_t(x^{k+1}) = (Σ nodes of t)·e_t(x^k)`; every tuple
ratio is the negated node sum; hence the boundary bad set is the negated
`(k+1)`-fold subset-sum set of the domain
(`boundary_slice_ladder_badSet_eq_unconditional`, with the farness hypothesis
discharged).

**Theorem 4.2 (spectrum fusion; `LadderSpectrumFusion{,Exact,Value}.lean`).** Subset
sums over the antipodal domain are exactly the realizable signed sums (both
inclusions: cancellation forward, pair-padding `spectrumLift` backward), so

```
#badSet(ladder, boundary band) = Σ_{a ∈ A(h,k+1)} 2^a·C(h,a),
A(h,m) = {a ≤ m : a ≡ m (mod 2), m + a ≤ 2h},
```

conditional only on the in-tree cyclotomic injectivity `sVal_injOn`
(`boundary_slice_ladder_badSet_card`). Numerically verified: `h=4, k=2` gives
`2·C(4,1)+8·C(4,3) = 40`, matching the exhaustive census.

**Theorem 4.3 (the cliff; `ladder_badSet_empty_below_boundary`,
`BandPackingLaw.lean`).** Below the boundary band the ladder bad set is *empty*: a
`(k+2)`-point witness contains two one-node-swap tuples whose Schur values force two
distinct nodes equal. With `ladder_badSet_card_le_spectrum_all_radii`
(`FullBandLadderLaw.lean`), the ladder `ε_mca` curve is completely determined at every
radius — the first such curve above Johnson for any stack class.

## 5. Deep bands: brackets, witness mass, and the bandwidth law

**Theorem 5.1 (band packing; `band_packing_law`, `BandPackingLaw.lean`).** For
strongly far directions at band `m`: `#badSet·C(k+m+1,k+1) ≤ C(n,k+1)` — witnesses of
distinct bad scalars overlap in ≤ `k` points, so their `(k+1)`-subset families pack
disjointly.

**Theorem 5.2 (attainment; `band_attainment`, `band_attainment_chained`,
`BandAttainment{,Chained}.lean`).** Disjoint blocks give `#badSet ≥ ⌊n/(k+m+1)⌋`;
overlapping blocks stepping by `m+1`, glued by Lagrange interpolants along interval
chains, improve this to `⌊(n−k)/(m+1)⌋` — extremal among interval core families for
the packing constraint.

**Theorem 5.3 (witness mass; `deep_band_witness_mass`, `DeepBandCoherence.lean`).** A
`(k+m+1)`-core is *coherent* for `Q` when the core interpolant of `Q` has vanishing
coefficients in degrees `k+1,…,k+m`; coherent cores are full band-`m` witnesses for
`γ_T = −coeff_k` (`mcaEvent_of_coherent`). Coherence is `m` subtraction-linear
conditions, so unconditionally some stack has coherent-core density `≥ q^{−m}` among
all cores: `∃ Q₀ : C(n,k+m+1) ≤ #(coherent cores)·q^m`.

**Theorem 5.4 (exact moments; `card_coherent_eq`, `card_pair_coherent_eq`,
`ExactCoherenceCount.lean`, `PairCoherenceCount.lean`).** On the coefficient family of
degree `< M = 2(k+m+1)`: the per-core coherent count is exactly `q^{M−m}` (a
polynomial of degree `< |T|` is its own interpolant, so prescribing coherence
coordinates is free), and for cores overlapping in ≤ `k` points the joint
coherence-plus-value-match count is exactly `q^{M−2m−1}` — by *merge-interpolation
surjectivity*: prescribe the `T`-interpolant freely, patch the `T'`-side on the
overlap with a degree-`<k` interpolant, and merge on `T ∪ T'`, which fits in degree
`M`. No rank computations or dual bases are needed; all fiber counts follow from the
shift bijection (`card_zeroFiber_eq_of_surjective'`).

**Theorem 5.5 (THE CAPACITY-FAILURE BANDWIDTH LAW; `capacity_failure_bandwidth`,
`CapacityFailureBandwidth.lean`).** At every band `m`, with no side conditions:

```
∃ Q₀ :  C(n,k+m+1)·q  ≤  #badSet(Q₀, x^k) · ((1 + C(k+m+1,k+1)·C(n,m))·q^{m+1}
                                              + C(n,k+m+1)).
```

Consequently, wherever `C(n,k+m+1) ≥ (1 + C(k+m+1,k+1)·C(n,m))·q^{m+1}`:
`#badSet ≥ q/2` — *half the field is bad*. The proof combines the exact first moment,
the stratified second moment (far pairs exact; high-overlap pairs bounded by a
subset-injection count `≤ Nₘ·C(k+m+1,k+1)·C(n,m)`; diagonal free), per-stack
Cauchy–Schwarz over value fibers, family-level Cauchy–Schwarz, and an argmax choice —
entirely in ℕ.

**Corollary 5.6 (the failure-zone width).** At production parameters
(`n = 2^{20..30}`, `ρ` constant, `q ≈ 2^{128}`), the condition of Theorem 5.5 holds
for all `m ≲ n·H(ρ)/log₂ q − O(log n)`: the capacity-failure region — where MCA fails
for half the field — extends `Θ(n·H(ρ)/log q)` bands below capacity. Below that zone
the law goes silent, *as it must*: the positive conjecture (MCA above Johnson) lives
exactly there.

## 6. The reduction of the remaining question

**Theorem 6.1 (fiber structure and the named supply; `coherent_explains_line`,
`deep_band_badSet_card_of_supply`, `DeepBandMultiplicity.lean`).** Each value fiber of
the coherent-core map lies in one word's explainable-core family; defining
`ExplainableCoreSupply B` (every word admits ≤ `B` explainable `(k+m+1)`-cores), the
witness-mass law converts to `∃ Q₀ : C(n,k+m+1) ≤ #badSet·q^m·B`.

**Theorem 6.2 (the supply above the wall;
`explainable_cores_card_of_agreement_le`, `near_scalar_unique`,
`agreeSet_card_le_of_natDegree_le`, `ExplainableCoreSupplyInstance.lean`,
`DeepBandFailureUnconditional.lean`).** For agreement-capped words the supply is a
theorem (`#explCores·C(k+m+1,k) ≤ C(n,k)·C(A−k,m+1)`); for the words the averaging
family actually generates, all agreements are capped at `2k+m+1` by degree, giving the
unconditional `∃ Q₀ : C(n,k+m+1) ≤ 2·#badSet·q^m·C(n,k)` — subsumed by Theorem 5.5
but historically the first unconditional multi-scalar deep-band bound.

**The wall, isolated.** Improving the supply *below Johnson agreement* for arbitrary
off-code words is quantitatively the classical sub-Johnson list-size question for
Reed–Solomon codes (analysis logged in `DISPROOF_LOG.md`, 2026-06-12). Every other
component of the deep-band question is proven. Equivalently: the open content of the
MCA threshold conjecture between Johnson and the failure zone is *exactly* the open
content of sub-Johnson list decoding — a coupling long believed, here machine-checked
as a two-way reduction with explicit constants.

## 7. The proven landscape

| object | value | status |
|---|---|---|
| boundary band sup, `C(n,k+1)² ≤ q` | `= C(n,k+1)` | exact, attained, universal |
| boundary band, production | `≥ Nq/(N+q−1) ≈ q` | unconditional |
| ladder stack, all radii | `0` below band; spectrum mass in band | exact |
| band `m`, scalar count | `[⌊(n−k)/(m+1)⌋, C(n,k+1)/C(k+m+1,k+1)]` | two-sided |
| band `m`, witness mass | `≥ C(n,k+m+1)/q^m` | exact density |
| failure-zone width | `Θ(n·H(ρ)/log q)` bands | bandwidth law |
| sub-failure-zone positive direction | — | **open = the conjecture** |

## 8. Discussion and open problems

The failure side of the MCA threshold question above Johnson is, to the precision of
the constants in Theorem 5.5, closed: we know exactly where MCA collapses (the
boundary value, the production regime, the bandwidth of the failure zone) and exactly
which stacks are extremal (generic-far at small parameters; the coefficient family on
average; the ladder family pinned as a non-extremizer with a complete curve). The
open problem is the positive direction:

> **Conjecture (MCA above Johnson).** There is `ε*(n,q) = poly(n)/q` such that
> `ε_mca(δ) ≤ ε*` for all `δ ≤ 1 − √ρ − η`, and (the open core) the same for some
> `δ` strictly above `1 − √ρ`.

Our results constrain any proof: it must operate strictly below the failure zone of
Theorem 5.5, it must fail for the coefficient family at band depths where
`C(n,k+m+1) ≥ (1+D)q^{m+1}`, and by Theorem 6.1 a sufficiently strong version implies
sub-Johnson list-size bounds. The known refutations and no-gos accumulated by this
programme (the in-tree `DISPROOF_LOG.md`: 60+ entries, including the
prime-field counterexamples to MCA-up-to-capacity and the production-vacuity of
agreement-capped supplies) chart the approaches that cannot work.

## 9. Artifact

All results are in `ArkLib/Data/CodingTheory/ProximityGap/` (Lean 4, Mathlib). The
boundary/census chain: `BoundarySliceExact` → `LadderSchurReduction` →
`ResidualModularReduction` → `BoundarySliceUnconditional` →
`LadderSpectrumFusion{,Exact,Value}` → `FullBandLadderLaw` → `GenericFarSeparation` →
`GenericFarPin` → `UniversalBoundaryBound` → `BandPackingLaw` →
`BandAttainment{,Chained}` → `ProductionBoundaryFailure` → `DeepBandCoherence` →
`DeepBandMultiplicity` → `ExplainableCoreSupplyInstance` →
`DeepBandFailureUnconditional` → `ExactCoherenceCount` → `PairCoherenceCount` →
`CapacityFailureBandwidth`. 103 axiom-clean declarations were added in the final
campaign (rounds 64–84 of #371/#389); every `#print axioms` reports
`[propext, Classical.choice, Quot.sound]`. Probes (exact small-instance computation)
live in `scripts/probes/`; the census at `(q,n,k) = (12289, 8, 2)` validates the
spectrum value `40` and the generic-far value `56 = C(8,3)`.

## References

- [ABF26] Mutual correlated agreement and the soundness of batched FRI
  (the in-tree reference for Definition 4.3; see `Errors.lean`).
- [KKH26] Krachun, Kazanin, Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782 — the antipodal signed-sum spectrum that Theorem 4.2 fuses with.
- [BCIKS20] Ben-Sasson, Carmon, Ishai, Kopparty, Saraf, *Proximity gaps for
  Reed–Solomon codes* — the Johnson-radius baseline.
- The issue threads `lalalune/ArkLib` #232 → #334 → #357 → #371 → #389 contain the
  complete round-by-round development, refutations, and probe data.
