# The census programme: the δ* architecture (#357)

> Status snapshot 2026-06-11. This page is the navigation map for the census approach to
> pinning `δ*` (the MCA threshold of smooth-domain RS codes, issue #357). **Read this before
> pruning, refactoring, or extending anything named below** — the #353 cleanup deleted a
> load-bearing file (`KKH26ParsevalThreshold.lean`) as "superseded" because this map did not
> exist (DISPROOF_LOG O151); it has been restored.

## The one-paragraph summary

For the adjacent/two-monomial stack families, the bad scalars of an MCA line at exact
agreement are **exactly** the pivot coefficients of band-constrained subsets of the domain
(the census laws — proven). Band-constrained subsets of 2-power smooth domains are
**exactly** fiber unions, in char 0 at every dyadic depth (the tower — proven) and in `F_p`
above an explicit threshold (the finite tower — proven, Parseval-sharpened). The census is
an unconditional `ε_mca` lower bound (proven), and `δ* = 1 − a_c/n` at the census crossing,
conditional on the named extremality surface (the crossing pin — proven conditional). The
two-family profile law (`ε_mca·q = min(q, max(staircase, census))`) matches **every exact
data point ever computed** (9 instances, 14+ field-combos, 3 red-team cycles).

## The theorem stack (all axiom-clean `[propext, Classical.choice, Quot.sound]`, on main)

| layer | file | headline |
|---|---|---|
| exact pin | `DeltaStarExactPinF5.lean` | `mcaDeltaStar_C542_eq_quarter` — first exact MCA-threshold value anywhere (RS[F₅,4,2], δ* = 1/4) |
| symmetry | `MCAEquivariance.lean` (sibling), `MCAMonomialEquivariance.lean` | invariances + `mcaEvent_monomial` (perm × diagonal; the GRS twist that merges the extremal orbits) |
| census law | `KKH26CensusLaw.lean` | `badScalar_iff_subsetSum` — bad λ ⟺ negated r-subset sum (adjacent pair, k = a−1) |
| census law | `KKH26ConstrainedCensusLaw.lean` | `badScalar_iff_constrainedSubsetSum` — general code degree, the constrained band |
| census law | `KKH26GapCensusLaw.lean` | `badScalar_iff_gapBand` — arbitrary two-monomial stacks `(X^A, X^B)` |
| structure | `KKH26FiberStructural.lean` | `fiberUnion_gapBand` / `kkh26_badScalar_of_fiberUnion` — fiber unions satisfy the band structurally (KKH26 Prop 1 inside the framework) |
| classification | `CensusClassificationCharZero.lean` | `subset_neg_mem_of_sum_zero` (subset Lam–Leung) + `gapBand_antipodal_charZero` — char-0 depth 1 |
| classification | `CensusTowerDescent.lean` | `tower_closed_of_dyadic_sums_zero` — char-0 at **all** dyadic depths |
| finite fields | `HaloFreeThreshold.lean` | `sum_pow_eq_zero_iff_antipodalClosed` — depth-1 halo provably empty above `(2^{m−1})^{2^{m−1}}` (the antipodal-differential device) |
| finite fields | `CensusTowerFinite.lean` | `tower_closed_of_oracle` + `tower_closed_finite` — the F_p tower at all depths above the threshold |
| finite fields | `KKH26ParsevalThreshold.lean` (restored) + `HaloFreeThresholdParseval.lean` | `tower_closed_finite_parseval` — threshold exponent halved: `(2^m)^{2^{m−2}}`; unconditional census reaches n = 128 at \|F\| < 2^256 |
| bracket | `CensusLowerBound.lean` (sibling) | `census_le_epsMCA` — census is an unconditional `ε_mca` lower bound |
| pin | `CensusConditionalPin.lean` + `CensusLowerBound.lean` (sibling) | `mcaDeltaStar_eq_of_censusCrossing'` — δ* = census crossing, conditional on `CensusUpperExtremal`; non-vacuously instantiated at F₅ |
| staircase | sibling universal-band files | `ε_mca·q` exact on the first two bands for every code (the double-spike mechanism) |
| staircase | `BandCollapse.lean` | `badScalar_card_le_band` / `epsMCA_le_band` — **the band collapse** (O153): ≤ `j+1` bad scalars on band `j` for distance `> 3j`; the rigid relation `w_γ = w_{γ₁} + (γ−γ₁)v` + injection + pinch |
| staircase | `BandExactness.lean` | `epsMCA_band_exact` — **the exact staircase**: `ε_mca(RS, j/n) = (j+1)/q` exactly at every in-hypothesis band (collapse + spike LB + `rs_nonzero_wt_lower`) |

## The empirical layer (DISPROOF_LOG O135–O152; probes in `scripts/probes/`)

- **O137/O138**: KKH26-extremality at exact rungs; the (12,6) flat numerator solved (the
  m=1 adjacent pair is the extremal stack; numerator = constrained census, field-indep).
- **O139/O140/O141**: first window-interior census data; family death radii; the
  fake-point reformulation (`e₂..e_c = 0 ⟺ p_j = t^j` — masquerade as a point); MITM
  counting; c*(n) growth (the family pushes INTO the window as n grows).
- **O142/O145/O150**: the classification verified exactly at four instances (multi-prime
  intersections = fiber unions); the **one-orbit halo law** (each prime carries exactly one
  rotation orbit of halo); the 2-prime-intersection trap (norms share divisors — use ≥ 3
  primes + char-0 anchor).
- **O146/O147/O152 (red-team cycles)**: `CensusUpperExtremal` refuted-as-stated (double
  spike at a = n−1) and **corrected to the two-family max**; the corrected law matches all
  exact data including prime-order domains (census = prime Lam–Leung predictions).
- **O148/O149/O151**: the production crossing priced (certified census caps at 2^64 < ε*·q
  before Parseval; the true-count uncertainty localized to s ∈ [128, 256] after); the halo
  mechanism verified at the norm level (N(α) = 2²·193² — monogamous halo membership).

## The conditional production answer and its three surfaces

**δ*(production smooth RS, ε* = 2⁻¹²⁸) = 1 − a_c/n**, where `a_c` is the true-census
crossing. Machine-checked end-to-end except for:

1. **Census-band sup-extremality** (the corrected `CensusUpperExtremal`, now needed ONLY in
   the census-dominance regime: the staircase regime is exact by theorem
   (`epsMCA_band_exact`) up to a third of the distance). Exact at 9 instances; 3 red-team
   survivals; equivalent in its regime to beyond-Johnson list-decoding bounds (the CS25
   coupling) — this is THE wall.
2. **The true subset-sum count at s ≥ 256** (the certified layer stops at n = 128
   post-Parseval; deeper needs Thorner–Zaman (`KKH26PolyFieldCeiling`) or
   lacunary-resultant progress).
3. **The beyond-Johnson floor** (unconditional `ε_mca` upper bounds past `1 − √ρ` —
   the 25-year wall; every other obstruction has been reduced to it or to 1.).

If the char-0 census forecasts hold at s* ≈ 256, the answer reads
**δ* = capacity − c(ρ)** with `c(ρ) ≈ 2/s*` a *constant* — sharper than the published
`capacity − Θ(1/log n)` (whose log came from prime-threshold coupling, not the census).

## Working rules learned (cost real debugging time)

- ZMod p `Field` needs `Fact (Nat.Prime p)` via `decide` (norm_num's prime ext is absent
  in this cone). `(1/4 : ℝ≥0) ≤ 1` needs `div_le_one`; `push Not` not `push_neg`.
- `coeff_X_pow` if-conditions need **both** orientations; `simp` normalizes `C`-of-`if`
  into polynomial ifs — case-split memberships first. `rw` cannot see through
  beta-redexes — use `show` with the reduced form.
- `eq_pow_of_pow_eq_one` needs `[NeZero n]`; `Finset.single_le_sum` needs `(f := …)`.
- The resultant pillars live in `ArkLib.ProximityGap.ResultantLiftLoop52`.
- Landing flow under sibling races: keep `/tmp` copies; `git reset fork/main` + re-apply +
  manual sorted import insert when `update-lib.sh` hits others' untracked files; always
  `git diff --cached` before commit; ≥ 3 primes + char-0 numeric anchor before declaring
  anything "field-independent".
