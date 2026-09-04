# Order-eight ceiling assembly and prize-claim audit

Date: 2026-09-04. Audited research base: `54007b004`.

This note assembles existing generic lemmas with G330. It does not introduce a new
cubic identity, prove a worst-case bound over word pairs, or solve the production
Proximity Prize. The accompanying
`docs/kb/proximity-astra-ceiling-draft.lean` is an **uncompiled candidate**: no Lean
toolchain is installed in this session, so neither elaboration nor its axiom
audits have been run. The mathematical argument below is independent of a bounded
prime scan.

## Exact finite statement

Let `p` be prime, `p = 1 mod 8`, `p != 17`, and let `g` have order eight in `F_p`.
Write

```
H = {g^i : 0 <= i < 8},
C = {x |-> a*x+b on H : a,b in F_p},
u0(x) = x^3, u1(x) = x^2.
```

The integer MCA event at agreement threshold three means that some `S ⊆ H` with
`|S| >= 3` admits an affine codeword agreeing with `u0+gamma*u1` on `S`, while
`u0,u1` do not jointly agree with two affine codewords on the same `S`.

Then

```
{gamma : mcaEventNat C 3 u0 u1 gamma}
  = {-sum(S) : S ⊆ H, |S|=3},
#{gamma : mcaEventNat C 3 u0 u1 gamma} = 40.
```

In the radius convention this is the event for every `5/8 <= delta < 3/4`, because
`ceil(8*(1-delta))=3`. At `delta=5/8`, the probability for this particular pair is
exactly `40/p`. Consequently the worst-case MCA error is **at least** `40/p`.
This calculation supplies no matching upper bound on that worst-case error.

There is a more precise witness profile. Exactly eight bad scalars, namely the
members of `H`, have three distinct affine codeword witnesses. The other 32 bad
scalars have one witness each. Every such codeword agrees on exactly three points.

## Proof

1. An affine witness `a*x+b` leaves the monic cubic
   `x^3+gamma*x^2-a*x-b`. It has at most three distinct roots. Any MCA witness thus
   consists of exactly three points, and comparison with
   `prod_(x in S)(X-x)` gives `gamma=-sum(S)`. Conversely that product determines
   `a,b` and gives an affine witness for every triple. The joint exclusion is
   automatic: `x^2` cannot agree with an affine polynomial on three distinct
   points. This is existing theory, formalized generically in
   `KKH26CensusLaw.badScalar_iff_subsetSum` and, with the MCA exclusion included, in
   `Ownership.boundary_slice_ladder_badSet_eq_unconditional`.

2. Split `H` into the four antipodal pairs `{g^i,-g^i}`, `0 <= i < 4`. A triple
   containing an antipodal pair sums to its remaining root: a signed datum of
   weight one. A triple without such a pair selects one signed root from each of
   three pairs: a signed datum of weight three. Hence every triple sum lies in
   the signed weight-`{1,3}` spectrum.

3. Every signed weight-three datum is itself a triple. Every signed weight-one
   datum becomes a triple by adjoining one of the three fresh antipodal pairs.
   This is the specialization of `KKH26.exists_realizing_subset` to `m=3,r=3`:
   take `j=0` for signed weight three, `j=1` for signed weight one. The spectrum
   and triple-sum image are therefore equal as sets, over every admissible prime.

4. G330's `spectrum_card_eq_forty` proves that the spectrum has exactly
   `2*C(4,1)+8*C(4,3)=8+32=40` values whenever `p != 17`. Negation is a bijection,
   so the bad-scalar set has 40 values too. G330 handles all these primes, not
   just those scanned by G328. Its algebraic norm certificate isolates 17 as the
   only possible collision prime congruent to one modulo eight.

5. There are `4*6=24` triples containing an antipodal pair, and each signed
   weight-one value has exactly three such triples. The remaining
   `C(8,3)-24=32` triples give distinct signed weight-three data. G330 excludes
   both within-stratum and cross-stratum collisions. For a fixed scalar,
   distinct triples yield distinct affine codewords: a single nonzero monic
   cubic cannot have two different sets of three roots. This proves the stated
   witness multiplicities.

The prime-17 exception is already represented by G328's explicit collision
`1=-1-2+2^2`. Its exact count 16 is separate from the theorem above, which excludes
17. No inference about the production order `2^30` follows from order eight.

## Existing API and the remaining formal assembly

All paths in this section are relative to
`ArkLib/Data/CodingTheory/ProximityGap/`.

| File / declaration | Exact role |
| --- | --- |
| `Frontier/_G330SpectrumExactBoundary.lean`, `spectrum_card_eq_forty` | Signed spectrum image has size 40 for every qualifying prime except 17. |
| `KKH26StratifiedSpread.lean`, `exists_realizing_subset` | Realizes each signed stratum by an actual subgroup subset; does not require a large-prime inequality. |
| `KKH26CensusExact.lean`, `census_card_le_stratified` | Unconditional triple-sum upper bound 40 at `m=3,r=3`. |
| `KKH26CensusLaw.lean`, `badScalar_census_card` | Polynomial witness census equals negated subset-sum image size. |
| `BoundarySliceUnconditional.lean`, `boundary_slice_ladder_badSet_eq_unconditional` | Full MCA event equals subset-sum image without a remaining farness hypothesis. |
| `MCAExactComputationKit.lean`, `mcaEvent_iff_mcaEventNat_ceil` | Converts radius events to integer agreement thresholds. |

The candidate Lean file implements the signed-spectrum inclusion, the two
cardinality inequalities giving 40, and the polynomial ceiling census. It does
not yet package the final full-MCA corollary on `Fin 8` or formalize the 3/1
witness-multiplicity refinement. The full-MCA mathematical implication above is
immediate from the existing unconditional boundary theorem plus the domain
reindexing; its explicit Lean assembly still requires compilation and review.

## Exact limits of the grand-prize claims

The target error in `Errors.lean` is

```
epsMCA C delta = sup_(u0,u1) Pr_gamma[mcaEvent C delta u0 u1 gamma].
```

The supremum is over all word pairs, not 64 monomial pairs. Therefore neither a
monomial maximum of nine at threshold four nor this particular pair's ceiling
count of 40 determines `epsMCA`. Likewise the prize asks for the specified code
families and rates; a finite order-eight calculation is not a production answer.

There are important stale claims in the research cone:

* `Frontier/_DeltaStarDefinitive.lean` does **not** prove an if-and-only-if
  reduction or that BGK is mathematically necessary. Its actual capstone combines
  an assumed-good/assumed-bad bracket, a sufficient conditional moment bound,
  and an obstruction to a specified uncentered moment estimate. Failure of that
  estimate does not prove that every possible proof must satisfy `BGKFloor`.
  The good and bad inputs also remain explicit hypotheses in the generic
  bracket theorem; the name “unconditional” does not itself instantiate them.

* Its `BGKFloor` is definitionally the **raw** `GaussianEnergyBound`,
  `E_r(G) <= (2r-1)!!*|G|^r`. The repository already records that this bound fails
  past the principal-frequency crossover: `E_r(G) >= |G|^(2r)/|F|`.
  `DCEnergyEssential.lean` and `PairingResidualFailsAtPrize.lean` formalize the
  obstruction, and the header of `GaussPeriodMomentBound.lean` points to the
  corrected `DCEnergyCorrection` interface. The old raw conditional cannot be
  advertised as the viable production-depth input.

* The old `31/64` rate-half pin is not a viable open endpoint for the first
  production field. `Frontier/_SYZ46CensusBridge.lean` explicitly proves
  `refutedPredecessorCensusBound_is_false`, using the SYZ3 over-budget witness;
  it also records the unconditional SYZ6 ceiling
  `deltaStar <= 358612991/2^30`, which is strictly below `31/64`.

The precise surviving rate-half census interface in SYZ46 is
`StripCensusBound`: **every** word pair on the first certified field's
`evalCode g (2^30) (2^29-1)` has at most `2^30-1` bad scalars at radius
`357913940/2^30`. If proved, it gives the floor `357913941/2^30`; together with
SYZ6 it gives the conditional bracket

```
357913941/2^30 <= deltaStar <= 358612991/2^30.
```

This is a bracket, not an exact value, and its lower bound is conditional.
SYZ46 explicitly lists four unfinished obligations behind its master-hypothesis
route: uniform Sylvester injectivity, disjoint-residual support control, the
realizability union-rank bound, and abstract-to-concrete transport. In particular
its final theorem takes `transport` as an additional argument; no reader should
mistake a clean axiom audit of that implication for discharging its arguments.

No production exact threshold, complete four-rate prize theorem, or list-decoding
grand-prize solution is established by this session's finite ceiling assembly.
