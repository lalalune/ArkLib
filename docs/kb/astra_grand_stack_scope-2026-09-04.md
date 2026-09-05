# The genuine-stack gap and an affine-span fourth-codeword obstruction

Date: 2026-09-04. Mathematical argument and exact Python checks; no new Lean
theorem or prize bound.

For the received word in the
[smooth middle-band construction](astra_grand_smooth_middle_counterexample-2026-09-04.md),
every codeword in the affine span of the three displayed codewords, other than
those three themselves, agrees on at most `5n/8`. Thus a fourth codeword with
agreement above `2n/3` must lie outside that affine span. This does not exclude
a fourth arbitrary Reed--Solomon codeword, or even every member of the larger
five-dimensional family `V_T(X) d(X^m)` with `deg d<=4`.

The source audit also identifies the missing genuine-stack information and
an overstrong quantifier in the existing SYZ43 rank hypothesis.

## 1. Exact missing stack data

[`_F1RegionSyzygyInterface.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_F1RegionSyzygyInterface.lean)
contains no genuine large-stack predicate. Its `Genuine` argument in
`middleExclusion_transport` is an arbitrary six-argument predicate supplied
by the caller. `RegionSyzygyRealizable` records four root subsets, their
cardinalities, numeric band faces, and the minimal syzygy degree. It does
not record a received pair, bad scalars, codeword witnesses, or a bad-count
threshold.

The actual event is
[`Errors.lean`, `mcaEvent`](../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean),
with an integer-threshold equivalent in
[`MCAExactComputationKit.lean`, `mcaEventNat`](../../ArkLib/Data/CodingTheory/ProximityGap/MCAExactComputationKit.lean):

```
exists S, |S| >= s,
  exists f in C, f|S = (u0 + gamma*u1)|S,
  and there is no pair (f0,f1) in C^2 jointly agreeing with (u0,u1) on S.
```

A concrete bad-family target must therefore retain fixed `u0,u1`, a set of
distinct scalars `Gamma`, these event witnesses for every scalar, and the
required inequality on `|Gamma|`. If it uses the F1 region/syzygy interface,
it must also specify how those particular regions and syzygies are extracted
from that same family's decoded codewords and supports. Four codewords close
to one received word would not by itself provide this data.

For example, putting the present received word in `u0` and taking `u1=0`
gives **no MCA-bad scalars at all**. Whenever `f` agrees with `u0+gamma*0`
on `S`, the pair `(f,0)` jointly agrees with `(u0,0)` on `S`, violating the
event's last clause. This remains true regardless of how many codewords
are near `u0`.

The existing merged-block conclusion in
[`_SYZ40FinalAssembly.lean`, `merged_branch_unconditional`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ40FinalAssembly.lean)
also needs explicit bad-scalar attribution to residual pairs on complements
of merged cores. It proves `|B|<=n-1` for at most three such merged blocks
above the `2n/3` agreement threshold. Counting three list members is not a
construction of those residual pairs or of their bad-scalar attribution.

## 2. SYZ43's present `hrank` quantifier admits the zero family

The exact theorem is
[`_SYZ43AutoInstantiation.lean`, `realizabilityCore_of_mcaEvent_witnesses`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_SYZ43AutoInstantiation.lean).
Its `hrank` premise requires, in abbreviated notation,

```
forall phi : Fin r x Fin(s-k) -> Dual(SyndromePair C),
  (forall p, phi(p)(syndromePair C u0 u1)=0) ->
  dim(span(range phi)) = 2*(Ucard-k).
```

Choose `phi` identically zero. Its annihilation condition holds, even if
the index type is empty. The span of its range is the zero subspace, so the
conclusion gives `0=2*(Ucard-k)`. With natural-number subtraction this forces
`Ucard<=k`. Therefore this hypothesis is impossible whenever `Ucard>k`.
The theorem has no additional premise tying `Ucard` to a support union which
would remove this zero-family specialization.

The proof obtains the bridge with
`obtain <phi,hann,_hblock> := exists_bridge_functionals ...` and discards
`_hblock`. The actual
[`_G87McaEventSyndromeBridge.lean`, `exists_bridge_functionals`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_G87McaEventSyndromeBridge.lean)
returns annihilation **and** linear independence inside each per-witness
block (source lines 265--272). Its construction uses rows of the form

```
phi_(i,j) = ellbar_(i,j) o fst + gamma_i * ellbar_(i,j) o snd,
```

where the parity rows come from the corresponding agreement support.

This is an overstrong sufficient hypothesis, not an invalid Lean theorem.
The existing implication remains valid. Restricting the quantifier to
nonzero or independent blocks would eliminate this particular zero-family
issue when the blocks are nonempty, but would still not preserve the
scalar-weighted support provenance. A corrected intended target must bind
the actual bridge construction and its underlying family, rather than claim
full rank for arbitrary annihilating functionals. The present note neither
asserts nor proves the resulting rank bound.

This source issue was independently confirmed against both named files.

## 3. No fourth codeword inside the displayed affine span

Use the prior construction's notation, with `m>=4`, `n=16m`, `k=8m`,
`t=4m-1`, disjoint pair regions `R_AB,R_AC,R_BC` of size `3m`, and
`q=floor(2m/3)+2` private positions per codeword. The remaining unused set
`E` has size

```
e = 3m+1-3q.
```

The received word is zero on `E`, as in the exact probe. Write its three
known polynomials as

```
f_A=0,     f_B=V_T W_AB r_AB,     f_C=-V_T W_AC r_AC,
f_B-f_C=-V_T W_BC r_BC,
```

where each `W` has degree `3m`, the three `W` are pairwise coprime, and
each cofactor `r` has degree at most `m`. All three cofactors are nonzero.
Moreover `f_B,f_C` are linearly independent: a nontrivial proportionality
would force `W_AB` to divide `r_AC`, contradicting `3m>m`.

Consider `f=alpha*f_B+beta*f_C`, with `(alpha,beta)` different from
`(0,0),(1,0),(0,1)`. The three lines

```
beta=0,     alpha=0,     alpha+beta=1
```

meet only at those excluded vertices, so exactly one or none applies.

**Off the three lines.** On any pair region, agreement with the received
word forces all three known codewords to agree there. Outside `T`, their
common zeros are contained in the roots of `r_AB*r_AC`: a common zero of
`W_AB*r_AB` and `W_AC*r_AC` must be a zero of one cofactor because the two
`W` have disjoint roots. There are at most `2m` such points. Giving the new
word every point of `T` and every private/unused point yields the bound

```
t + 2m + (3m+1) = 9m.
```

**On `beta=0`.** Here `alpha` is neither zero nor one. Everywhere except
the private region of C, the received value is either `f_A=0` or `f_B`;
on the AC pair region it is zero, and on BC it equals `f_B`. Agreement of
`alpha*f_B` therefore requires `f_B=0`, unless the point is private to C.
The roots of `f_B` outside `T` number at most `4m`, so the total is at most
`t+4m+q=8m-1+q`. The case `alpha=0` is symmetric, relabeling the BC value
as `f_C` and allowing the private region of B.

**On `alpha+beta=1`.** Both coefficients are nonzero. Except for the
private region of A and `E`, the received value is one of `f_B,f_C`:
on AB it equals `f_B=0`, and on AC it equals `f_C=0`. Agreement forces
`f_B=f_C`. The difference has at most `4m` roots outside `T`. Hence the
total is at most

```
t+4m+q+e = 11m-2q.
```

These arguments allow accidental cofactor roots. They require no generic
position assumption. Since `2q>=m` and `q<=2m+1` for `m>=4`, all three
bounds are at most `10m=5n/8`, which is strictly below `2n/3` and below
the target assigned agreement `floor(2n/3)+1`.

## 4. Exact verification and remaining scope

Run:

```sh
python3 scripts/probes/astra_grand_stack_affine_span.py
```

The probe reconstructs the existing received word and enumerates every
coefficient pair in its two-dimensional codeword span for `(p,m)=(193,4)`,
`(257,4)`, and `(257,8)`, excluding the three known vertices. It checks
each candidate against its sharper case bound above. It also checks a
fixed finite coefficient sample over the certified Proth field
`p=111*2^128+1` at `m=4,8,16`, and checks the bound arithmetic at the
production parameter `m=2^26`.

All **169,338 exhaustive coefficient-pair checks** pass. The maximum new
agreements are 30 in both length-64 cells (target 43), and 59 in the
length-128 cell (target 86). The three large-field samples contain 373
coefficient pairs each and also pass every case bound.

The exhaustive searches are only within the two-dimensional span; they do
not enumerate all degree-`<8m` polynomials. The large-field and
production-size conclusions in that span follow from the proof, not from
sampling. Whether this same received word has a fourth codeword elsewhere
in the Reed--Solomon code remains unresolved by this bounded attempt.

The [actual MCA conversion](astra_mca_lift_three_core-2026-09-04.md) shortens
the triple region by one and constructs a nontrivial received pair on the
same smooth domain. It verifies the no-joint clause with exact dual parity
certificates and proves the best possible count for its specified three-core
conversion. That count remains below the target; the full event set is not
computed.
