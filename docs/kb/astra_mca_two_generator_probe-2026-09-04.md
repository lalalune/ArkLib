# Exact finite MCA certificates from two syzygy generators

The two-generator construction gives **18, 66, and 258 distinct MCA-bad
scalars** on the 16-, 64-, and 256-point smooth domains respectively, over
the repository's production prime. All agreement and no-joint-explanation
claims below have exact finite certificates. They are not Lean-formalized.
These are certified lower bounds; the probes do not enumerate every bad scalar.

This is a finite construction, not a production-domain result. The field is

```
P=365375409332725729550921208179070755120141565953,
floor(P/2^128)=1073741824.
```

None of the finite counts here exceeds that probability numerator budget.
The 2^30-point case still requires a proof that its cancellation directions
are distinct. Smaller successful cells do not establish that claim.

## First irregular mu16 certificate

Write the nodes as `omega^j`, for j=0,...,15, where

```
omega=357111556877444407914257742635116754287240874648.
```

The script checks exact order 16. The first tested irregular partition is

```
AB:        [0,1,4,9]
AC:        [2,6,11,15]
BC:        [3,7,8,10,12,14]
private A: [5,13].
```

Let A,B,C be the pair-region vanishing polynomials. The original coefficient
matrix for `Au+Bv+Cw=0` has zero kernel at product degree 6 and a
two-dimensional kernel at degree 7. The two exact kernel basis vectors give
two local codeword triples

```
(0, Au_1, -Bv_1),       (0, Au_2, -Bv_2),
```

all of degree less than k=8. Their three prescribed cores each have 10 points.
At every shared core point both coordinate values agree; the two private
points receive the A pair (0,0).

There are 18 absent-core/coordinate slots. All residual vectors are nonzero
and have distinct projective directions. All cancellation scalars are already
finite for this basis. Each resulting codeword agrees with the received
combination on its 10-point core plus the extra point, giving 11 agreements.

`astra_mca_two_generator_probe.py` emits the full exact receipt: partition,
primitive root, syzygy basis, both local triples, received pair, 18 scalars,
all witness polynomial coefficients and supports, and every parity certificate.
An independent reviewer reconstructed the local values and independently
computed all 18 no-joint parity checks from the receipt; all passed.

## The recursive architecture after two deletions

The general construction and deletion proof are recorded in
[the two-generator bridge](astra_mca_two_generator_bridge-2026-09-04.md).
Start with the balanced recursive
[four-coset partition](astra_mca_paircover_four_cosets-2026-09-04.md), whose
old minimum product degree is D=n/2. Compute its two degree-D generators.
For `xi in AB` and `eta in AC`, use the old w-cofactor row to choose a
combination vanishing at eta and another vanishing at xi. Divide those
triples by `X-eta` and `X-xi`, respectively.

The probe chooses the **first valid pair**, stopping once the two old
w-evaluation rows are independent. It never changes the pair to improve
cancellation counts. For all three prescribed cells, the first pair is
`(index(xi),index(eta))=(0,1)`. Those coordinates become private A points.

| n | k | Pair-region sizes | Core size | Event agreement | Distinct bad scalars |
|---:|---:|---|---:|---:|---:|
| 16 | 8 | 4,4,6 | 10 | 11 | 18 |
| 64 | 32 | 20,20,22 | 42 | 43 | 66 |
| 256 | 128 | 84,84,86 | 170 | 171 | 258 |

Every mismatch residual is nonzero, and all n+2 projective directions are
distinct in each cell. The fixed basis change `g -> g+f` makes all those
directions finite. The script then checks every codeword agreement and every
no-joint certificate. This goes beyond a count of projective directions.

## The no-joint certificates

For each event support, take k points of its core together with the extra
point. On these k+1 distinct nodes z_j, define

```
lambda_j = 1 / product_{l != j}(z_j-z_l).
```

The script independently checks `sum lambda_j*z_j^d=0` for every
`d=0,...,k-1`. Thus the row annihilates every degree-less-than-k codeword.
Applied separately to the two received coordinates, it gives a nonzero
syndrome pair. Their combination at the chosen cancellation scalar is zero.
If a joint codeword pair explained the event support, both syndromes would
instead be zero. This certifies the no-joint clause directly, in addition to
the core-uniqueness argument in the bridge note.

The deletion probe hashes the complete sequence of computed scalars, supports,
witness coefficients, parity rows, and syndrome pairs after checking them.
The hashes are receipts for deterministic reruns, not substitutes for the
checks or cryptographic proofs of the mathematical claim.

## Reproduction and remaining obligation

```
python3 scripts/probes/astra_mca_two_generator_probe.py
python3 scripts/probes/astra_mca_two_generator_delete_probe.py
```

The first command emits the full irregular mu16 certificate. The second emits
three compact receipts, including all certificate counts and SHA256 digests.
The prime is the one certified by `_PrizeShapePrimeP30.lean`; each finite
domain's primitive-root order is checked again by the probes.

The general deletion lemma supplies degree-allowed local triples for a
production-size construction. It does **not** by itself prove that residual
directions at different coordinates are distinct. That collision problem is
the substantive remaining step for this architecture. No additional domain
sizes or alternative deletion pairs were searched in these three-cell tests,
and no production unsafe-radius certificate or prize solution is claimed.
