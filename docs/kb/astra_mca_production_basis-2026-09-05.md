# The constructed polynomial basis in the certified production field

The [root-domain basis construction](astra_mca_polynomial_basis-2026-09-05.md)
is now instantiated over the repository's exact production field and
generator. Seven additional theorems in
[`astra_mca_production_basis.lean`](../../scripts/probes/astra_mca_production_basis.lean)
pass local Lean 4.30.0-rc2. **This proves the concrete polynomial basis and scalar projection;
the indexed MCA witnesses, their probability and the threshold consequence
still need formal assembly. The universal lower bound remains open.**

## What is instantiated

The proof imports the existing
[`_PrizeShapePrimeP30.lean`](../../ArkLib/Data/CodingTheory/ProximityGap/Frontier/_PrizeShapePrimeP30.lean)
certificate directly. That source proves primality of

```text
P = 365375409332725729550921208179070755120141565953
  = 2^30*(2^128+192)+1
```

and exact multiplicative order 2^30 of

```text
g = 303645430271030343624574566109998498685964493478 in ZMod P.
```

The new `productionDomain` is the image of `range(2^30)` under `e -> g^e`.
`power_domain_card` derives its size from the exact order, and
`power_domain_roots` proves the required root equations. Neither theorem
enumerates this domain.

`production_deleted_basis` applies the general construction to these
facts. It yields disjoint pair regions A, B, S and a private region I,
covering the concrete power domain, with

```text
card A = card B = 357913939
card S = 357913942
card I = 4
```

and four polynomials F0, F1, G0, G1 of degree at most 536870910. The F
polynomials vanish on A, the G polynomials vanish on B, and corresponding
F/G components agree on S. Their determinant is a nonzero scalar times
the locator of A union B union S.

`production_residual_rows` further supplies exactly 1073741828 nonzero,
pairwise projectively distinct [residual rows](astra_mca_residual_rows-2026-09-05.md)
from that same constructed basis. `production_scalar_projection` now supplies
two coefficient vectors with nonzero denominators and pairwise distinct
[scalar challenges](astra_mca_scalar_projection-2026-09-05.md).

This domain uses the powers displayed in the repository's
[`KKH26.evalCode`](../../ArkLib/Data/CodingTheory/ProximityGap/KKH26WitnessSpread.lean)
definition. The new proof does not yet put the constructed polynomial
evaluations into that indexed code or prove its `mcaEvent` statements.

## Checked field-size arithmetic

`production_projection_arithmetic` verifies, for `M=2^30+4`,

```text
3*choose(M,2) < P
P < M*2^128.
```

The first is the field-size condition in the written four-generator
projection argument. The second says that M distinct bad scalars would
exceed probability 2^-128. Those scalars now exist formally. The general
polynomial same-support lemmas are also checked, but their indexed MCA and
probability consequences still require assembly.

`production_moment_curve_arithmetic` additionally checks `3*M<P` and
`3*M*M<P`, the sufficient bounds used by the implemented univariate
root-avoidance projection.

## Reproduction and provenance

From a Lake project using the repository's pinned Mathlib, with the
polynomial, interpolation, Lucas primality and prime-tactic imports cached,
run

```sh
bash /absolute/path/to/arklib/scripts/check-mca-production-basis.sh /tmp/mca-proof-lib
```

The [helper](../../scripts/check-mca-production-basis.sh) compiles the
unaltered production certificate, polynomial basis, residual-row, evaluation, and projection modules
into the supplied directory, then checks the concrete instantiation using those exact compiled
dependencies. It runs individual Lean compilations, without a full ArkLib
build. Use a separate output directory for each toolchain.

The local audit checks 69 named axiom reports: 31 polynomial construction
theorems, three existing certificate theorems, nine residual-row theorems,
13 evaluation/support theorems, six projection theorems, and seven instantiation
theorems. All use only the permitted standard axioms, with no compiler
warnings or placeholder proofs. The expanded
[auxiliary CI](../../.github/workflows/proximity-strip-proof.yml) runs this
same helper on both supported pins and audits these reports alongside the
other auxiliary proofs. Its status must be checked for the new revision.

The previous construction revision `8c22713deaa91a0a100e04e8275d11765f4437a4`
passed both versions in
[run 33987947699](https://github.com/lalalune/ArkLib/actions/runs/33987947699).
That earlier run does not cover this concrete instantiation.

The first production revision `6ec208d51f7751c80a31d3e7a4e4569b5abb3bce`
passed Lean 4.30 but failed Lean 4.32.2 in
[run 33988276658](https://github.com/lalalune/ArkLib/actions/runs/33988276658):
the latter required explicit conversion from a strict inequality to interval
membership in `power_domain_card`. The source now uses `Set.mem_Iio.mpr`
explicitly. This repair and the residual-row addition passed both pins at
`f5f60954060c9f0ec8645e2b7d01f582279b9c7e` in
[run 33988862034](https://github.com/lalalune/ArkLib/actions/runs/33988862034).
The new scalar-projection revision requires its own CI result.

The strongest previously computed numerical upper bound is unchanged.
No exact threshold, improved companion score, matching universal bound,
or prize solution is claimed here.
