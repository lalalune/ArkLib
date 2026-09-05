# The constructed polynomial basis in the certified production field

The [root-domain basis construction](astra_mca_polynomial_basis-2026-09-05.md)
is now instantiated over the repository's exact production field and
generator. Four additional theorems in
[`astra_mca_production_basis.lean`](../../scripts/probes/astra_mca_production_basis.lean)
pass local Lean 4.30.0-rc2. **This proves the concrete polynomial basis;
the actual MCA witnesses, their probability and the threshold consequence
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
exceed probability 2^-128. Producing those scalars and verifying the
same-support no-joint-explanation clause remain separate proof steps.

## Reproduction and provenance

From a Lake project using the repository's pinned Mathlib, with the
polynomial, interpolation, Lucas primality and prime-tactic imports cached,
run

```sh
bash /absolute/path/to/arklib/scripts/check-mca-production-basis.sh /tmp/mca-proof-lib
```

The [helper](../../scripts/check-mca-production-basis.sh) compiles the
unaltered production certificate and polynomial basis into the supplied
directory, then checks the concrete instantiation using those exact compiled
dependencies. It runs individual Lean compilations, without a full ArkLib
build. Use a separate output directory for each toolchain.

The local audit checks 38 named axiom reports: 31 polynomial construction
theorems, three existing certificate theorems, and four new instantiation
theorems. All use only the permitted standard axioms, with no compiler
warnings or placeholder proofs. The expanded
[auxiliary CI](../../.github/workflows/proximity-strip-proof.yml) runs this
same helper on both supported pins and audits these reports alongside the
other auxiliary proofs. Its status must be checked for the new revision.

The previous construction revision `8c22713deaa91a0a100e04e8275d11765f4437a4`
passed both versions in
[run 33987947699](https://github.com/lalalune/ArkLib/actions/runs/33987947699).
That earlier run does not cover this concrete instantiation.

The strongest previously computed numerical upper bound is unchanged.
No exact threshold, improved companion score, matching universal bound,
or prize solution is claimed here.
