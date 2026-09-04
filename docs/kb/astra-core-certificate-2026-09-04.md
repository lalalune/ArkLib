# Lean kernel certificate for the finite monomial arithmetic

`scripts/probes/astra_core_certificate.lean` passed Lean 4.30.0-rc2 on
2026-09-04 using only `import Std`. It has no Mathlib dependency, `sorry`, custom
axiom, or `native_decide`. The proved declaration is

```lean
theorem AstraCoreCertificate.certificate : AstraCoreCertificate.audit = true := by decide
```

The actual axiom audit printed:

```text
'AstraCoreCertificate.certificate' depends on axioms: [propext]
```

The process exited **0** after **68.91 seconds** wall time and **66.62 seconds**
CPU time. Maximum resident set size was **5,520,474,112 bytes**; the process
reported zero swaps. The source's status comment was then updated from draft to
checked; no definitions, proof bodies, imports, or options changed after the
successful run.

## What the kernel checked

The Boolean predicate computes in integer coordinates for `Z[z]/(z^4+1)` and
enumerates all 70 strictly increasing four-element subsets of the eight roots.
For each subset it computes the degree-two and degree-three coefficients of
`X^a` modulo the four-root polynomial, for every `0 <= a < 8`.

For all 64 exponent pairs it then checks the finite certificate conditions:

* every relevant nonzero proportionality determinant has power-of-two norm;
* every chosen nonzero denominator has power-of-two norm;
* the chosen numerator and denominator solve both residual equations exactly;
* every nonzero cross-product separating candidate labels has power-of-two norm;
* the resulting distinct-label counts equal the full expected 8-by-8 matrix.

It also checks the root relations and power-of-two norms of all distinct-root
differences. Candidate separation is checked against every existing representative,
including those after the first duplicate match. An independent Python comparison
confirmed the remainder recurrence matches all 560 remainder pairs in the original
certificate and that its 680 nonzero representative-separation checks pass.

## Scope

This is a kernel-checked **finite arithmetic certificate**. The mathematical
interpretation and field-specialization argument are in
`proximity-astra-monomial-census-2026-09-04.md`; they are not formalized as a general
field theorem in this file. In particular, the declaration is an equality about
the explicit Boolean audit, not a Lean statement quantifying over all fields or
all MCA witness sets.

The independent direct enumerations over `F9` and `F25` are retained in
`scripts/probes/astra_extension_field_check.py`. They check every scalar and every
affine codeword for all 64 monomial pairs, without using the symbolic remainder
or candidate-label algorithm, and match the same matrix.

None of these finite results establishes the production Proximity Prize threshold
or bounds arbitrary nonmonomial word pairs by nine.

## Reproduction

With a Lean 4.30.0-rc2 toolchain available:

```sh
lean scripts/probes/astra_core_certificate.lean
python3 scripts/probes/astra_order_eight_monomial_certificate.py
python3 scripts/probes/astra_extension_field_check.py
```

The session used a checksum-verified standalone runtime, with no global toolchain
installation or Lake configuration changes. Its exact executed command was:

```sh
/usr/bin/time -l /tmp/arklib-lean-bootstrap/lean-4.30.0-rc2-darwin_aarch64/bin/lean scripts/probes/astra_core_certificate.lean
```

The [official arm64 macOS release archive](https://github.com/leanprover/lean4/releases/download/v4.30.0-rc2/lean-4.30.0-rc2-darwin_aarch64.tar.zst)
had SHA-256
`6a23d26241fd78bcc3d1c24be97341bfe3f4635f2e6feabcbb5863035290ab1b`,
matching GitHub's release-asset digest. `lean --version` reported compiler commit
`3dc1a088b6d2d8eafe25a7cd7ec7b58d731bd7cc`.

Full stdout, stderr and timing are retained for this session at
`/tmp/arklib-lean-bootstrap/astra-core-certificate-attempt2.log`.
