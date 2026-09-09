# Final production assembly semantic audit

2026-09-08 local date. Bounded independent source/receipt audit; no rebuild or
census rerun. **PASS: the exported theorem states the intended concrete
production upper bound, without weakened event semantics or extra hypotheses.**

Audited `scripts/probes/astra_mca_order16_assembly.lean`, its production code
and embedding definitions, generic received-word assembly, actual Errors.lean
event/error definitions, and MCAThresholdLedger.lean threshold conversion.

## Concrete target and semantics

- `AstraMcaProductionUpper.productionCode` is exactly
  `ReedSolomon.code productionEmbedding (2^29)` on `Fin (2^30) -> ZMod P`.
  The embedding sends i to `g^i` and proves injectivity using the certified
  order `2^30`. The code membership theorem exposes ordinary polynomial
  degree below `2^29` (equivalently natDegree at most 536870911).
- The new `many_events` theorem constructs one shared pair of received words
  and one finite set of distinct field scalars with cardinality **1073741828**.
  This is a Finset cardinality, not a count of decoder witnesses or repeated
  origins. The generic construction preserves every source core and makes
  fresh directions disjoint from ordinary ones before taking their union.
- The predicate is the actual `ProximityGap.mcaEvent`: one support S has size
  at least `(1-radius)*n`, the scalar projection agrees with a codeword on S,
  and **no joint codeword pair agrees on that same S**. Neither a global
  non-proximity condition nor a decoder-only substitute is used.
- The radius is exactly `313174699/1073741824` in NNReal. Its support threshold
  is proved to be **760567125**, one larger than each certified source core
  **760567124**. Source p and q satisfy the actual production code degree
  bound; the core is large enough to pin both component polynomials.
- `mca_error_lower` embeds the shared pair into the actual two-row WordStack
  and proves error at least `1073741828/P`. `security_exceeded` proves this
  exceeds **1/2^128** using exact arithmetic. It does not silently substitute
  a rounded scalar budget or a different security parameter.
- `delta_star_upper` concludes exactly
  `mcaDeltaStar productionCode (1/2^128) <= 313174699/1073741824`.
  The referenced ledger defines delta-star as the supremum of good radii
  in [0,1] for this same MCA error. The bad-radius monotonicity conversion
  justifies a non-strict upper bound; it does not assert equality or safety
  at this radius.

## Assumptions, provenance, and proof boundary

The assembly has no section variables or mathematical premises on its final
theorems. Its field instance is constructed from the existing certified
`prime_P`. The selected core owner is an explicit finite choice with a proved
membership fact; overlap compatibility and all generic assembly hypotheses
are discharged by concrete seed, locator, allocation, cardinality, and field
arithmetic lemmas. The generic assembly's hypotheses have not been retained
as assumptions of the final theorem.

I inspected the retained successful kernel log: all six exported axiom reports,
including `many_events` and `delta_star_upper`, list only **propext,
Classical.choice, Quot.sound**. I independently recomputed hashes of the
assembly, all five direct imported source files, and the log, and all match
the successful receipt in the assembly agent receipt, then the combined `kernel_receipt.json` retained here. The reviewed
assembly SHA256 is
`d67ea412ec6b56a68f023cb899564b0b1180a56c5a172b4ac2bf9abcb6894c25`.
No `sorry`, extra `axiom`, unsafe definition, or hidden section assumption is
present in the assembly. Compilation itself was performed by the assembly/root
lane, not repeated during this semantic audit.

The conclusion may now be described as a kernel-checked numerical upper bound
for the concrete production rate-one-half MCA threshold, subject to preserving
the verified build receipt. This does **not** formalize the separately reviewed
arbitrary-four-source optimality or new first-step branch arguments. It does
not prove the matching lower bound, exact threshold, all challenge rates, or
the grand-prize result.
