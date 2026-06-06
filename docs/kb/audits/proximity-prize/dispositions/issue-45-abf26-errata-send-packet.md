STATUS: SEND-READY — repo-side packet complete; external email send still requires an
authenticated mail channel.

# issue-45 — ABF26 errata packet for Proximity Prize judges

Tracking issue: lalalune/ArkLib#45
Target channel: `proximityprize@ethereum.org`
Local source draft: `/home/shaw/ethereumroadmap/research/proximity-prize/abf26-feedback-for-judges-draft-2026-06-04.md`
Local attachment source: `/home/shaw/ethereumroadmap/research/proximity-prize/abf26-c38-erratum/abf26-c38-erratum.pdf`

This note is the in-repository send packet for the ABF26 / Proximity Prize errata
message.  It preserves the exact recipient, subject, message body, attachment list,
and evidence map so the external send can be performed without reconstructing the
formalization context.

## Send status

Not sent from this workspace.  The current agent has GitHub and repository access, but
no authenticated email-sending surface.  Closing this issue should require independent
evidence that the message below, with the listed attachment, was actually delivered or
submitted through an approved Proximity Prize feedback channel.

## Outbound message

To: `proximityprize@ethereum.org`
Subject: ABF26 / Proximity Prize errata from ArkLib formalization campaign

Body:

```text
Hello Proximity Prize organizers,

During a Lean 4 formalization campaign for ABF26 (ePrint 2026/680) in ArkLib, we found
several paper/prize-condition issues that look worth resolving before the prize
conditions are finalized.  The high-impact items are below; each is backed by
machine-checked statements, counterexamples, or audited residuals in the ArkLib fork.

1. Section 4.5 MCA conjecture is referenced but not rendered in the ePrint PDF.
   The TeX source contains the MCA conjecture inside an \ignore{} block, while the
   rendered 2026/680 PDF has no visible Section 4.5 statement.  Downstream artifacts
   can therefore cite a conjecture that is present only in source.

2. Corollary 3.3 needs a real Johnson/Guruswami-Sudan refinement step.
   The formalization found that the literal derivation from Theorem 3.2 to the
   asymptotic radius 1 - sqrt(1 - delta) and the 1/(2 eta rho) constant silently
   switches regimes; the discrete Johnson precondition fails at the boundary.

3. Table 1 row 3 appears to carry the wrong regime annotation.
   The n^{Omega(1)} / |F| lower-bound row is near capacity, while the row text says
   "delta below the unique decoding radius"; below UDR the existing rows give the
   O(n) / |F| behavior.

4. Theorem 4.12 constants are inconsistent in the ePrint text.
   The general statement uses the shifted multiplicity terms m + 1/2, while the
   Section 6.3.1 numeric instantiation drops those shifts.  The two printed formulas
   do not match.

5. A natural black-box counting proof route for Theorem 4.21 is false.
   ArkLib contains a formal counterexample to the per-position double-coverage route:
   a single shared missed position defeats the count for arbitrarily large lists.
   A faithful proof must use Guruswami-Sudan interpolation structure.

6. Lemma 2.17 / Theorem 2.18 rate conventions need an explicit worked example.
   Under the natural finrank/n reading the statement is false for alphabet F^s,
   s >= 2.  The paper-faithful rate k/(s n), plus a nontriviality hypothesis, matches
   the checked repair.

7. Lemma 4.6's "identical proof for F-additive codes" footnote hides a real
   joint-stack uniqueness step in the epsilon_mca <= epsilon_ca direction below UDR.

8. The Section 6.4.1 / CS25 bridge has two sign/boundary hazards that are now checked
   in ArkLib: the CS25 deep-hole combiner is z = -p(a), and the boundary
   E(L0) = epsilon q needs a strict margin rather than a non-strict count.

I have attached the separate C3.8 erratum note as a compact worked example of the
machine-checked feedback style.

Best,
Shaw
```

Attachment:

* `abf26-c38-erratum.pdf` from
  `/home/shaw/ethereumroadmap/research/proximity-prize/abf26-c38-erratum/abf26-c38-erratum.pdf`

## Evidence map

* Section 4.5 source/PDF mismatch:
  `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`
  records that the MCA conjecture sits inside an `\ignore{...}` block in the current
  TeX source, while `ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean`
  carries the conjecture as a source-faithful `Prop` with the same caveat.
* C3.3 Johnson switch:
  `ArkLib/Data/CodingTheory/JohnsonBound/Family.lean` contains the repaired real
  analysis and boundary discussion; `docs/kb/audits/proximity-prize/dispositions/issue-49-johnson-family.md`
  records the disposition.
* Table 1 / Theorem 4.12 constant issues:
  `ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean` records the BCHKS25
  Johnson-range surface and its relationship to the Grand MCA lower witness work.
* Theorem 4.21 black-box counting failure:
  `ArkLib/Data/CodingTheory/ProximityGap/LineDecodingRefutation.lean` and
  `ArkLib/Data/CodingTheory/ProximityGap/LineDecodingCounting.lean` record the
  counterexample route; the current issue tracker carries the repaired multi-gamma
  coverage work under #12.
* Lemma 2.17 / Theorem 2.18 rate convention:
  the GK16/CZ25 folded-RS and subspace-design work is tracked in the #53 closure
  path and its upstream-PR bucket #44.
* Lemma 4.6 F-additive adaptation:
  `ArkLib/ToMathlib/L46GSLowerBound.lean` and `ArkLib/ToMathlib/L46DiffStackRS.lean`
  isolate the GS-witness route and the joint-stack uniqueness issue.
* CS25 sign and boundary hazards:
  `ArkLib/ToMathlib/CS25DeepHole.lean`,
  `ArkLib/ToMathlib/CS25Claim3.lean`,
  `ArkLib/ToMathlib/CS25Claim3Counting.lean`, and
  `ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean` document the checked
  sign convention and strict-boundary arithmetic.

## Verification

This is a documentation-only send packet.  The repository-side verification is that
the tracked packet exists and still points to the supporting evidence:

```sh
test -f docs/kb/audits/proximity-prize/dispositions/issue-45-abf26-errata-send-packet.md
rg -n 'proximityprize@ethereum.org|ABF26 / Proximity Prize errata|Not sent from this workspace' \
  docs/kb/audits/proximity-prize/dispositions/issue-45-abf26-errata-send-packet.md
```
