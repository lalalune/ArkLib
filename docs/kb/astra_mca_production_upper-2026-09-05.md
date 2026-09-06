# A kernel-checked production MCA threshold upper bound

The four-deletion construction now proves, in Lean 4.30.0-rc2,

```text
epsMCA(C, 357913942/2^30) >= 1073741828/P > 2^-128
mcaDeltaStar(C, 2^-128) <= 357913942/2^30,
```

where C is the rate-one-half Reed-Solomon code on the certified power domain
of length 2^30 and P is the existing certified production prime. The proof
constructs the basis, projects its residual rows, builds the indexed supports,
proves the actual MCA events, and applies the repository's probability and
threshold lemmas. **This is an upper bound for one exact production code.
The exact threshold and the grand prize problems remain open.**

This bound is one Hamming step weaker than the earlier
[computational bound](astra_mca_production_count-2026-09-05.md)
357913941/2^30. It does not improve that number. Its advance is a complete
kernel-checked construction and threshold argument without a billion-point
enumeration.

The later [common-root relocation construction](astra_mca_root_relocation-2026-09-06.md)
gives the stronger written bound `355676980/2^30`, with independent exact
controls. That construction is not yet Lean-formalized; this page records
the earlier kernel-checked theorem.

## Exact code and statement

The [production upper-bound module](../../scripts/probes/astra_mca_production_upper.lean)
uses `ReedSolomon.code productionEmbedding (2^29)` with
`productionEmbedding i = g^i`. The imported certificate proves

```text
P = 365375409332725729550921208179070755120141565953
g = 303645430271030343624574566109998498685964493478 in ZMod P
orderOf(g) = 2^30.
```

`production_code_iff` proves that membership is exactly evaluation of a
polynomial of natural degree at most 536870911 at these powers. This is the
predicate in the existing `KKH26.evalCode` definition. The separate
[KKH26 adapter](../../scripts/probes/astra_mca_kkh26_upper.lean) states their
equality and the upper bound directly for that existing definition, unchanged.
This adapter and the unchanged KKH26 dependency chain passed the ArkLib CI
job at commit `450cb330ef2101b0daed1e41b597ad361f96a140` in
[run 33990217749](https://github.com/lalalune/ArkLib/actions/runs/33990217749).

## Constructed supports and bad scalars

The [production event module](../../scripts/probes/astra_mca_production_events.lean)
uses the same partition and coefficient vectors supplied by
`production_scalar_projection`. The three core sizes are 715827882,
715827881, and 715827881. For every slot, the proof chooses a core subset of
size 715827881 and inserts that slot's coordinate. The nonzero denominator
proves it is a new point, so the resulting support has size 715827882.

This is exactly `(1-357913942/2^30)*2^30`. On the pulled-back indexed support,
the received affine combination agrees with an actual codeword while the
original pair has no joint codeword explanation. The
[event bridge](astra_mca_event_bridge-2026-09-05.md) proves this using the
repository's literal `mcaEvent`, on that same support.

`production_many_events` provides one pair of received words and a finite set
of exactly 1073741828 distinct bad scalars. Each scalar can have its own
support. The theorem does not assume a bad-scalar count or perform an
enumeration.

## Probability and threshold

`production_mca_error_lower` applies the existing
`epsMCA_ge_card_div_of_mcaEvent_set` theorem to that constructed set. Exact
arithmetic gives 1073741828/P > 2^-128. Finally,
`mcaDeltaStar_le_of_bad` turns the strict error inequality into
`production_delta_star_upper` using the actual supremum-based threshold
definition. No named analytic residual is assumed.

## Verification

The local chain has 81 checked named reports: the preceding 69 construction
reports, two general event bridges, six production-event theorems, and four
probability/code/threshold theorems. All use only `propext`,
`Classical.choice`, and `Quot.sound`, with no diagnostics in the new sources.
The KKH26 adapter adds two reports, both checked in CI. The complete chain
therefore has 83 verified reports on the ArkLib pin. The separate companion
job checks the 69-report construction chain on Lean 4.32.2; it does not check
the ArkLib event, threshold, or KKH26 modules on that pin.

Run from the matching ArkLib Lake environment:

```sh
bash scripts/lake-locked.sh build ArkLib.Data.CodingTheory.ProximityGap.KKH26WitnessSpread ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrizeShapePrimeP30
bash scripts/check-mca-production-basis.sh /tmp/mca-proof-lib
bash scripts/check-mca-event-bridge.sh /tmp/mca-proof-lib
```

The [second helper](../../scripts/check-mca-event-bridge.sh) compiles the
event bridge, production events, upper bound, and KKH26 adapter in order.
Its optional second argument supplies a compiled ArkLib library path.
The [workflow](../../.github/workflows/proximity-strip-proof.yml) audits all
83 reports on the ArkLib pin; the companion pin covers the separate 69-report
Mathlib-based construction chain.

Both jobs succeeded in
[run 33990217749](https://github.com/lalalune/ArkLib/actions/runs/33990217749)
at `450cb330ef2101b0daed1e41b597ad361f96a140`. Including the workflow's 27
other auxiliary reports, its standard-axiom audit accepted 110 reports on
the ArkLib pin and 96 on the companion pin. In particular,
`AstraMcaKkh26Upper.first_prime_rate_half_delta_star_upper` passed with only
`propext`, `Classical.choice`, and `Quot.sound`. The new proof sources passed
the workflow's diagnostic gate; existing dependency warnings remain separate.
Independent mathematical review and the matching universal lower bound
remain open.
