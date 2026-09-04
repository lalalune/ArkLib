# Live upstream update: 68.03 is now the baseline

During the final remote check on 2026-09-04, the official companion HEAD
advanced from `b34c0131cfa36b51111521541d7d3e35c8791082` to
[`032154395c51fd6f77715a7f42d9a987ab9fb48a`](https://github.com/proximity-prize/proximity-prize/commit/032154395c51fd6f77715a7f42d9a987ab9fb48a).
It is one new commit, titled `Validate submission dde863e1-2396-4ffd-8453-dc7fd29bbba7`,
co-authored by BitWonka and timestamped `2026-09-04T22:08:00Z`.

The [live companion leaderboard](https://better.codes/) now displays **68.03
to 116.13 bits**, with BitWonka's promoted 68.03 lower submission. Its lower
solution exports `ProtocolClaim 6803 10340095 33554432`. Therefore our earlier
68.03 arithmetic candidate is **not a new record**. Its independently checked
theorems remain valid, but any further improvement must exceed the new baseline.

The comparison changes 13 files, all inside `ProximityPrize/SubmissionLower`.
No benchmark target, dependency manifest, upper submission, or verifier rule
changes in this commit. All 13 changed files were downloaded at the pinned
commit and their Git blob hashes checked. Their combined size is 3916257 bytes.
The old source snapshot was preserved for reproducibility.

## What the new proof adds

The new proof has substantial overlap with the degree-accounting direction
we were investigating:

- `ChainAmort` sums decreasing left R-degree costs along a derivative chain,
  proves superadditivity, and can combine the per-factor tails with the chains.
- `ChainGroupMaj` gives a closed-form group bound depending on slope and
  Y-degree. The fixed gcd and residual quotient share the original B slope
  budget through `QB=H*Q`.
- The fixed-stage complement now incorporates chain groups and the residual
  count **at the actual universal-child flag**, rather than maximizing those
  terms separately. This retains more correlation than our simpler shared-chain
  aggregate bound.
- There is an additional phase source and a repacked sparse certificate layout
  with `PackedLocatorRunsA` through `D`, `PackedLocatorChecksA/B`, and a new
  `PackedLocatorTail3` closure.

The upstream root parameters largely match our earlier candidate, but use
`LB=14915`, `LT=6680`, and selected total cap 6677. Its scalar interpolant uses
`m=97`, Y cap 133, slope 29, and list budget `5224816755`. The new correlated
fixed allowance is `273301903386687639`; it already contains chain and residual
charges, so it must not be compared directly with our regular-only phase cap.
Adding its fixed tails gives the stated ledger `273373097646796867`.

Our weighted-derivative Y shrinkage and the checked natural-number identities
remain separate artifacts. They should be compared against the new group bounds
where they help, not described as a newly verified companion score.

## Next error cell: necessary 68.04 checks

An exact integer score check shows that the first candidate error cell for
68.04 is **80791**, with radius `10341375/33554432`. Cell 80790 fails the same
centibit check. The new
[`astra_companion_6804_seed.py`](../../scripts/probes/astra_companion_6804_seed.py)
records the following interpolation starting point:

| Kernel | m | L | slope | Y cap |
|---|---:|---:|---:|---:|
| A | 99 | 217071 | 30 | 136 |
| B | 111 | 17568 | 33 | 153 |
| C | 270 | 130000 | 81 | 373 |
| T | 194 | 6922 | 60 | 268 |

All four signed kernel nullities are positive. The T nullity exceeds its
total-degree-two quotient dimension by `194725418`. A scalar interpolant
`(m,Y,s)=(99,136,30)` has nullity `1496153`, mixed degree `2121253094 < p`, and
list budget `5529601254`. The ordinary mixed-characteristic endpoint at support
caps `(R,Y)=(30,136)` is `2113404958 < p`.

These are necessary gates only. **No 68.04 phase envelope, combined count, full
Lean proof, or verifier acceptance has been established.** In particular, the
68.03 phase receipts and its ordinary-gate certificate cannot be relabeled as
68.04 proofs. The next work is to evaluate the new correlated ledger with
retuned sources and then port the resulting proof at the current official pin.

The user's ArkLib remote main and research branches remained at
`8e2fc19130e2fea9e175c52b0953b88804b8f333` and
`54007b004040a9cd0964dcb0a2413e86bc60ae8d`, respectively, during this check.
