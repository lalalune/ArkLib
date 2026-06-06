# Current ArkLib residualized tree audit (2026-06-06)

This is the current source-of-truth index for the proximity-prize audit notes in this ArkLib
checkout. Older notes in this directory preserve campaign history and may mention old raw-hole line
numbers such as `Curves.lean:1819`; treat those as historical breadcrumbs, not current locations.

## Current shape

The live ArkLib tree mostly exposes unfinished work as named residual APIs, explicit hypothesis
bundles, documentation-only roadmap notes, or opaque stand-ins. The old "single raw sorry at a line"
framing is no longer accurate for the BCIKS20/FRI/STIR/WHIR proximity-gap campaign.

## Current tracking issues

Use focused GitHub issues as the active work index:

| Area | Issue |
|---|---|
| Umbrella proof-gap audit | #6 |
| BCIKS20 correlated agreement residuals | #7 |
| BCIKS20 Claim 5.7 residuals | #8 |
| BCIKS20 Appendix-A Hensel residuals | #9 |
| Hab25 Johnson-range MCA residuals | #10 |
| ABF26 Lemma 4.6 hard direction | #11 |
| GG25 line-decodability multi-gamma coverage | #12 |
| LogUp Protocol 2 residuals | #13 |
| Batched FRI query soundness | #14 |
| Duplex-sponge Fiat-Shamir placeholder | #15 |
| ToyProblem KoalaBear placeholder | #16 |
| SendWitness knowledge-soundness placeholders | #17 |
| ToyProblem protocol and leaderboard residual anchors | #18 |
| RingSwitching/Binius completeness plumbing | #19 |
| WHIR MCA conjecture placeholders | #20 |
| External coding-theory theorem residual APIs | #21 |
| CS25/BCHKS/BGKS bridge residuals | #22 |
| Stale proximity-prize docs cleanup | #23 |

## Historical notes

The following notes are retained for provenance but are not current inventories:

* `GRIND-LEDGER.md` records the June 5 bottom-up campaign and still contains old
  `Curves.lean:1819` breadcrumbs.
* `integration-2026-06-05/NOTES.md` records an isolated integration attempt and explicitly says the
  old keystone did not close against that base.
* `dispositions/*.md` files are campaign-specific dispositions; prefer the issue list above for
  current ownership and open work.

## Audit commands

Raw proof-hole and placeholder census:

```sh
rg -n --glob '*.lean' '^\s*(sorry|admit)\b|:=\s*(by\s+)?(sorry|admit)\b|by\s+(sorry|admit)\b|\baxiom\s+[A-Za-z_]|opaque\s+[A-Za-z_]' ArkLib
rg -n --glob '*.lean' '^(noncomputable\s+)?(def|structure|class|theorem|lemma)\s+\w*Residual\w*|\b\w*Residual\w*\s*:' ArkLib
rg -n --glob '*.lean' 'opaque\s+\w+|placeholder|stub|TODO|FIXME|named residual|explicit hypothesis|remaining unproven|only remaining|sole residual|single remaining' ArkLib
```

Historical proximity-prize note scan:

```sh
rg -n --glob '*.md' 'Curves\.lean:1819|Agreement\.lean.*11|raw pass|sorry@|admit@|Current ArkLib.*ac6dc78a|arklib-sorry-fixes|Curves\.lean:1288' docs/kb/audits/proximity-prize
```
