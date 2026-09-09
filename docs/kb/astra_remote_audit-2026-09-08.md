# Remote research audit — 2026-09-08

Read-only audit against local `codex/proximity-astra-20260904` at `7941e60694f77346c0e375548737f8301695b8b3`. Read root AGENTS.md, ProximityGap AGENTS/CLAUDE.md and current programme. No remote write, checkout, merge, build or downloaded executable. Origin refs were refreshed before the audit; exact upstream review refs were fetched during it. GitHub metadata and source diffs below were read live with `gh api`.

## Exact current heads and dates

| Ref | SHA | Commit date / status |
|---|---|---|
| origin/codex/proximity-astra-20260904 | `7941e60694f77346c0e375548737f8301695b8b3` | 2026-09-06 17:03:29Z; identical to HEAD |
| origin/research/proximity-prize | `54007b004040a9cd0964dcb0a2413e86bc60ae8d` | 2026-08-15 23:01:50Z; no commits outside HEAD |
| origin/main | `8e2fc19130e2fea9e175c52b0953b88804b8f333` | 2026-08-15 02:39:20Z; 7 commits outside HEAD |
| origin/codex/tuple-equalities-issue2 | `cf5c691bb4c021f66a0da5185d88a6d0dd955f69` | 2026-09-05 19:52:37Z; 129 outside HEAD, largely upstream library history |
| **Verified-zkEVM/ArkLib main** | **`8d7e758b5c4421711358595870ff7fbcee2a3a9f`** | **2026-09-08 16:26:05Z**, latest live API read; oracle-reduction completeness repair #887 |

Fork `lalalune/ArkLib` pushed_at is 2026-09-06 17:03:32Z. Its issues API with `since=2026-09-06T00:00:00Z` returns **zero** items. Latest fork issue/PR update remains PR #543 on 2026-08-25 19:17:54Z. Its parent/source is `Verified-zkEVM/ArkLib`; checking only origin would miss current work there.

## Highest-value fresh upstream work

[Upstream tracker #859](https://github.com/Verified-zkEVM/ArkLib/issues/859), updated **2026-09-08 01:52:13Z**, is explicitly OPEN. Its target is BCHKS25 Theorem 4.6, arbitrary polynomial curves with the same-agreement-set quantifier and exact finite exceptional bound. It does not claim the production threshold is proved.

All of the following PRs remain OPEN/unmerged. Heads belong to `quangvdao/ArkLib`. They are source/API opportunities, not independently replayed kernel receipts in this audit.

| PR / branch | Exact head | Useful slice |
|---|---|---|
| [#865](https://github.com/Verified-zkEVM/ArkLib/pull/865), `quang/bchks-curve-contract` | `272fe77c77fc0ae18506fb245983af8c01b23ef0` | Same-set MCA and exceptional-set API; updated 2026-09-08 00:00:58Z |
| [#866](https://github.com/Verified-zkEVM/ArkLib/pull/866), `quang/bchks-factorization-review` | `4e413e3ad9f5373a1223ca4dbdd08d60471d5e4c` | Content-aware fraction-field/Frobenius factorization |
| [#867](https://github.com/Verified-zkEVM/ArkLib/pull/867), `quang/bchks-interpolation-counts` | `d2fe9538beb54b414b2da3b0fd4f717b3b353136` | Exact symbolic support/constraint counts and rounded surplus |
| [#873](https://github.com/Verified-zkEVM/ArkLib/pull/873), `quang/bchks-sprint-algebra-20260907` | `0ef306fc6a430e679acfde79b304eeec0b1e4946` | Both bivariate factor-degree sums |
| [#875](https://github.com/Verified-zkEVM/ArkLib/pull/875), `quang/bchks-sprint-weighted-degree-20260907` | `0ffecb528a8a63eb9522b68d7061e0b671339a47` | Weighted product/divisor degree budgets |
| [#877](https://github.com/Verified-zkEVM/ArkLib/pull/877), `quang/bchks-fraction-field-resultant-20260907` | `df6c2ad50a63c7896cf732cc2735590162455736` | Fraction-field resultant/separability certificate |
| [#878](https://github.com/Verified-zkEVM/ArkLib/pull/878), `quang/bchks-resultant-degree-20260907` | `cb7f88959ff9fa8246976c7892807dca8f1d94f1` | General resultant-degree bounds |
| [#882](https://github.com/Verified-zkEVM/ArkLib/pull/882), `quang/bchks-fraction-field-hensel-20260907` | `22da7b6d07bc59853d2999544a6b60a1df6d900d` | Hensel root existence from fraction-field separability |
| [#888](https://github.com/Verified-zkEVM/ArkLib/pull/888), `quang/bchks-universal-numerator-20260908` | `8f589831261a5ca84231f3034c92995c8447e545` | Universal numerator recurrence and ring-map naturality |
| [#890](https://github.com/Verified-zkEVM/ArkLib/pull/890), `quang/bchks-numerator-setup-20260908` | `d1c9a8937aa220d459374995fcb98f7b0f883967` | Weakened native cleared-numerator setup; updated 2026-09-08 02:12:35Z |

API inspection of #865:

- `ArkLib/Data/CodingTheory/ProximityGenerator/Basic.lean`: `CoreDefinitions.not_isMCA_iff_forall_exists_codewords`, `not_isMCA_univariatePowersGenerator_iff`, `univariatePowersGenerator_one_eq_affineLineGenerator`.
- New `ArkLib/Data/CodingTheory/ProximityGenerator/ExceptionalSet.lean`: `mcaError_le_of_exists_exceptional_set`, `mcaError_le_of_exists_exceptional_set_codewords`.
- Error conclusion is `mcaError G MC δ ≤ ENNReal.ofReal (B / Fintype.card S)`. Hypothesis order is `∀ U, ∃ E, ∀ x ∉ E, ∀ qualifying T, ∃ codewords agreeing on T`. **E cannot depend on T; codewords can.** Module alphabets work; only seed type must be finite/nonempty in the generic bridge. This does not establish a Reed–Solomon exceptional bound.
- Five public declarations have standard-axiom reports according to the PR, and the author reports full validation at its exact head. This audit inspected source, not hosted Lean execution. PR API currently gives base `e029c9f5d4e06e30f3a44079146ecbe58d413e0c`; PR prose lists older original base `a527b514...`, so use the live base/head and rebuild an eventual integration.

#867 is independent of #865/#866 and adds `SymbolicInterpolationSupport.lean`, `SymbolicInterpolationParameters.lean`, `SymbolicInterpolationSurplus.lean` under `ArkLib/Data/Polynomial`. Its support is `j < dy`, `i+k*j < dx`, `j+h < dz`; its exact size retains truncated natural subtraction. It proves counts/arithmetic, not construction, rigidity or MCA.

[Latest #859 checkpoint](https://github.com/Verified-zkEVM/ArkLib/issues/859#issuecomment-5577893143) links pushed integration `quangvdao/ArkLib@83352bc58d93029cacdc30f8ff4bd5db5cebf432`, with 14 files +1574/-58 over prior `4fd6cf7692dbfd3b4c979a752385a5761f6c0796`. Author reports full validation/no new trust debt. It includes additional primitive/full-degree specialization, a native xi adapter, residual scaling and exact-root identification. **Still open:** choosing suitable coefficient-span pairs for every relevant irreducible factor, aggregate primitive/leading/derivative-resultant budgets, weighted universal numerators/full native sequence bridge, useful-factor rigidity, original-candidate Frobenius transport, and final all-set exception accounting. Donor provenance is public proximity-prize #45/#72; no claim here of a fresh audit of that entire donor repository.

## Fork PRs: check contents before importing

- [#542 CLM-043](https://github.com/lalalune/ArkLib/pull/542), head `63cfd25644ad3f98c134212f647bc10e7ee48d5a`, still open, updated 2026-08-25 06:38:19Z. **All 8 PR file blobs exactly match HEAD**; imported at local commit `390c9e0f9` on September 4. No integration needed. Local work already improves its remainder constant 87 to 24; the principal U term remains unbounded.
- [#543 wall-floor/value pins](https://github.com/lalalune/ArkLib/pull/543), head `0852a1a21a95d9cb224f3e56bc89850a9bf6f021`, 9 commits/10 files. Nine files absent locally and `OverdetIncidenceMaxClosedFormExt.lean` differs. Scope is mechanical pins m=51..200 and a proposed general-depth wall-floor formula. **Do not import as a structural theorem:** outstanding review finds finite probes mislabeled an all-d/all-m proof, an invalid depth-four intermediate equality, and a false claim that the naive pattern agrees at depth three. The visible current source still contains those problems. Only `summarize` check is visible on its exact head, not a Lean build receipt. Low priority for production progress.

## Origin branch content outside HEAD

167 actual origin branches (plus symbolic origin/HEAD); 74 branch tips have outside commits, with 234 unique outside commits overall. Most are a nested July 10–11 G110/G114/G133/G137/G138…G204 chain, so the count is misleading.

- `origin/codex/g204-two-coset-vanisher` ends at `1091c78e0d8c068c32f1ca81a67bbeb832100fa5` (2026-07-11 19:42:24Z), 74 outside commits. Of its 73 changed paths since merge-base, 16 are blob-identical in HEAD, 55 source paths are absent, and only ArkLib.lean/DISPROOF_LOG differ otherwise. Earlier branch variants have duplicate histories; blanket merge is unsuitable.
- Concrete reusable candidate: missing `_G203TwoCosetTwistedGenerators.lean` and `_G204TwoCosetVanisher.lean`. Inspected G204 source constructs nonzero Ψ for `x^t=α`, `(x-c)^t=β`, with multiplicity ≥D and degree ≤`D-1+2*t*(B-1)`, under `1≤D,B`, `DB≤t`, `2D≤B²`, `tB≤p`, and nonzero c,α,β. It prints three axiom reports but they were **not replayed here**. A focused extraction/build can test this brick; it does not supply the square-root production bound.
- Other missing sources include depth-four composite census, primitive packet parity, deletion energy, covariance refutations, and Mobius/Stepanov normalization. This audit did not certify all 55; they are concrete unintegrated source inventory, not 55 accepted results.
- Main's three old research commits are `620360d959677416a420f51a1bde402e2bb32975`, `490e03a64feb89cc1d2b699fdd04fa9aaec6116a`, `458b5e2a0217f7b3e1a2c9de0cb5e109d03d37eb`: G246 n=16 Krylov obstruction and corrected full-height rank probes. Four Python probes plus four output files are absent. Remaining divergence is CI history; `.github/workflows/retry-transient.yml` is absent, 25 of main's 35 touched files already match HEAD.
- `origin/codex/shard-lean-ci` at `616482401c4f3ced268c8948f9568135debd6efc` is old closed/unmerged PR #513, not a current proof contribution. Its workflow/stage script should not be pulled into this research run.
- Tuple branch's 129 outside commits include extensive upstream coding-theory/library modernization through September 5; branch tip itself only fixes Fin tuple equalities. Inspect current upstream main in isolation rather than merging this unrelated branch.

## Recommended next action

Fetch exact upstream main and PR #865 into isolated audit refs, inspect their canonical MCA/threshold definitions against the current campaign, then choose narrowly compatible statements to adapt. Preserve the current numerical construction and rebuild any adaptation. #867 and the coefficient/rigidity stack are genuine later formalization work, but none presently narrows the written `[268435457,313174699]/2^30` bracket or closes its numerical Lean instantiation.
