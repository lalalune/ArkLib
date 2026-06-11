# #313 front-door wiring map (2026-06-10 evening recon)

Machine recon of every role-named hypothesis surface in the Binius front doors against the
landed composition keystones. Companion to the lane-D front-door table (#313 comment
2026-06-10 ~20:18Z); supersedes its "dischargeable-now" gradings where they conflict.

## Global blockers (the cone does not elaborate on main)

1. `OracleReduction.castInOut`/`castOutSimple` used 8× in
   `BinaryBasefold/CoreInteractionPhase.lean` (:385–:837) but deleted from `Cast.lean` in the
   new-API migration. **FIXED**: ported + new PC/KS transfer lemmas in
   `ArkLib/OracleReduction/CastInOut.lean` (`f0132bbb9`, axiom-clean).
2. `strictSumcheckRoundRelation` / `strictBatchingInputRelation` / `toStrictRelInput` defined
   nowhere (strict surface dropped in the #29 refactor); referenced by FRIBinius/General,
   FRIBinius/CoreInteractionPhase, BBFSmallFieldIOPCS. **Decision** (RingSwitching lane,
   #317 comment 2026-06-11 ~01:58Z): restate consumers on plain relations + the conjoin
   keystone; do NOT re-add strict surfaces upstream.
3. 𝓑-staleness: FRIBinius/General + BBFSmallFieldIOPCS pass `(𝓑 := 𝓑)` into RingSwitching
   declarations that no longer carry it.
4. BBFSmallFieldIOPCS forwards six hypotheses to
   `FullRingSwitching.fullOracleReduction_perfectCompleteness`, which is now unconditional
   (current signature needs only `[IsDomain L] [IsDomain K] hInit hMlnPos hMlnDir`).

## Keystone inventory (all proven, axiom-clean)

- Append PC: `append_perfectCompleteness_msg_proof` (+ unconditional
  `appendToReductionResidual_proof`), `append_perfectCompleteness_challenge`, `_empty`.
- n-ary PC: `seqCompose_pc_oracle_msg'` / `seqCompose_perfectCompleteness_threaded` (msg),
  `seqCompose_perfectCompleteness_challenge_threaded` (challenge).
- Append KS: state-collapse arbitrary-σ (`append_rbrKnowledgeSoundness_keystone_collapse`),
  msg-seam failing-det (`OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton`,
  via the optionization reduction), total-det challenge-seam
  (`append_rbrKnowledgeSoundness_keystone_subsingleton_challenge`), failing-det 0-round tail,
  **NEW** challenge-seam failing-det
  (`OracleVerifier.append_rbrKnowledgeSoundness_failingDet_subsingleton_challenge`,
  `AppendRbrKnowledgeFailingDetChallenge.lean`, `15cdd5c5c` — the optionization reduction is
  seam-direction-agnostic, so this is the msg-seam capstone with the keystone swapped).
- n-ary KS: `OracleVerifier.seqCompose_rbrKnowledgeSoundness_failingDet`.
- Relation strictness: `Verifier.rbrKnowledgeSoundness_conjoin`.
- RingSwitching round completeness: `iteratedSumcheckRound_perfectCompleteness_residual_holds`
  (closes the only missing-math item in the lane-D table).
- Templates: `RingSwitching/RbrKnowledgeWiring{,Full}.lean` (the #29 end-to-end KS wiring),
  `RingSwitching/General.lean` EndToEndCompleteness section, `SumcheckLoopPC.lean` (n-ary
  recipe incl. the whnf-loop trap notes).
- Lens transfers (for FRIBinius): `liftContext_perfectCompleteness`,
  `liftContext_rbr_knowledgeSoundness`.

## Per-front-door status

| Item | Surface | Status |
|---|---|---|
| A1 | BB/General:117 completeness | mechanical given C3 (challenge-seam PC keystone; h₂ = proven `queryOracleProof_perfectCompleteness`) |
| A2 | BB/General:149 rbr-KS | unblocked by the NEW keystone; needs determinism bricks + binder additions (`[Subsingleton σ] hInit hInitNF`) |
| B1/B2 | FRIBinius/General:191/:237 | blocked on blockers 2–3 restatement + lens instances (`LiftContextCoherent`, `Extractor.Lens.IsKnowledgeSound` for `sumcheckFoldExtractorLens`) + determinism bricks |
| C1 | BB/CoreInteractionPhase:918 | castInOut PC transfers landed; remaining = relation-family Fin reconciliation along the block tree |
| C2 | :1039 | n-ary failing-det keystone landed; needs fold/relay/commit verifier determinism bricks (pattern `BatchingDeterminism.lean`; note `FoldDet*.lean` are matrix determinants, unrelated) + castInOut KS transfers (landed) |
| C3/C4 | :1137/:1174 | mechanical given C1/C2 |
| D1 | BBFSmallFieldIOPCS:765 | restate over the now-unconditional upstream; `hRounds` discharged exactly by `iteratedSumcheckRound_perfectCompleteness_residual_holds` |
| D2 | :832 | four hyps have 1:1 landed dischargers (`sumcheckLoop_rbrKnowledgeSoundness`, `coreInteraction_rbrKnowledgeSoundness_wired` (one error-form mismatch: unit placeholder vs `2/|L|` — prove monotonicity or rewrite), `batchingCore_…_wired`, `fullOracleVerifier_…_wired`); needs added binders |

All BinaryBasefold leaf completeness/KS theorems are genuinely proven (Steps/Fold:162/:1743,
Relay:146/:440, Commit:148/:519, FinalSumcheck:141/:1892).

## Discharge order

① castInOut port + transfers — **DONE** (`f0132bbb9`). ② challenge-seam failing-det keystone —
**DONE** (`15cdd5c5c`). ③ Binius verifier determinism bricks. ④ strict-surface restatement on
plain relations + conjoin (decision recorded above). ⑤ C1→C3, C2→C4. ⑥ A1/A2. ⑦ B/D
restatements (BBFSmallFieldIOPCS coordinated with the ExtractMLP migration lane — that file is
hot).
