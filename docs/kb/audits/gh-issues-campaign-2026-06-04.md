# Audit: GitHub issues campaign (2026-06-04) — issues #1–#4, #222–#233, #450, #480

Status: complete. Companion to `gh-issues-222-224-225-233-verification.md` (which carries the
detailed per-theorem evidence for the four Guruswami–Sudan / InterleavedCode issues).

Scope: branch `gh-issues` (base: campaign tip `a36a4ea9`, a strict descendant of upstream
`main` `c1784658`). All verification commands were run in this worktree; axiom probes accept
only `propext`, `Classical.choice`, `Quot.sound`.

## Per-issue outcome

| Issue | Verdict | Evidence |
|---|---|---|
| #233 `decoder_mem_impl_dist` | RESOLVED UPSTREAM | `dist_le_of_mem_decoder`, sorry-free, axiom-clean (companion audit) |
| #222 `decoder_dist_impl_mem` | RESOLVED UPSTREAM (corrected) | `mem_decoder_of_dist` + necessary `p.natDegree < k` hypothesis |
| #224 GS divisibility | SUBSUMED | `dvd_property` (Basic.lean:884) + recast named lemma, sorry-free |
| #225 `minDist_eq_minDist` | MOOT | InterleavedCode API rewritten; maintainer-confirmed |
| #450 splitNth/foldNth eval lemmas | DONE (this branch) | `59a1c9bf`: `foldNth` def + `polyFold_eq_foldNth` + `eval_eq_sum_splitNth` + the 3 issue lemmas, axiom-clean |
| #480 Basic.lean docs | DONE (this branch, per maintainer redirection) | `ef78352f`: `docs/kb/concepts/oracle-reductions.md` (KB page, not docstrings — #433-safe); lint green |
| #2 commitment schemes | DONE | Box 1 (security defs) live upstream in `CommitmentScheme/Basic.lean`; box 2 done here: `76c2c944` states `ProtocolSpec.BCSTransform` (fully general) + `OracleReduction.BCSTransform` (phases-as-inputs; honest deferral notes), zero sorry |
| #3 sumcheck & Spartan | CHECKBOXES PROVEN; lift blocked on #433 | All three boxes sorry-free + axiom-clean as `Simple.*` (SingleRound.lean L898/L1000/L1037). Canonical lifted variants sorryAx-tainted via `OracleVerifier.liftContext` (see design gaps). Spartan defs blocked on the same |
| #1 IOR composition | DEFS DONE; proofs advanced to structural ceiling | `toFun_next` of `StateFunction.append` proven (`d4db5576`); 7 new sorry-free infrastructure lemmas (`dc52d2ea`, `2c1cc5b9`); remainder blocked on documented design gaps below |
| #4 Merkle trees | BATCH COMPLETENESS + BINDING PROVEN; RO layer open | `2ab8b7bf`: Batch/Extraction/Hiding modules (+475 lines, zero sorry); see VCVio findings below |

Sorry deltas vs upstream `main` on issue-relevant files (campaign base + this session):
SingleRound 21→12, Append 19→11, Spartan 8→3, SeqCompose 9→0, Implications 13→10,
Security/Basic 3→0, Rewinding 2→0, Sequential/General 3→0, BCS 2→0, Fold 5→0.

## Statements found FALSE or unprovable-as-stated (do not "prove"; need upstream statement fixes)

1. `Sumcheck...Simple.oracleVerifier_eq_verifier` (SingleRound.lean:594) and consumer
   `oracleReduction_eq_reduction` — the compiled oracle verifier guards on the *oracle
   statement* polynomial's D-sum; the plain verifier guards on the *prover message*
   polynomial. Equal only for honest provers (Finding-13 / eq-510 family; already de-tainted
   out of all real proofs).
2. `Simple.verifier_rbrKnowledgeSoundness` (L1031) and `Security.verifier_rbrKnowledgeSoundness`
   (L1524) — false at error `deg/|R|`: a malicious prover wins with probability 1 because the
   plain verifier never checks the message against the oracle (constructive attack in the
   2026-06-04 analysis; same root cause as item 1).
3. `StateFunction.append.toFun_full` (Append.lean) — unprovable for the conjunction-based
   composite `toFun`: in the S₁-false/S₂-true case, `S₂(last)` may legitimately hold on
   out-of-language input (lucky challenge — rbr soundness bounds this only probabilistically),
   so the demanded `Pr = 0` fails. Composite state function needs a different `toFun`.
4. (VCVio, pinned package) `MerkleTree.Inductive.completeness` is vacuous w.r.t. verification
   success: `NeverFail (….run)` over `OptionT` holds even for wrong-leaf openings, because
   `guard` rejection reifies as the *value* `none`. Adversarially probed. Acceptance-form
   replacements proven in `ArkLib/CommitmentScheme/MerkleTree/Batch.lean`. Worth reporting to
   VCVio upstream.

## Design gaps blocking the remaining sorries (all consistent with the #433 rewrite rationale)

- `OracleVerifier.liftContext` (LiftContext/OracleReduction.lean:48): under-determined — the
  Lens API lacks `simOStmt`/`liftOStmt` oracle-routing fields (commented-out TODOs at
  Lens.lean:63–94, Basic.lean:278–293). The sumcheck lens is a non-invertible virtual
  summation; Spartan's lenses change oracle index types. No restricted equiv-variant serves
  either use-case. Blocks: de-tainting the lifted sumcheck theorems, Spartan's 3 defs, the
  `Simpler` decomposition (4 defs).
- `Implications.lean` lattice: `knowledgeSoundness`/`rbrKnowledgeSoundness` quantify provers
  over the relation's fixed witness types while `soundness`/`rbrSoundness` quantify over
  arbitrary types (KS⇒S, rbrKS⇒rbrS not derivable as stated); SR-vs-plain theorems relate
  unrelated `init`/`impl` pairs; salt theorems have statement holes and Salt.lean itself
  documents an SR-not-preserved counterexample; the OneShot converter needs the upstream
  `IsMonotone` placeholder completed.
- rbr⇒plain telescoping pair (the only legitimately-closable Implications residue): the
  combinatorial backbone is now proven (`exists_flip_of_false_zero_true_last`,
  `exists_challenge_flip_of_false_zero_true_last`, `probEvent_exists_mem_le_sum`,
  `probEvent_exists_le_sum` in RoundByRound.lean; `runToRound_succ`,
  `processRound_challenge`, `fst_map_runToRound_succ_challenge` in Execution.lean — and the
  feared fresh-challenge coupling mismatch was checked and does NOT exist). The remaining gap
  is a probabilistic-monad layer over `OptionT (StateT σ ProbComp)` + `simulateQ`:
  failure-monotone bind, per-round decomposition of full-run marginals, and a
  verifier-run↔full-run bridge. Exact stuck goal recorded in the 2026-06-04 agent ledger.
- `Prover.append_run` + `append_completeness`: blocked on a runToRound split decomposition and
  the upstream-documented commutative-monad obstacle (Append.lean:404–448, "prove after VCVio
  refactor").
- Merkle full extractability (§18.5) + hiding: the deterministic cores are proven
  (`opening_binding`, extraction uniqueness, salted completeness); the missing layer is
  negligible-collision-probability reasoning over the random oracle, absent from VCVio.

## New infrastructure banked (sorry-free, axiom-clean; verified 2026-06-04)

`exists_flip_of_false_zero_true_last`, `exists_challenge_flip_of_false_zero_true_last`,
`probEvent_exists_mem_le_sum`, `probEvent_exists_le_sum` (RoundByRound.lean);
`Prover.runToRound_succ`, `Prover.processRound_challenge`,
`Prover.fst_map_runToRound_succ_challenge` (Execution.lean);
`StateFunction.append.toFun_next` closed (Append.lean);
`ProtocolSpec.BCSOpeningPhase`/`BCSTransform`, `Reduction.bcsMessageOpening`,
`OracleReduction.BCSTransform` (BCS/Basic.lean);
`Polynomial.foldNth` + `polyFold_eq_foldNth` + `eval_eq_sum_splitNth` +
`splitNth_two_eval_add`/`_sub` + `foldNth_two_eval` (SplitFold.lean);
`InductiveMerkleTree` batch/extraction/hiding modules (CommitmentScheme/MerkleTree/).
