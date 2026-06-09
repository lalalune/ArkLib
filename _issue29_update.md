### Append keystone: router-collapse infrastructure now `sorry`-free (collaborative)

The `simulateQ`-routing-collapse layer that the append/`toVerifier` completeness keystone needs is now proven and builds clean in `Append.lean` (pushed `f8f4b3928`):

- **`router1_collapse` / `router2_collapse`** — `(simOracle2 oSpec oStmt tr.messages) ∘ₛ router_k = ` the component `simOracle2` over the first/second sub-transcript (and, for `router₂`, over `mkVerifierOStmtOut V₁.embed V₁.hEq oStmt tr.fst`, i.e. `V₁`'s reconstructed output oracle statements).
- **`simulateQ_emitOStmt₂Query`**, **`emitOStmtQuery{Inl,Inr}_simulateQ`**, **`simulateQ_emitMessage{Inl,Inr}`** — the per-query characterizations.
- **`messages_{fst,snd}_heq` / `challenges_{fst,snd}_heq`** — the transcript seam-split `HEq`s.

The append-completeness residual `reductionAppendPerfectCompletenessResidual_of_message` (`AppendPerfectCompletenessMsg.lean`) is also `sorry`-free, discharging `appendPerfectCompletenessResidual`.

**Two technical cruxes worth recording (reusable):**

1. `emitOStmt₂Query` was defined with `by cases h : V₁.embed i` → desugars to `Sum.rec`, which is **not** `split`-able and whose self-referential `rfl` makes both `unfold; cases h` ("generalize result not type correct") and `rw [h]`/`simp [h]` ("motive not type correct") fail. **Fix:** define it with term-mode `match h : V₁.embed i with | .inl k => …` (a split-able matcher, defeq to the `cases`-form). The characterization then goes `unfold emitOStmt₂Query; split; · next k h => rw [emitOStmtQuery*_simulateQ, mkVerifierOStmtOut_{inl,inr} … i k h]; congr 2; simp only [eqRec_eq_cast, cast_cast]`.

2. The cast closer: `mkVerifierOStmtOut`'s `hEq i ▸ h ▸ oStmt k` is not a plain `Eq.recOn`, so an `eq_of_heq (eqRec_heq …)` chain fails to unify. `congr 2; simp only [eqRec_eq_cast, cast_cast]` normalizes both sides to `cast _ (oStmt k)` and closes by proof-irrelevance.

(Heads-up: a prior autosync had committed a non-building intermediate of this proof — `0` sorries but a `554/558` type-mismatch. `f8f4b3928` restores a green `Append.lean`; please `git show lalalune/main:…/Append.lean` builds, not just sorry-count.)

**Remaining for unconditional `fullOracleReduction_perfectCompleteness`:** it is currently `sorry`-free but **conditional** (`General.lean:171` assumes the per-phase + append `perfectCompleteness` as hypotheses). The unconditional version needs to discharge `hCoreInteractionAppend`/`hBatchingCoreAppend`/`hFullAppend` via `reduction_append_perfectCompleteness_msg` (now available) + the `AppendCoherent` instances + the message-seam side conditions. The soundness-side sorries (`AppendSoundnessMsgProof`, `AppendSoundnessSeamTransfer`) are separate from the completeness chain.
