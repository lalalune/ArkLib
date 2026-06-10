/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEvents

/-!
# Paper-faithful redundant-entry dedup for the duplex-sponge trace (CO25 Def. 5.5)

`BadEvents.lean`'s `redundantEntryDS` deviates from CO25 (ePrint 2025/536) Definition 5.5: its
swapped certificate for a permutation entry uses the **same direction** with the state pair
reversed, where the paper uses the **opposite-direction** entry (`(p, x, y)` is redundant given a
prior `(p⁻¹, y, x)`, and vice versa). That deviation is not cosmetic — both honest residuals
written against it are *refuted* by machine-checked countermodels
(`Lemma516TimePFalse.lean`, `Lemma514ForkFalse.lean`).

This file introduces the paper-faithful definition `redundantEntryDSPaper` (the two swapped
disjuncts corrected to opposite-direction certificates) together with its dedup machinery
(`NoRedundantEntryDSPaper`, `removeRedundantEntryDSPaper`, fixpoint lemmas), mirroring the
legacy API so the downstream chain (`Lemma512Honest.lean`, the `KeyLemmaFoundations.lean`
honest residuals) can migrate incrementally. The legacy definition stays in place — the landed
refutations are *about it* and remain meaningful as the record of why this repair exists.

Note the semantic consequence flagged by the refutation analysis: under paper semantics a raw
*inverse* entry can dedup against a prior *forward* entry (and vice versa), so the legacy
"inverse entry ⇒ E" keystone of `Lemma512Honest.lean` changes shape under migration.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleSpec

namespace QueryLog

section DuplexSpongeFS

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- **Paper-faithful redundant entry (CO25 Def. 5.5).** An entry is redundant if a prior entry
answers it: same hash query-answer pair; same-direction same permutation pair; or — the corrected
clause — the **opposite-direction** permutation entry with input/output exchanged
(`(p, x, y)` given a prior `(p⁻¹, y, x)`; `(p⁻¹, y, x)` given a prior `(p, x, y)`). -/
def redundantEntryDSPaper (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) : Prop :=
  match log[idx] with
  | ⟨.inl u, ⟨stmt, state⟩⟩ => ∃ j' < idx, log[j'] = ⟨.inl u, stmt, state⟩
  | ⟨.inr (.inl stateIn), stateOut⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr (.inl stateIn), stateOut⟩ ∨
      log[j'] = ⟨.inr <|.inr stateOut, stateIn⟩
  | ⟨.inr (.inr stateOut), stateIn⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr (.inr stateOut), stateIn⟩ ∨
      log[j'] = ⟨.inr <|.inl stateIn, stateOut⟩

/-- A trace has no paper-redundant entries. -/
def NoRedundantEntryDSPaper (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ idx : Fin log.length, ¬ log.redundantEntryDSPaper idx

/-- Remove paper-redundant entries by repeated erasure (classical choice of a redundant index),
mirroring `removeRedundantEntryDS`. Terminates since each erasure shortens the trace. -/
noncomputable def removeRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) | log.NoRedundantEntryDSPaper} :=
  letI : Decidable (∃ idx : Fin log.length, log.redundantEntryDSPaper idx) :=
    Classical.propDecidable _
  if h : ∃ idx : Fin log.length, log.redundantEntryDSPaper idx then
    removeRedundantEntryDSPaper (log.eraseIdx (Classical.choose h).val)
  else
    ⟨log, fun idx => not_exists.mp h idx⟩
termination_by log.length
decreasing_by
  exact (by
    have hlt : (Classical.choose h).val < log.length := (Classical.choose h).isLt
    have heq : (log.eraseIdx (Classical.choose h).val).length + 1 = log.length :=
      List.length_eraseIdx_add_one hlt
    omega)

/-- `removeRedundantEntryDSPaper` is a fixpoint on already-deduplicated traces. -/
theorem removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : log.NoRedundantEntryDSPaper) :
    removeRedundantEntryDSPaper log = ⟨log, h⟩ := by
  have hnone : ¬ ∃ idx : Fin log.length, log.redundantEntryDSPaper idx := not_exists.mpr h
  rw [removeRedundantEntryDSPaper]
  simp [hnone]

/-- First-projection form of the fixpoint lemma. -/
theorem removeRedundantEntryDSPaper_fst_eq_self_of_noRedundantEntryDSPaper
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : log.NoRedundantEntryDSPaper) :
    (removeRedundantEntryDSPaper log).1 = log := by
  rw [removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper log h]

/-- Subtype fixpoint form for the canonical output. -/
theorem removeRedundantEntryDSPaper_eq_self
    (base : {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) |
      log.NoRedundantEntryDSPaper}) :
    removeRedundantEntryDSPaper base.1 = base := by
  cases base with
  | mk log h =>
      exact removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper log h

/-- A hash entry's paper-redundancy coincides with legacy redundancy (the repair only touches
the permutation arms). -/
theorem redundantEntryDSPaper_iff_of_hash
    (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin log.length)
    {u : StmtIn} {v : _} (hidx : log[idx] = ⟨.inl u, v⟩) :
    log.redundantEntryDSPaper idx ↔ log.redundantEntryDS idx := by
  unfold redundantEntryDSPaper redundantEntryDS
  rw [hidx]
  rcases v with ⟨stmt, state⟩
  rfl

end DuplexSpongeFS

end QueryLog

end OracleSpec

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper
#print axioms OracleSpec.QueryLog.removeRedundantEntryDSPaper
#print axioms OracleSpec.QueryLog.removeRedundantEntryDSPaper_eq_self_of_noRedundantEntryDSPaper
#print axioms OracleSpec.QueryLog.removeRedundantEntryDSPaper_eq_self
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper_iff_of_hash
