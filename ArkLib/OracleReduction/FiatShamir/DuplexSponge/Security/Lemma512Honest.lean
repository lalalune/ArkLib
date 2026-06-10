/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemmaFoundations

/-!
# #316 — Duplex-Sponge Fiat-Shamir: discharge of the M2a honest bad-event residual
`DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual`
(CO25 Lemma 5.12, honest form: `¬E(tr) → ¬E_inv_honest(tr, s, S)`).

Route (all new content, no probability needed):

1. `hasInvEntry_eraseIdx` — erasing one *redundant* entry preserves "the trace contains an
   inverse-permutation (`p⁻¹`) entry": if the erased slot holds the witness, its redundancy
   certificate (`redundantEntryDS`, third arm) is itself an **earlier inverse entry**, which
   survives the erasure; otherwise the witness occurrence survives (index-shifted).
2. `hasInvEntry_removeRedundant` — hence the dedup fixpoint `removeRedundantEntryDS`
   preserves it (strong induction on the trace length through the WF recursion).
3. `capacitySegmentDupPermInv_of_inv_mem` — any inverse entry in the dedup'd trace fires
   `E_pinv`: its 5th disjunct allows `j' ≤ j` with the *answer*-capacity condition, which
   **self-matches at `j' = j`** (the answer's capacity equals itself).
4. `hasInvEntry_implies_E` — keystone: an inverse entry anywhere in the *raw* trace fires the
   combined bad event `E`. Contrapositive: `¬E(tr)` ⟹ the raw trace has **no** `p⁻¹ entries.
5. `lemma5_12_honest` — `E_inv_honest` exhibits a `p⁻¹` entry at a raw-trace index
   (`tr[·]? = some ⟨.inr (.inr _), _⟩`); contradiction with the keystone.

NOTE on strength: step 3 leans on the in-tree `capacitySegmentDupPermInv` being
self-firing on every inverse entry (its `j' ≤ j` answer-side disjunct). This is the
*in-tree* CO25 Eq. 39 rendering that the residual is stated against; the discharge is
therefore exact for the in-tree statement.
-/

open OracleComp OracleSpec ProtocolSpec
open OracleSpec.QueryLog OracleSpec.QueryLog.BadEventDS

namespace DuplexSpongeFS.Sponge316

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- The trace contains an inverse-permutation (`p⁻¹`) entry. -/
def HasInvEntry (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ sOut sIn : CanonicalSpongeState U,
    (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
      (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
        (duplexSpongeChallengeOracle StmtIn U).Range t) ∈ tr

/-- Membership from an `getElem?`-hit. -/
private lemma mem_of_getElem?' {α : Type _} {l : List α} {i : ℕ} {a : α}
    (h : l[i]? = some a) : a ∈ l := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hlt

/-- The trace contains a concrete hash entry. -/
def HasHashEntry (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) : Prop :=
  (⟨Sum.inl stmt, capSeg⟩ :
    (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
      (duplexSpongeChallengeOracle StmtIn U).Range t) ∈ tr

/-- Inversion of `redundantEntryDS` at a hash slot: the redundancy certificate is an earlier
copy of the same hash entry. -/
private lemma redundantEntryDS_hash_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C)
    (hval : tr[idx] =
      (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDS idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      tr[j'] = (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t) := by
  unfold redundantEntryDS at hred
  rw [hval] at hred
  exact hred

/-- **One-step preservation**: erasing a redundant entry preserves a concrete hash entry. -/
private lemma hasHashEntry_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDS idx)
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (hP : HasHashEntry tr stmt capSeg) :
    HasHashEntry (tr.eraseIdx idx.val) stmt capSeg := by
  classical
  unfold HasHashEntry at hP ⊢
  by_cases hval : tr[idx] =
      (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t)
  · obtain ⟨j', hj', hentry⟩ :=
      redundantEntryDS_hash_inversion tr idx stmt capSeg hval hred
    have hj'idx : j'.val < idx.val := hj'
    have hkeep : (tr.eraseIdx idx.val)[j'.val]? = tr[j'.val]? :=
      List.getElem?_eraseIdx_of_lt hj'idx
    have hhit : tr[j'.val]? = some tr[j'] := by
      simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem (l := tr) j'.isLt
    exact mem_of_getElem?' (by rw [hkeep, hhit, hentry])
  · rw [List.mem_iff_getElem] at hP
    obtain ⟨p, hp, hpe⟩ := hP
    have hpne : p ≠ idx.val := by
      intro hcontr
      apply hval
      calc tr[idx] = tr[p]'hp := by
            subst hcontr; rfl
        _ = _ := hpe
    have hp? : tr[p]? = some
        (⟨Sum.inl stmt, capSeg⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) := by
      rw [List.getElem?_eq_getElem hp, hpe]
    rcases Nat.lt_or_ge p idx.val with hlt | hge
    · exact mem_of_getElem?' (i := p) (by rw [List.getElem?_eraseIdx_of_lt hlt, hp?])
    · have hgt : idx.val < p := lt_of_le_of_ne hge (Ne.symm hpne)
      exact mem_of_getElem?' (i := p - 1) (by
        rw [List.getElem?_eraseIdx_of_ge (by omega), show p - 1 + 1 = p by omega, hp?])

/-- **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves concrete
hash entries. -/
private lemma hasHashEntry_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      ∀ {stmt : StmtIn} {capSeg : Vector U SpongeSize.C},
        HasHashEntry tr stmt capSeg → HasHashEntry (removeRedundantEntryDS tr).1 stmt capSeg := by
  intro N
  induction N with
  | zero =>
      intro tr hlen stmt capSeg hP
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)] at hP
      simp [HasHashEntry] at hP
  | succ N ih =>
      intro tr hlen stmt capSeg hP
      rw [removeRedundantEntryDS]
      split
      · rename_i hex
        refine ih _ ?_ (hasHashEntry_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hP

/-- Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the
deduplicated trace still contains that same hash entry. -/
theorem hasHashEntry_removeRedundant_of_mem
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasHashEntry tr stmt capSeg) :
    HasHashEntry (removeRedundantEntryDS tr).1 stmt capSeg :=
  hasHashEntry_removeRedundant tr.length tr le_rfl h

/-- Inversion of `redundantEntryDS` at an inverse-permutation slot: the redundancy
certificate is an earlier inverse entry (same or reversed). -/
private lemma redundantEntryDS_inv_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (sOut sIn : CanonicalSpongeState U)
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDS idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      (tr[j'] = (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
        tr[j'] = (⟨Sum.inr (Sum.inr sIn), sOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) := by
  unfold redundantEntryDS at hred
  rw [hval] at hred
  exact hred

/-- **One-step preservation**: erasing a redundant entry preserves `HasInvEntry`. -/
private lemma hasInvEntry_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDS idx)
    (hP : HasInvEntry tr) :
    HasInvEntry (tr.eraseIdx idx.val) := by
  classical
  obtain ⟨sOut, sIn, hmem⟩ := hP
  by_cases hval : tr[idx] =
      (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t)
  · -- the erased slot is (a copy of) the witness: redundancy yields an earlier inverse twin
    obtain ⟨j', hj', hcase⟩ := redundantEntryDS_inv_inversion tr idx sOut sIn hval hred
    have hj'idx : j'.val < idx.val := hj'
    have hkeep : (tr.eraseIdx idx.val)[j'.val]? = tr[j'.val]? :=
      List.getElem?_eraseIdx_of_lt hj'idx
    have hhit : tr[j'.val]? = some tr[j'] := by
      simpa only [List.get_eq_getElem] using List.getElem?_eq_getElem (l := tr) j'.isLt
    rcases hcase with hc | hc
    · exact ⟨sOut, sIn, mem_of_getElem?' (by rw [hkeep, hhit, hc])⟩
    · exact ⟨sIn, sOut, mem_of_getElem?' (by rw [hkeep, hhit, hc])⟩
  · -- some other occurrence carries the witness; it survives the erasure
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨p, hp, hpe⟩ := hmem
    have hpne : p ≠ idx.val := by
      intro hcontr
      apply hval
      calc tr[idx] = tr[p]'hp := by
            subst hcontr; rfl
        _ = _ := hpe
    have hp? : tr[p]? = some
        (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) := by
      rw [List.getElem?_eq_getElem hp, hpe]
    rcases Nat.lt_or_ge p idx.val with hlt | hge
    · refine ⟨sOut, sIn, mem_of_getElem?' (i := p) ?_⟩
      rw [List.getElem?_eraseIdx_of_lt hlt, hp?]
    · have hgt : idx.val < p := lt_of_le_of_ne hge (Ne.symm hpne)
      refine ⟨sOut, sIn, mem_of_getElem?' (i := p - 1) ?_⟩
      rw [List.getElem?_eraseIdx_of_ge (by omega), show p - 1 + 1 = p by omega, hp?]

/-- **Fixpoint preservation**: the dedup procedure `removeRedundantEntryDS` preserves
`HasInvEntry` (strong induction on the trace length). -/
private lemma hasInvEntry_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      HasInvEntry tr → HasInvEntry (removeRedundantEntryDS tr).1 := by
  intro N
  induction N with
  | zero =>
      intro tr hlen hP
      obtain ⟨sOut, sIn, hmem⟩ := hP
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)] at hmem
      simp at hmem
  | succ N ih =>
      intro tr hlen hP
      rw [removeRedundantEntryDS]
      split
      · rename_i hex
        refine ih _ ?_ (hasInvEntry_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hP

/-- Any inverse-permutation entry in the dedup'd trace fires `E_pinv`
(`capacitySegmentDupPermInv`): the left conjunct is the entry itself, and the right
disjunction is satisfied by its **5th disjunct at `j' = j`** (the inverse-answer capacity
trivially equals itself). -/
private lemma capacitySegmentDupPermInv_of_inv_mem
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasInvEntry (removeRedundantEntryDS tr).1) :
    capacitySegmentDupPermInv tr := by
  obtain ⟨sOut, sIn, hmem⟩ := h
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨j, hj, hje⟩ := hmem
  unfold capacitySegmentDupPermInv
  exact ⟨⟨j, hj⟩, sIn.capacitySegment, ⟨sOut, sIn, hje, rfl⟩,
    Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨j, hj⟩, le_refl _, sIn, sOut, hje, rfl⟩)))⟩

/-- **Keystone**: an inverse-permutation entry anywhere in the *raw* trace fires the
combined bad event `E`. Contrapositive: off `E`, the trace contains no `p⁻¹` entries at
all — the reusable engine behind the honest Lemmas 5.12/5.14/5.16 analyses. -/
theorem hasInvEntry_implies_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : HasInvEntry tr) :
    BadEventDS.E tr :=
  Or.inl (Or.inr (Or.inr (capacitySegmentDupPermInv_of_inv_mem tr
    (hasInvEntry_removeRedundant tr.length tr le_rfl h))))

/-- Contrapositive form of the keystone. -/
theorem not_hasInvEntry_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr) :
    ¬ HasInvEntry tr :=
  fun hinv => h (hasInvEntry_implies_E tr hinv)

/-- Index form of `not_hasInvEntry_of_not_E`: off `E`, no trace slot can be an inverse
permutation entry. This is the form consumed by the `J_BT` first-occurrence payloads in the
honest backtrack timing/fork analyses. -/
theorem not_inv_getElem?_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    {i : ℕ} {sOut sIn : CanonicalSpongeState U}
    (hentry : tr[i]? =
      some (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t)) :
    False :=
  not_hasInvEntry_of_not_E tr h ⟨sOut, sIn, mem_of_getElem?' hentry⟩

/-- Off `E`, a trace slot known to be either the forward or inverse entry for one sponge step
must be the forward entry. This is the local eliminator for `firstOccurrenceOfEither`. -/
theorem forward_getElem?_of_not_E_of_perm_or_inv
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    {i : ℕ} {sIn sOut : CanonicalSpongeState U}
    (hentry :
      tr[i]? =
        some (⟨Sum.inr (Sum.inl sIn), sOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
      tr[i]? =
        some (⟨Sum.inr (Sum.inr sOut), sIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) :
    tr[i]? =
      some (⟨Sum.inr (Sum.inl sIn), sOut⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t) := by
  rcases hentry with hforward | hinv
  · exact hforward
  · exact False.elim (not_inv_getElem?_of_not_E tr h hinv)

/-- `J_BT` hash-index payloads point to the recorded hash query for their sequence. -/
theorem jbt_hash_getElem?
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S) :
    GetElem?.getElem? tr p.2.1.val =
      some (⟨Sum.inl p.1.stmt,
        Vector.drop (p.1.inputState[0]'(by
          rw [p.1.inputState_length_eq_outputState_length_succ]
          exact Nat.succ_pos _)) SpongeSize.R⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using DuplexSpongeFS.Backtrack.BacktrackSequence.index_hash_getElem?
    (trace := tr) (state := state) (seq := seq)

/-- A `J_BT` hash-index payload is the first occurrence of its hash anchor: no strictly earlier
raw trace slot contains the same hash entry. -/
theorem jbt_hash_no_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (j : Fin tr.length) (hj : j.val < p.2.1.val) :
    tr.get j ≠
      (⟨Sum.inl p.1.stmt,
        Vector.drop (p.1.inputState[0]'(by
          rw [p.1.inputState_length_eq_outputState_length_succ]
          exact Nat.succ_pos _)) SpongeSize.R⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using DuplexSpongeFS.Backtrack.BacktrackSequence.index_hash_no_prior
    (trace := tr) (state := state) (seq := seq) (j := j) hj

/-- Off `E`, a nonterminal `J_BT` permutation-index payload points to the forward
permutation query for that chain step. -/
theorem jbt_perm_forward_getElem?_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length) :
    GetElem?.getElem? tr (p.2.2 pairIdx).val =
      some (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
        p.1.outputState[pairIdx.val]'hpair⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using forward_getElem?_of_not_E_of_perm_or_inv (tr := tr) h
    (DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_getElem?_of_lt
      (trace := tr) (state := state) (seq := seq) (pairIdx := pairIdx) (hpair := hpair))

/-- A nonterminal `J_BT` permutation-index payload is the first occurrence of either recorded
permutation direction for that chain step: no strictly earlier raw trace slot contains the same
forward entry or the corresponding inverse entry. -/
theorem jbt_perm_no_prior_of_lt
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length)
    (j : Fin tr.length) (hj : j.val < (p.2.2 pairIdx).val) :
    tr.get j ≠
        (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
          p.1.outputState[pairIdx.val]'hpair⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      tr.get j ≠
        (⟨Sum.inr (Sum.inr (p.1.outputState[pairIdx.val]'hpair)), p.1.inputState[pairIdx]⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  simpa using DuplexSpongeFS.Backtrack.BacktrackSequence.index_perm_no_prior_of_lt
    (trace := tr) (state := state) (seq := seq) (pairIdx := pairIdx) (hpair := hpair)
    (j := j) hj

/-- A `J_BT` payload witnessing the hash-after-first-permutation timing condition cannot be
the empty chain: in the empty case the first-chain index is the sentinel `tr.length`, while the
hash index is a genuine trace index. -/
theorem jbt_time_h_outputState_nonempty
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (hgt : p.2.1.val > (p.2.2 ⟨0, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val) :
    0 < p.1.outputState.length := by
  classical
  unfold DuplexSpongeFS.Backtrack.J_BT at hp
  rw [Finset.mem_image] at hp
  obtain ⟨seq, _hseq, hp_eq⟩ := hp
  subst p
  by_contra hnot
  have hidx :
      ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2 ⟨0, by
        have := seq.inputState_length_eq_outputState_length_succ
        omega⟩).val = tr.length := by
    dsimp [DuplexSpongeFS.Backtrack.BacktrackSequence.Index]
    simp [hnot]
  have hhash_lt : (DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1.val
      < tr.length :=
    (DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1.isLt
  have hgt' :
      (DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).1.val >
        ((DuplexSpongeFS.Backtrack.BacktrackSequence.Index tr state seq).2 ⟨0, by
          have := seq.inputState_length_eq_outputState_length_succ
          omega⟩).val := by
    simpa using hgt
  omega

/-- Off `E`, the first chain index in a hash-after-first-permutation `J_BT` payload is the
forward permutation query for the first chain step. -/
theorem jbt_time_h_first_perm_forward_getElem?_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (p : Sigma fun seq : DuplexSpongeFS.Backtrack.BacktrackSequence tr state =>
      DuplexSpongeFS.Backtrack.BacktrackIndexList tr seq)
    (hp : p ∈ DuplexSpongeFS.Backtrack.J_BT S)
    (hgt : p.2.1.val > (p.2.2 ⟨0, by
      have := p.1.inputState_length_eq_outputState_length_succ
      omega⟩).val) :
    ∃ (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length),
      pairIdx.val = 0 ∧
      GetElem?.getElem? tr (p.2.2 pairIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
          p.1.outputState[pairIdx.val]'hpair⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  let pairIdx : Fin p.1.inputState.length := ⟨0, by
    rw [p.1.inputState_length_eq_outputState_length_succ]
    exact Nat.succ_pos _⟩
  have hpair : pairIdx.val < p.1.outputState.length := by
    simpa [pairIdx] using jbt_time_h_outputState_nonempty tr state S p hp hgt
  refine ⟨pairIdx, hpair, rfl, ?_⟩
  simpa using jbt_perm_forward_getElem?_of_not_E
    (tr := tr) h (state := state) (S := S) (p := p) (hp := hp)
    (pairIdx := pairIdx) (hpair := hpair)

/-- Off `E`, an honest hash-ordering witness gives concrete raw trace entries: the anchoring
hash query and the first forward permutation query, with the permutation entry earlier in the
trace. This is the raw-trace payload needed before the dedup collision step of M2c. -/
theorem e_time_h_honest_raw_forward_witness_of_not_E
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (h : ¬ BadEventDS.E tr)
    (state : CanonicalSpongeState U) (S : DuplexSpongeFS.Backtrack.S_BT tr state)
    (hTime : DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest tr state S) :
    ∃ p ∈ DuplexSpongeFS.Backtrack.J_BT S,
    ∃ (pairIdx : Fin p.1.inputState.length) (hpair : pairIdx.val < p.1.outputState.length),
      pairIdx.val = 0 ∧
      (p.2.2 pairIdx).val < p.2.1.val ∧
      GetElem?.getElem? tr p.2.1.val =
        some (⟨Sum.inl p.1.stmt,
          Vector.drop (p.1.inputState[0]'(by
            rw [p.1.inputState_length_eq_outputState_length_succ]
            exact Nat.succ_pos _)) SpongeSize.R⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∧
      GetElem?.getElem? tr (p.2.2 pairIdx).val =
        some (⟨Sum.inr (Sum.inl p.1.inputState[pairIdx]),
          p.1.outputState[pairIdx.val]'hpair⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) := by
  unfold DuplexSpongeFS.KeyLemmaFoundations.E_time_h_honest at hTime
  obtain ⟨p, hp, hgt⟩ := hTime
  obtain ⟨pairIdx, hpair, hidx0, hperm⟩ :=
    jbt_time_h_first_perm_forward_getElem?_of_not_E
      (tr := tr) h (state := state) (S := S) (p := p) (hp := hp) hgt
  refine ⟨p, hp, pairIdx, hpair, hidx0, ?_, jbt_hash_getElem? tr state S p hp, hperm⟩
  have hpairIdx :
      pairIdx = ⟨0, by
        have := p.1.inputState_length_eq_outputState_length_succ
        omega⟩ := Fin.ext hidx0
  rw [hpairIdx]
  omega

/-- **M2a discharged** — `DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual`
holds: off the combined bad event `E`, no BackTrack chain step is anchored by an
inverse-permutation entry (CO25 Lemma 5.12, honest form over `Backtrack.S_BT`). -/
theorem lemma5_12_honest :
    DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual StmtIn U := by
  unfold DuplexSpongeFS.KeyLemmaFoundations.Lemma5_12HonestResidual
  intro tr state S hE hInv
  unfold DuplexSpongeFS.KeyLemmaFoundations.E_inv_honest at hInv
  obtain ⟨p, _hpJ, ιx, sOut, sIn, hentry⟩ := hInv
  exact hE (hasInvEntry_implies_E tr ⟨sOut, sIn, mem_of_getElem?' hentry⟩)

end DuplexSpongeFS.Sponge316

#print axioms DuplexSpongeFS.Sponge316.hasInvEntry_implies_E
#print axioms DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundant_of_mem
#print axioms DuplexSpongeFS.Sponge316.not_inv_getElem?_of_not_E
#print axioms DuplexSpongeFS.Sponge316.forward_getElem?_of_not_E_of_perm_or_inv
#print axioms DuplexSpongeFS.Sponge316.jbt_hash_getElem?
#print axioms DuplexSpongeFS.Sponge316.jbt_hash_no_prior
#print axioms DuplexSpongeFS.Sponge316.jbt_perm_forward_getElem?_of_not_E
#print axioms DuplexSpongeFS.Sponge316.jbt_perm_no_prior_of_lt
#print axioms DuplexSpongeFS.Sponge316.jbt_time_h_outputState_nonempty
#print axioms DuplexSpongeFS.Sponge316.jbt_time_h_first_perm_forward_getElem?_of_not_E
#print axioms DuplexSpongeFS.Sponge316.e_time_h_honest_raw_forward_witness_of_not_E
#print axioms DuplexSpongeFS.Sponge316.lemma5_12_honest
