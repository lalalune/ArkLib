/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BadEventsPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma512Honest

/-!
# Lemma 5.12 migration to paper semantics — inversion bricks (statement repair, step 3a)

First bricks of the `Lemma512Honest.lean` migration onto the paper-faithful dedup
`redundantEntryDSPaper` (CO25 Def. 5.5): the per-slot inversion lemmas and the capacity-transport
corollaries. The key semantic difference vs the legacy chain: a redundant *forward* entry's
certificate is now an earlier forward entry with the **same** pair or an earlier **inverse** entry
with the same pair (opposite direction) — the state pair is preserved, only the direction flips,
so capacity transports carry **both** sides unchanged (cleaner than the legacy reversed-pair
attribution). Downstream consumers must therefore case on the prior entry's direction — this is
exactly the "raw inverse entries can dedup into forward entries" shape-change the refutation
analysis predicted.
-/

open OracleComp OracleSpec ProtocolSpec

namespace OracleSpec

namespace QueryLog

section DuplexSpongeFS

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

/-- Inversion of `redundantEntryDSPaper` at a forward slot: the certificate is an earlier entry
with the **same state pair**, in either direction. -/
lemma redundantEntryDSPaper_forward_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stateIn stateOut : CanonicalSpongeState U)
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDSPaper idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      (tr[j'] = (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
        tr[j'] = (⟨Sum.inr (Sum.inr stateOut), stateIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) := by
  unfold redundantEntryDSPaper at hred
  rw [hval] at hred
  exact hred

/-- Inversion of `redundantEntryDSPaper` at an inverse slot: the certificate is an earlier entry
with the **same state pair**, in either direction. -/
lemma redundantEntryDSPaper_inverse_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stateOut stateIn : CanonicalSpongeState U)
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inr stateOut), stateIn⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDSPaper idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      (tr[j'] = (⟨Sum.inr (Sum.inr stateOut), stateIn⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t) ∨
        tr[j'] = (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
          (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
            (duplexSpongeChallengeOracle StmtIn U).Range t)) := by
  unfold redundantEntryDSPaper at hred
  rw [hval] at hred
  exact hred

/-- Inversion of `redundantEntryDSPaper` at a hash slot: an earlier copy of the same hash entry
(unchanged from legacy — the repair only touches the permutation arms). -/
lemma redundantEntryDSPaper_hash_inversion
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C)
    (hval : tr[idx] =
      (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t))
    (hred : tr.redundantEntryDSPaper idx) :
    ∃ j' : Fin tr.length, j' < idx ∧
      tr[j'] = (⟨Sum.inl stmt, capSeg⟩ :
        (t : (duplexSpongeChallengeOracle StmtIn U).Domain) ×
          (duplexSpongeChallengeOracle StmtIn U).Range t) := by
  unfold redundantEntryDSPaper at hred
  rw [hval] at hred
  exact hred

/-- A paper-redundant forward entry sharing a target capacity has an earlier **permutation**
replacement (in either direction) carrying the same state pair, hence the same capacity sides. -/
theorem redundantPaper_forward_capacity_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {capSeg : Vector U SpongeSize.C} {stateIn stateOut : CanonicalSpongeState U}
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inl stateIn), stateOut⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hred : tr.redundantEntryDSPaper idx)
    (hcap : stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg) :
    ∃ j' : Fin tr.length, j' < idx ∧
      ∃ stateIn' stateOut' : CanonicalSpongeState U,
        (tr[j'] =
            (⟨Sum.inr (Sum.inl stateIn'), stateOut'⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∨
          tr[j'] =
            (⟨Sum.inr (Sum.inr stateOut'), stateIn'⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) ∧
        (stateOut'.capacitySegment = capSeg ∨ stateIn'.capacitySegment = capSeg) := by
  obtain ⟨j', hj', hcase⟩ :=
    redundantEntryDSPaper_forward_inversion tr idx stateIn stateOut hval hred
  exact ⟨j', hj', stateIn, stateOut, hcase, hcap⟩

/-- A paper-redundant inverse entry sharing a target capacity has an earlier **permutation**
replacement (in either direction) carrying the same state pair, hence the same capacity sides. -/
theorem redundantPaper_inverse_capacity_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {capSeg : Vector U SpongeSize.C} {stateOut stateIn : CanonicalSpongeState U}
    (hval : tr[idx] =
      (⟨Sum.inr (Sum.inr stateOut), stateIn⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hred : tr.redundantEntryDSPaper idx)
    (hcap : stateOut.capacitySegment = capSeg ∨ stateIn.capacitySegment = capSeg) :
    ∃ j' : Fin tr.length, j' < idx ∧
      ∃ stateIn' stateOut' : CanonicalSpongeState U,
        (tr[j'] =
            (⟨Sum.inr (Sum.inl stateIn'), stateOut'⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)) ∨
          tr[j'] =
            (⟨Sum.inr (Sum.inr stateOut'), stateIn'⟩ :
              OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) ∧
        (stateOut'.capacitySegment = capSeg ∨ stateIn'.capacitySegment = capSeg) := by
  obtain ⟨j', hj', hcase⟩ :=
    redundantEntryDSPaper_inverse_inversion tr idx stateOut stateIn hval hred
  refine ⟨j', hj', stateIn, stateOut, ?_, hcap⟩
  rcases hcase with hinv | hfwd
  · exact Or.inr hinv
  · exact Or.inl hfwd


end DuplexSpongeFS

end QueryLog

end OracleSpec

/-! ## Dedup transports (hash anchors) -/

namespace DuplexSpongeFS.Sponge316

open OracleSpec OracleSpec.QueryLog

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]

private lemma mem_of_getElem?' {α : Type _} {l : List α} {i : ℕ} {a : α}
    (h : l[i]? = some a) : a ∈ l := by
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hlt

private lemma hasHashEntry_eraseIdxPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDSPaper idx)
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
      redundantEntryDSPaper_hash_inversion tr idx stmt capSeg hval hred
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
private lemma hasHashEntry_removeRedundantPaper :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      ∀ {stmt : StmtIn} {capSeg : Vector U SpongeSize.C},
        HasHashEntry tr stmt capSeg → HasHashEntry (removeRedundantEntryDSPaper tr).1 stmt capSeg := by
  intro N
  induction N with
  | zero =>
      intro tr hlen stmt capSeg hP
      rw [List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)] at hP
      simp [HasHashEntry] at hP
  | succ N ih =>
      intro tr hlen stmt capSeg hP
      rw [removeRedundantEntryDSPaper]
      split
      · rename_i hex
        refine ih _ ?_ (hasHashEntry_eraseIdxPaper tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hP

/-- Public dedup bridge for hash anchors: if the raw trace contains a concrete hash entry, the
deduplicated trace still contains that same hash entry. -/
theorem hasHashEntry_removeRedundantPaper_of_mem
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (h : HasHashEntry tr stmt capSeg) :
    HasHashEntry (removeRedundantEntryDSPaper tr).1 stmt capSeg :=
  hasHashEntry_removeRedundantPaper tr.length tr le_rfl h

/-! ## Paper-semantics collision shapes (direction-aware guards)

The legacy first-occurrence guards exclude "the same pair up to *same-direction* reversal" —
shaped around the buggy certificate. Under `redundantEntryDSPaper` the certificates preserve the
pair and flip the *direction*, so the guards must exclude the same forward pair and the
opposite-direction (inverse) pair, and prior capacity witnesses may sit on either direction. -/

private def hashEntryP (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inl stmt, capSeg⟩

private def forwardEntryP (stateIn stateOut : CanonicalSpongeState U) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inr (Sum.inl stateIn), stateOut⟩

private def inverseEntryP (stateOut stateIn : CanonicalSpongeState U) :
    OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U) :=
  ⟨Sum.inr (Sum.inr stateOut), stateIn⟩

/-- Direction-agnostic prior-permutation capacity shape: some permutation entry (either
direction) strictly before the tracked forward output shares the target capacity on either side
of its pair. The paper-semantics analogue of `HasForwardCapacityBeforeForwardOutput`. -/
def HasPermCapacityBeforeForwardOutputPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ jCur : Fin tr.length,
    ∃ stateIn stateOut : CanonicalSpongeState U,
      tr[jCur] = forwardEntryP stateIn stateOut ∧
      ∃ jPrev : Fin tr.length, jPrev < jCur ∧
        ∃ prevIn prevOut : CanonicalSpongeState U,
          (tr[jPrev] = forwardEntryP prevIn prevOut ∨
            tr[jPrev] = inverseEntryP prevOut prevIn) ∧
          (prevOut.capacitySegment = stateOut.capacitySegment ∨
            prevIn.capacitySegment = stateOut.capacitySegment)

/-- Paper-semantics first-occurrence collision shape: the tracked forward entry has no prior copy
of its pair **in either direction** (matching `redundantEntryDSPaper`'s certificates), and some
strictly earlier permutation entry (either direction) shares its output capacity. -/
def HasFirstPermCapacityBeforeForwardOutputPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ jCur : Fin tr.length,
    ∃ stateIn stateOut : CanonicalSpongeState U,
      tr[jCur] = forwardEntryP stateIn stateOut ∧
      (∀ j : Fin tr.length, j.val < jCur.val →
        tr[j] ≠ forwardEntryP stateIn stateOut ∧
          tr[j] ≠ inverseEntryP stateOut stateIn) ∧
      ∃ jPrev : Fin tr.length, jPrev < jCur ∧
        ∃ prevIn prevOut : CanonicalSpongeState U,
          (tr[jPrev] = forwardEntryP prevIn prevOut ∨
            tr[jPrev] = inverseEntryP prevOut prevIn) ∧
          (prevOut.capacitySegment = stateOut.capacitySegment ∨
            prevIn.capacitySegment = stateOut.capacitySegment)

/-- Forgetting the first-occurrence guard leaves the broad paper shape. -/
theorem hasPermCapacityBeforeForwardOutputPaper_of_first
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstPermCapacityBeforeForwardOutputPaper tr) :
    HasPermCapacityBeforeForwardOutputPaper tr := by
  obtain ⟨jCur, stateIn, stateOut, hcur, _hfirst, jPrev, hlt, prevIn, prevOut, hprev, hcap⟩ := h
  exact ⟨jCur, stateIn, stateOut, hcur, jPrev, hlt, prevIn, prevOut, hprev, hcap⟩


/-- A forward slot whose pair has no prior copy in either direction is not paper-redundant:
the first-occurrence guard defeats both certificate disjuncts of `redundantEntryDSPaper`. -/
theorem not_redundantEntryDSPaper_forward_of_no_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {stateIn stateOut : CanonicalSpongeState U}
    (hidx : tr[idx] = forwardEntryP stateIn stateOut)
    (hfirst : ∀ j : Fin tr.length, j.val < idx.val →
      tr[j] ≠ forwardEntryP stateIn stateOut ∧
        tr[j] ≠ inverseEntryP stateOut stateIn) :
    ¬ tr.redundantEntryDSPaper idx := by
  intro hred
  unfold OracleSpec.QueryLog.redundantEntryDSPaper at hred
  rw [hidx] at hred
  obtain ⟨j, hjlt, hcase⟩ := hred
  rcases hcase with hsame | hinv
  · exact (hfirst j hjlt).1 hsame
  · exact (hfirst j hjlt).2 hinv

/-- The paper first-occurrence collision shape carries the nonredundancy proof for its forward
anchor. -/
theorem hasFirstPermCapacityBeforeForwardOutputPaper_current_not_redundant
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstPermCapacityBeforeForwardOutputPaper tr) :
    ∃ jCur : Fin tr.length,
      ∃ stateIn stateOut : CanonicalSpongeState U,
        tr[jCur] = forwardEntryP stateIn stateOut ∧
        ¬ tr.redundantEntryDSPaper jCur := by
  obtain ⟨jCur, stateIn, stateOut, hcur, hfirst,
    _jPrev, _hlt, _prevIn, _prevOut, _hprev, _hcap⟩ := h
  exact ⟨jCur, stateIn, stateOut, hcur,
    not_redundantEntryDSPaper_forward_of_no_prior tr jCur hcur hfirst⟩


end DuplexSpongeFS.Sponge316

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper_forward_inversion
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper_inverse_inversion
#print axioms OracleSpec.QueryLog.redundantEntryDSPaper_hash_inversion
#print axioms OracleSpec.QueryLog.redundantPaper_forward_capacity_prior
#print axioms OracleSpec.QueryLog.redundantPaper_inverse_capacity_prior
#print axioms DuplexSpongeFS.Sponge316.hasHashEntry_removeRedundantPaper_of_mem
#print axioms DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_of_first
#print axioms DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_forward_of_no_prior
#print axioms DuplexSpongeFS.Sponge316.hasFirstPermCapacityBeforeForwardOutputPaper_current_not_redundant
