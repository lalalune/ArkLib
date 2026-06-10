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


/-- Natural-index form of `HasFirstPermCapacityBeforeForwardOutputPaper`, for the recursive
`eraseIdx` proof where indices shift left. The guard and the prior witness are both
direction-aware, matching the paper certificates. -/
private def HasFirstPermCapacityBeforeForwardOutputPaperNat
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∃ iCur iPrev : ℕ,
    ∃ curIn curOut prevIn prevOut : CanonicalSpongeState U,
      iPrev < iCur ∧
      tr[iCur]? = some (forwardEntryP curIn curOut) ∧
      (tr[iPrev]? = some (forwardEntryP prevIn prevOut) ∨
        tr[iPrev]? = some (inverseEntryP prevOut prevIn)) ∧
      (prevOut.capacitySegment = curOut.capacitySegment ∨
        prevIn.capacitySegment = curOut.capacitySegment) ∧
      ∀ j, j < iCur →
        tr[j]? ≠ some (forwardEntryP curIn curOut) ∧
          tr[j]? ≠ some (inverseEntryP curOut curIn)

/-- Convert the public finite-index paper witness into the natural-index form. -/
private lemma firstPermNatPaper_of_first
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : HasFirstPermCapacityBeforeForwardOutputPaper tr) :
    HasFirstPermCapacityBeforeForwardOutputPaperNat tr := by
  obtain ⟨jCur, curIn, curOut, hcur, hfirst,
    jPrev, hlt, prevIn, prevOut, hprev, hcap⟩ := h
  have hcur? : tr[jCur.val]? = some (forwardEntryP curIn curOut) := by
    rw [List.getElem?_eq_getElem jCur.isLt]
    simpa only [List.get_eq_getElem] using congrArg some hcur
  have hprev? : tr[jPrev.val]? = some (forwardEntryP prevIn prevOut) ∨
      tr[jPrev.val]? = some (inverseEntryP prevOut prevIn) := by
    rcases hprev with hf | hi
    · exact Or.inl (by
        rw [List.getElem?_eq_getElem jPrev.isLt]
        simpa only [List.get_eq_getElem] using congrArg some hf)
    · exact Or.inr (by
        rw [List.getElem?_eq_getElem jPrev.isLt]
        simpa only [List.get_eq_getElem] using congrArg some hi)
  have hfirstNat : ∀ j, j < jCur.val →
      tr[j]? ≠ some (forwardEntryP curIn curOut) ∧
        tr[j]? ≠ some (inverseEntryP curOut curIn) := by
    intro j hj
    have hjlen : j < tr.length := lt_trans hj jCur.isLt
    constructor
    · intro hsome
      have hraw : tr.get ⟨j, hjlen⟩ = forwardEntryP curIn curOut := by
        rw [List.getElem?_eq_getElem hjlen] at hsome
        exact Option.some.inj hsome
      exact (hfirst ⟨j, hjlen⟩ hj).1 hraw
    · intro hsome
      have hraw : tr.get ⟨j, hjlen⟩ = inverseEntryP curOut curIn := by
        rw [List.getElem?_eq_getElem hjlen] at hsome
        exact Option.some.inj hsome
      exact (hfirst ⟨j, hjlen⟩ hj).2 hraw
  exact ⟨jCur.val, jPrev.val, curIn, curOut, prevIn, prevOut, hlt,
    hcur?, hprev?, hcap, hfirstNat⟩

/-- Convert the natural-index witness back to the broad paper shape. -/
private lemma hasPermCapacityBeforeForwardOutputPaper_of_firstPermNat
    {tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)}
    (h : HasFirstPermCapacityBeforeForwardOutputPaperNat tr) :
    HasPermCapacityBeforeForwardOutputPaper tr := by
  obtain ⟨iCur, iPrev, curIn, curOut, prevIn, prevOut,
    hlt, hcur, hprev, hcap, _hfirst⟩ := h
  obtain ⟨hCurLt, hCurEq⟩ := List.getElem?_eq_some_iff.mp hcur
  rcases hprev with hf | hi
  · obtain ⟨hPrevLt, hPrevEq⟩ := List.getElem?_eq_some_iff.mp hf
    exact ⟨⟨iCur, hCurLt⟩, curIn, curOut, hCurEq,
      ⟨iPrev, hPrevLt⟩, hlt, prevIn, prevOut, Or.inl hPrevEq, hcap⟩
  · obtain ⟨hPrevLt, hPrevEq⟩ := List.getElem?_eq_some_iff.mp hi
    exact ⟨⟨iCur, hCurLt⟩, curIn, curOut, hCurEq,
      ⟨iPrev, hPrevLt⟩, hlt, prevIn, prevOut, Or.inr hPrevEq, hcap⟩


/-- **One-step preservation (paper semantics)**: erasing one paper-redundant entry preserves the
first-perm-capacity collision shape. The erase-current case is impossible (the guard defeats both
paper certificates); the erase-prev case re-anchors through the direction-disjunctive capacity
priors; all other erasures shift indices. -/
private lemma firstPermNatPaper_eraseIdx
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin tr.length) (hred : tr.redundantEntryDSPaper idx)
    (hP : HasFirstPermCapacityBeforeForwardOutputPaperNat tr) :
    HasFirstPermCapacityBeforeForwardOutputPaperNat (tr.eraseIdx idx.val) := by
  classical
  obtain ⟨iCur, iPrev, curIn, curOut, prevIn, prevOut,
    hlt, hcur, hprev, hcap, hfirst⟩ := hP
  by_cases hEraseCur : idx.val = iCur
  · have hidx? : tr[idx.val]? = some (forwardEntryP curIn curOut) := by
      simpa [hEraseCur] using hcur
    have hidxVal : tr[idx] = forwardEntryP curIn curOut := by
      rw [List.getElem?_eq_getElem idx.isLt] at hidx?
      exact Option.some.inj hidx?
    have hred' :
        ∃ j' : Fin tr.length, j' < idx ∧
          (tr[j'] = forwardEntryP curIn curOut ∨
            tr[j'] = inverseEntryP curOut curIn) := by
      unfold OracleSpec.QueryLog.redundantEntryDSPaper at hred
      rw [hidxVal] at hred
      simpa [forwardEntryP, inverseEntryP] using hred
    obtain ⟨j', hj', hcase⟩ := hred'
    have hjCur : j'.val < iCur := by omega
    rcases hcase with hsame | hinv
    · have hsome : tr[j'.val]? = some (forwardEntryP curIn curOut) := by
        rw [List.getElem?_eq_getElem j'.isLt]
        simpa only [List.get_eq_getElem] using congrArg some hsame
      exact False.elim ((hfirst j'.val hjCur).1 hsome)
    · have hsome : tr[j'.val]? = some (inverseEntryP curOut curIn) := by
        rw [List.getElem?_eq_getElem j'.isLt]
        simpa only [List.get_eq_getElem] using congrArg some hinv
      exact False.elim ((hfirst j'.val hjCur).2 hsome)
  · let iCur' := if idx.val < iCur then iCur - 1 else iCur
    have hcur' : (tr.eraseIdx idx.val)[iCur']? = some (forwardEntryP curIn curOut) := by
      by_cases hidxCur : idx.val < iCur
      · have hge : idx.val ≤ iCur - 1 := by omega
        simp only [iCur', hidxCur, ↓reduceIte]
        rw [List.getElem?_eraseIdx_of_ge hge, show iCur - 1 + 1 = iCur by omega, hcur]
      · have hCurIdx : iCur < idx.val := by omega
        simp only [iCur', hidxCur, ↓reduceIte]
        rw [List.getElem?_eraseIdx_of_lt hCurIdx, hcur]
    have hfirst' : ∀ j, j < iCur' →
        (tr.eraseIdx idx.val)[j]? ≠ some (forwardEntryP curIn curOut) ∧
          (tr.eraseIdx idx.val)[j]? ≠ some (inverseEntryP curOut curIn) := by
      intro j hj
      constructor
      · intro hsome
        by_cases hidxCur : idx.val < iCur
        · by_cases hjIdx : j < idx.val
          · have hraw : tr[j]? = some (forwardEntryP curIn curOut) := by
              rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
              exact hsome
            exact (hfirst j (by simp [iCur', hidxCur] at hj; omega)).1 hraw
          · have hraw : tr[j + 1]? = some (forwardEntryP curIn curOut) := by
              have hge : idx.val ≤ j := by omega
              rw [List.getElem?_eraseIdx_of_ge hge] at hsome
              exact hsome
            exact (hfirst (j + 1) (by simp [iCur', hidxCur] at hj; omega)).1 hraw
        · have hCurIdx : iCur < idx.val := by omega
          have hjIdx : j < idx.val := by simp [iCur', hidxCur] at hj; omega
          have hraw : tr[j]? = some (forwardEntryP curIn curOut) := by
            rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
            exact hsome
          exact (hfirst j (by simpa [iCur', hidxCur] using hj)).1 hraw
      · intro hsome
        by_cases hidxCur : idx.val < iCur
        · by_cases hjIdx : j < idx.val
          · have hraw : tr[j]? = some (inverseEntryP curOut curIn) := by
              rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
              exact hsome
            exact (hfirst j (by simp [iCur', hidxCur] at hj; omega)).2 hraw
          · have hraw : tr[j + 1]? = some (inverseEntryP curOut curIn) := by
              have hge : idx.val ≤ j := by omega
              rw [List.getElem?_eraseIdx_of_ge hge] at hsome
              exact hsome
            exact (hfirst (j + 1) (by simp [iCur', hidxCur] at hj; omega)).2 hraw
        · have hCurIdx : iCur < idx.val := by omega
          have hjIdx : j < idx.val := by simp [iCur', hidxCur] at hj; omega
          have hraw : tr[j]? = some (inverseEntryP curOut curIn) := by
            rw [List.getElem?_eraseIdx_of_lt hjIdx] at hsome
            exact hsome
          exact (hfirst j (by simpa [iCur', hidxCur] using hj)).2 hraw
    by_cases hErasePrev : idx.val = iPrev
    · -- the erased entry IS the prior witness: re-anchor through its paper certificate,
      -- in whichever direction the witness held
      rcases hprev with hprevF | hprevI
      · have hidx? : tr[idx.val]? = some (forwardEntryP prevIn prevOut) := by
          simpa [hErasePrev] using hprevF
        have hidxVal : tr[idx] = forwardEntryP prevIn prevOut := by
          rw [List.getElem?_eq_getElem idx.isLt] at hidx?
          exact Option.some.inj hidx?
        obtain ⟨j', hj', stateIn', stateOut', hentry, hcap'⟩ :=
          redundantPaper_forward_capacity_prior
            (tr := tr) (idx := idx) (capSeg := curOut.capacitySegment)
            (stateIn := prevIn) (stateOut := prevOut)
            (by simpa [forwardEntryP] using hidxVal) hred hcap
        have hkeep : (tr.eraseIdx idx.val)[j'.val]? = tr[j'.val]? :=
          List.getElem?_eraseIdx_of_lt (by exact hj')
        have hprev' : (tr.eraseIdx idx.val)[j'.val]? = some (forwardEntryP stateIn' stateOut') ∨
            (tr.eraseIdx idx.val)[j'.val]? = some (inverseEntryP stateOut' stateIn') := by
          rcases hentry with hf | hi
          · exact Or.inl (by
              rw [hkeep, List.getElem?_eq_getElem j'.isLt]
              simpa [forwardEntryP, List.get_eq_getElem] using congrArg some hf)
          · exact Or.inr (by
              rw [hkeep, List.getElem?_eq_getElem j'.isLt]
              simpa [inverseEntryP, List.get_eq_getElem] using congrArg some hi)
        refine ⟨iCur', j'.val, curIn, curOut, stateIn', stateOut',
          ?_, hcur', hprev', hcap', hfirst'⟩
        by_cases hidxCur : idx.val < iCur
        · simp [iCur', hidxCur]
          omega
        · simp [iCur', hidxCur]
          omega
      · have hidx? : tr[idx.val]? = some (inverseEntryP prevOut prevIn) := by
          simpa [hErasePrev] using hprevI
        have hidxVal : tr[idx] = inverseEntryP prevOut prevIn := by
          rw [List.getElem?_eq_getElem idx.isLt] at hidx?
          exact Option.some.inj hidx?
        obtain ⟨j', hj', stateIn', stateOut', hentry, hcap'⟩ :=
          redundantPaper_inverse_capacity_prior
            (tr := tr) (idx := idx) (capSeg := curOut.capacitySegment)
            (stateOut := prevOut) (stateIn := prevIn)
            (by simpa [inverseEntryP] using hidxVal) hred hcap
        have hkeep : (tr.eraseIdx idx.val)[j'.val]? = tr[j'.val]? :=
          List.getElem?_eraseIdx_of_lt (by exact hj')
        have hprev' : (tr.eraseIdx idx.val)[j'.val]? = some (forwardEntryP stateIn' stateOut') ∨
            (tr.eraseIdx idx.val)[j'.val]? = some (inverseEntryP stateOut' stateIn') := by
          rcases hentry with hf | hi
          · exact Or.inl (by
              rw [hkeep, List.getElem?_eq_getElem j'.isLt]
              simpa [forwardEntryP, List.get_eq_getElem] using congrArg some hf)
          · exact Or.inr (by
              rw [hkeep, List.getElem?_eq_getElem j'.isLt]
              simpa [inverseEntryP, List.get_eq_getElem] using congrArg some hi)
        refine ⟨iCur', j'.val, curIn, curOut, stateIn', stateOut',
          ?_, hcur', hprev', hcap', hfirst'⟩
        by_cases hidxCur : idx.val < iCur
        · simp [iCur', hidxCur]
          omega
        · simp [iCur', hidxCur]
          omega
    · -- the erased entry is neither witness: shift indices, preserving the prior's direction
      let iPrev' := if idx.val < iPrev then iPrev - 1 else iPrev
      have hprev' : (tr.eraseIdx idx.val)[iPrev']? = some (forwardEntryP prevIn prevOut) ∨
          (tr.eraseIdx idx.val)[iPrev']? = some (inverseEntryP prevOut prevIn) := by
        by_cases hidxPrev : idx.val < iPrev
        · have hge : idx.val ≤ iPrev - 1 := by omega
          rcases hprev with hf | hi
          · exact Or.inl (by
              simp only [iPrev', hidxPrev, ↓reduceIte]
              rw [List.getElem?_eraseIdx_of_ge hge, show iPrev - 1 + 1 = iPrev by omega, hf])
          · exact Or.inr (by
              simp only [iPrev', hidxPrev, ↓reduceIte]
              rw [List.getElem?_eraseIdx_of_ge hge, show iPrev - 1 + 1 = iPrev by omega, hi])
        · have hPrevIdx : iPrev < idx.val := by omega
          rcases hprev with hf | hi
          · exact Or.inl (by
              simp only [iPrev', hidxPrev, ↓reduceIte]
              rw [List.getElem?_eraseIdx_of_lt hPrevIdx, hf])
          · exact Or.inr (by
              simp only [iPrev', hidxPrev, ↓reduceIte]
              rw [List.getElem?_eraseIdx_of_lt hPrevIdx, hi])
      have hlt' : iPrev' < iCur' := by
        by_cases hidxCur : idx.val < iCur
        · by_cases hidxPrev : idx.val < iPrev
          · simp [iCur', iPrev', hidxCur, hidxPrev]
            omega
          · simp [iCur', iPrev', hidxCur, hidxPrev]
            omega
        · have hidxPrev : ¬ idx.val < iPrev := by omega
          simp [iCur', iPrev', hidxCur, hidxPrev]
          omega
      exact ⟨iCur', iPrev', curIn, curOut, prevIn, prevOut,
        hlt', hcur', hprev', hcap, hfirst'⟩

/-- **Fixpoint preservation (paper semantics)**: dedup preserves the first-perm collision shape
as the broad base-trace shape. -/
private lemma firstPermNatPaper_removeRedundant :
    ∀ (N : ℕ) (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)), tr.length ≤ N →
      HasFirstPermCapacityBeforeForwardOutputPaperNat tr →
        HasPermCapacityBeforeForwardOutputPaper (removeRedundantEntryDSPaper tr).1 := by
  intro N
  induction N with
  | zero =>
      intro tr hlen hP
      obtain ⟨iCur, _iPrev, _cI, _cO, _pI, _pO, _hlt, hcur, _⟩ := hP
      have hlen0 : tr.length = 0 := Nat.le_zero.mp hlen
      rw [List.length_eq_zero_iff.mp hlen0] at hcur
      simp at hcur
  | succ N ih =>
      intro tr hlen hP
      rw [removeRedundantEntryDSPaper]
      split
      · rename_i hex
        refine ih _ ?_ (firstPermNatPaper_eraseIdx tr (Classical.choose hex)
          (Classical.choose_spec hex) hP)
        have hlt := (Classical.choose hex).isLt
        have hsucc := List.length_eraseIdx_add_one hlt
        omega
      · exact hasPermCapacityBeforeForwardOutputPaper_of_firstPermNat hP

/-- **Public dedup bridge (paper semantics)**: a raw first-occurrence perm-capacity collision
survives `removeRedundantEntryDSPaper` as the broad base-trace shape. -/
theorem hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstPermCapacityBeforeForwardOutputPaper tr) :
    HasPermCapacityBeforeForwardOutputPaper (removeRedundantEntryDSPaper tr).1 :=
  firstPermNatPaper_removeRedundant tr.length tr le_rfl (firstPermNatPaper_of_first h)


/-- **The reshaped keystone (paper semantics)**: a raw first-occurrence permutation-capacity
collision forces the paper capacity-collision event `E_p` — every direction/side combination of
the transported prior witness lands in one of `capacitySegmentDupPerm`'s disjuncts. -/
theorem e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstPermCapacityBeforeForwardOutputPaper tr) :
    BadEventDSPaper.E_p tr := by
  have hbase := hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first tr h
  obtain ⟨jCur, curIn, curOut, hcur, jPrev, hlt, prevIn, prevOut, hprev, hcap⟩ := hbase
  unfold BadEventDSPaper.E_p BadEventDSPaper.capacitySegmentDupPerm
  refine ⟨jCur, curOut.capacitySegment, ⟨curIn, curOut, hcur, rfl⟩, ?_⟩
  rcases hprev with hf | hi
  · rcases hcap with hout | hin
    · -- prior forward, output side: disjunct 2
      exact Or.inr (Or.inl ⟨jPrev, hlt, prevIn, prevOut, hf, hout⟩)
    · -- prior forward, input side: disjunct 4
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨jPrev, le_of_lt hlt, prevIn, prevOut, hf, hin⟩)))
  · rcases hcap with hout | hin
    · -- prior inverse, output side: disjunct 5
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨jPrev, le_of_lt hlt, prevOut, prevIn, hi, hout⟩)))
    · -- prior inverse, input side: disjunct 3
      exact Or.inr (Or.inr (Or.inl ⟨jPrev, le_of_lt hlt, prevOut, prevIn, hi, hin⟩))

/-- The reshaped keystone, composed into the combined paper bad event `E`. -/
theorem e_of_hasFirstPermCapacityBeforeForwardOutputPaper
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (h : HasFirstPermCapacityBeforeForwardOutputPaper tr) :
    BadEventDSPaper.E tr :=
  Or.inl (Or.inr (Or.inl (e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper tr h)))


/-! ## The honest residuals, re-stated against paper semantics

The legacy `Lemma5_14HonestResidual` / `Lemma5_16HonestResidual` are REFUTED as stated
(machine-checked countermodels exploiting the legacy dedup's certificate deviation). These are
the same confinement statements against the **paper-faithful** combined event
`BadEventDSPaper.E` — correctly stated, honestly OPEN named Props awaiting discharge against
the repaired semantics. The honest events themselves (`E_inv_honest`/`E_fork_honest`/
`E_time_honest`) are dedup-independent and unchanged. -/

open DuplexSpongeFS.KeyLemmaFoundations in
/-- CO25 Lemma 5.12 (honest form), **paper semantics**: off the paper combined bad event, no
BackTrack chain step is anchored by an inverse-permutation entry. -/
def Lemma5_12HonestResidualPaper (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ BadEventDSPaper.E tr → ¬ E_inv_honest tr state S

open DuplexSpongeFS.KeyLemmaFoundations in
/-- CO25 Lemma 5.14 (honest form), **paper semantics**: off the paper combined bad event, the
backtrack family has at most one maximal sequence. Replaces the refuted legacy form. -/
def Lemma5_14HonestResidualPaper (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ BadEventDSPaper.E tr → ¬ E_fork_honest tr state S

open DuplexSpongeFS.KeyLemmaFoundations in
/-- CO25 Lemma 5.16 (honest form), **paper semantics**: off the paper combined bad event, all
chain queries appear in trace order. Replaces the refuted legacy form; the `E_{time,h}` half's
legacy proof (`Lemma516HashHalf.lean`) is a transfer candidate since the hash-arm certificates
coincide across semantics. -/
def Lemma5_16HonestResidualPaper (StmtIn U : Type) [SpongeUnit U] [SpongeSize] : Prop :=
  ∀ (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (S : Backtrack.S_BT tr state),
    ¬ BadEventDSPaper.E tr → ¬ E_time_honest tr state S


/-! ## Hash-anchored collision machinery (paper semantics) — toward the 5.16 hash half -/

/-- A hash slot that is the first occurrence of its concrete entry is not paper-redundant
(the hash certificate coincides across semantics). -/
theorem not_redundantEntryDSPaper_hash_of_no_prior
    (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U)) (idx : Fin tr.length)
    {stmt : StmtIn} {capSeg : Vector U SpongeSize.C}
    (hidx : tr[idx] =
      (⟨Sum.inl stmt, capSeg⟩ :
        OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U)))
    (hfirst : ∀ j : Fin tr.length, j.val < idx.val →
      tr[j] ≠
        (⟨Sum.inl stmt, capSeg⟩ :
          OracleSpec.duplexSpongeTraceEntry (StartType := StmtIn) (U := U))) :
    ¬ tr.redundantEntryDSPaper idx := by
  intro hred
  unfold OracleSpec.QueryLog.redundantEntryDSPaper at hred
  rw [hidx] at hred
  obtain ⟨j, hjlt, hj⟩ := hred
  exact hfirst j hjlt hj

/-- ℕ-indexed first-hash collision shape, paper semantics: the hash anchor is first-occurrence,
and an earlier **permutation entry in either direction** shares the anchor capacity on either
side of its pair. Generalizes `HasFirstHashFwdCapNat` — under paper certificates the permutation
witness can re-anchor across directions during dedup. -/
def HasFirstHashPermCapNatPaper (tr : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (stmt : StmtIn) (capSeg : Vector U SpongeSize.C) : Prop :=
  ∃ jh jp : ℕ, jp < jh ∧
    tr[jh]? = some (hashEntryP stmt capSeg) ∧
    (∀ k, k < jh → tr[k]? ≠ some (hashEntryP stmt capSeg)) ∧
    ∃ sIn sOut : CanonicalSpongeState U,
      (tr[jp]? = some (forwardEntryP sIn sOut) ∨
        tr[jp]? = some (inverseEntryP sOut sIn)) ∧
      (sOut.capacitySegment = capSeg ∨ sIn.capacitySegment = capSeg)


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
#print axioms DuplexSpongeFS.Sponge316.hasPermCapacityBeforeForwardOutputPaper_removeRedundant_of_first
#print axioms DuplexSpongeFS.Sponge316.e_p_of_hasFirstPermCapacityBeforeForwardOutputPaper
#print axioms DuplexSpongeFS.Sponge316.e_of_hasFirstPermCapacityBeforeForwardOutputPaper
#print axioms DuplexSpongeFS.Sponge316.not_redundantEntryDSPaper_hash_of_no_prior
