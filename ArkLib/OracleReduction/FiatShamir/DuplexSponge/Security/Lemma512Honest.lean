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
#print axioms DuplexSpongeFS.Sponge316.not_inv_getElem?_of_not_E
#print axioms DuplexSpongeFS.Sponge316.lemma5_12_honest
