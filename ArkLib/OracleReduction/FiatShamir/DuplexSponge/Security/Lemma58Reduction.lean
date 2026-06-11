/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BirthdayBoundPaper
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58Correspondence
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Lemma58Extraction

/-!
# The dedup reduction holds — CO25 Lemma 5.8 unconditionally (issue #316)

`ePaperReduction_holds` discharges `EPaperReduction`, the one remaining
pure-list-combinatorics obligation of the CO25 Lemma 5.8 chain: a log consistent with the
empty cache that exhibits the paper bad event `EPaper` contains an anchored collision.

The proof is the four-arm composition over the structure of `EPaper`:

* the dedup of the log is consistent (`consistentFrom_removeRedundantEntryDSPaper`) and
  carries its own no-redundancy certificate (the subtype's `.2`);
* each `E_dup` arm fires its anchor theorem on the dedup
  (`anchored_of_hash_anchor` / `anchored_of_perm_anchor` / `anchored_of_permInv_anchor`);
* the `E_func` arm is refuted outright (`notFunction_data_impossible`);
* anchoredness of the dedup reflects back to the original log
  (`anchoredFrom_of_removeRedundantEntryDSPaper`).

Feeding this into the conditional assembly
`probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction` yields the unconditional paper
bound `probEvent_EPaper_toReal_le_lemma5_8Bound`: for any `T`-query adversary the logged
trace of the eager lazy carrier exhibits `EPaper` with probability at most
`(7T² − 3T)/(2|U|^C)` — CO25 Lemma 5.8.
-/

open OracleComp OracleSpec

namespace DuplexSpongeFS.EagerLazyDS

open DuplexSpongeFS.Paper

variable {StmtIn : Type} {U : Type} [SpongeUnit U] [SpongeSize]
  [DecidableEq StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]
  [Fintype StmtIn] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]

/-- **The dedup reduction holds.** A log consistent with the empty cache that satisfies
`EPaper` contains an anchored collision against the empty cache. -/
theorem ePaperReduction_holds : EPaperReduction StmtIn U := by
  intro log hcons hE
  classical
  -- the dedup is consistent and carries its own no-redundancy certificate
  have hconsD : ConsistentFrom ((∅, []) : DSCache StmtIn U)
      (Paper.removeRedundantEntryDSPaper log).1 :=
    consistentFrom_removeRedundantEntryDSPaper _ hcons
  have hnr : Paper.NoRedundantEntryDSPaper (Paper.removeRedundantEntryDSPaper log).1 :=
    (Paper.removeRedundantEntryDSPaper log).2
  -- anchoredness of the dedup reflects back to the original log
  refine anchoredFrom_of_removeRedundantEntryDSPaper _ hcons ?_
  -- split `EPaper` into its four arms (defeq exposure of the `let`-destructure)
  have hE' : (Paper.capacitySegmentDupHashPaper log ∨
      Paper.capacitySegmentDupPermPaper log ∨
      Paper.capacitySegmentDupPermInvPaper log) ∨ Paper.notFunctionPaper log := hE
  rcases hE' with (hhash | hperm | hpinv) | hfunc
  · -- `E_hash` arm (Eq. 24)
    have h' : ∃ j : Fin (Paper.removeRedundantEntryDSPaper log).1.length,
        ∃ capSeg : Vector U SpongeSize.C, ∃ stmt : StmtIn,
        (Paper.removeRedundantEntryDSPaper log).1[j] = ⟨.inl stmt, capSeg⟩ ∧
        ∃ j' < j, ∃ stmt',
          (Paper.removeRedundantEntryDSPaper log).1[j'] = ⟨.inl stmt', capSeg⟩ ∨
          (∃ sIn1 sOut1, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inl sIn1), sOut1⟩ ∧ sOut1.capacitySegment = capSeg) ∨
          (∃ sOut2 sIn2, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inr sOut2), sIn2⟩ ∧ sIn2.capacitySegment = capSeg) ∨
          (∃ sIn3 sOut3, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inl sIn3), sOut3⟩ ∧ sIn3.capacitySegment = capSeg) ∨
          (∃ sOut4 sIn4, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inr sOut4), sIn4⟩ ∧ sOut4.capacitySegment = capSeg) := hhash
    obtain ⟨j, capSeg, stmt, hj, hcoin⟩ := h'
    exact anchored_of_hash_anchor hnr hconsD hj hcoin
  · -- `E_p` arm (Eq. 25)
    have h' : ∃ j : Fin (Paper.removeRedundantEntryDSPaper log).1.length,
        ∃ capSeg : Vector U SpongeSize.C,
        (∃ sIn sOut, (Paper.removeRedundantEntryDSPaper log).1[j]
          = ⟨.inr (.inl sIn), sOut⟩ ∧ sOut.capacitySegment = capSeg) ∧
        ((∃ j' < j, ∃ stmt', (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inl stmt', capSeg⟩) ∨
          (∃ j' < j, ∃ sIn1 sOut1, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inl sIn1), sOut1⟩ ∧ sOut1.capacitySegment = capSeg) ∨
          (∃ j' ≤ j, ∃ sOut2 sIn2, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inr sOut2), sIn2⟩ ∧ sIn2.capacitySegment = capSeg) ∨
          (∃ j' ≤ j, ∃ sIn3 sOut3, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inl sIn3), sOut3⟩ ∧ sIn3.capacitySegment = capSeg) ∨
          (∃ j' ≤ j, ∃ sOut4 sIn4, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inr sOut4), sIn4⟩ ∧ sOut4.capacitySegment = capSeg)) := hperm
    obtain ⟨j, capSeg, ⟨sIn, sOut, hj, hcap⟩, hcoin⟩ := h'
    exact anchored_of_perm_anchor hnr hconsD hj hcap hcoin
  · -- `E_pinv` arm (Eq. 26)
    have h' : ∃ j : Fin (Paper.removeRedundantEntryDSPaper log).1.length,
        ∃ capSeg : Vector U SpongeSize.C,
        (∃ sOut sIn, (Paper.removeRedundantEntryDSPaper log).1[j]
          = ⟨.inr (.inr sOut), sIn⟩ ∧ sIn.capacitySegment = capSeg) ∧
        ((∃ j' < j, ∃ stmt', (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inl stmt', capSeg⟩) ∨
          (∃ j' < j, ∃ sIn1 sOut1, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inl sIn1), sOut1⟩ ∧ sOut1.capacitySegment = capSeg) ∨
          (∃ j' < j, ∃ sIn2 sOut2, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inr sOut2), sIn2⟩ ∧
            CanonicalSpongeState.capacitySegment sIn2 = capSeg) ∨
          (∃ j' ≤ j, ∃ sIn3 sOut3, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inl sIn3), sOut3⟩ ∧ sIn3.capacitySegment = capSeg) ∨
          (∃ j' ≤ j, ∃ q a, (Paper.removeRedundantEntryDSPaper log).1[j']
            = ⟨.inr (.inr q), a⟩ ∧
            CanonicalSpongeState.capacitySegment q = capSeg)) := hpinv
    obtain ⟨j, capSeg, ⟨sOut, sIn, hj, hcap⟩, hcoin⟩ := h'
    exact anchored_of_permInv_anchor hnr hconsD hj hcap hcoin
  · -- `E_func` arm: refuted outright
    have h' : ∃ j : Fin (Paper.removeRedundantEntryDSPaper log).1.length,
        ∃ sIn sOut : CanonicalSpongeState U,
        (Paper.removeRedundantEntryDSPaper log).1[j] = ⟨.inr (.inl sIn), sOut⟩ ∧
        ∃ j' < j, ∃ out1 : CanonicalSpongeState U,
          (Paper.removeRedundantEntryDSPaper log).1[j'] = ⟨.inr (.inl sIn), out1⟩ ∨
          ∃ out2 : CanonicalSpongeState U,
            (Paper.removeRedundantEntryDSPaper log).1[j']
              = ⟨.inr (.inr out2), sIn⟩ := hfunc
    obtain ⟨j, sIn, sOut, hj, j', hj'lt, out1, hcase⟩ := h'
    rcases hcase with hA | ⟨out2, hB⟩
    · exact (notFunction_data_impossible hnr hconsD hj hj'lt (Or.inl ⟨out1, hA⟩)).elim
    · exact (notFunction_data_impossible hnr hconsD hj hj'lt (Or.inr ⟨out2, hB⟩)).elim

open DuplexSpongeFS.Paper in
/-- **CO25 Lemma 5.8, unconditional.** For any `T`-query adversary, the probability that
the logged trace of the eager lazy carrier exhibits `EPaper`, in real form, is at most
`(7T² − 3T)/(2|U|^C)`. -/
theorem probEvent_EPaper_toReal_le_lemma5_8Bound
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) => EPaper z.2 |
        (simulateQ lazyDSImpl ((simulateQ loggingOracle P).run)).run'
          ((∅, ([] : List (CanonicalSpongeState U × CanonicalSpongeState U))))]).toReal
      ≤ DuplexSpongeFS.BirthdayBound.lemma5_8Bound U T :=
  probEvent_EPaper_toReal_le_lemma5_8Bound_of_reduction ePaperReduction_holds P T hT

end DuplexSpongeFS.EagerLazyDS

/-! ## The eager side: the repaired residual is a theorem, the channel is unconditional -/

namespace DuplexSpongeFS.BirthdayBoundPaper

open DuplexSpongeFS.BirthdayBound DuplexSpongeFS.Paper
open DuplexSpongeFS.KeyLemmaFoundations
open OracleSpec.QueryLog

variable {StmtIn U : Type} [SpongeUnit U] [SpongeSize] [Fintype U] [DecidableEq U]
  [SampleableType (StmtIn → Vector U SpongeSize.C)]
  [SampleableType (Equiv.Perm (CanonicalSpongeState U))]
  [DecidableEq StmtIn] [Fintype StmtIn]
  [SampleableType (Vector U SpongeSize.C)]
  [DecidableEq (CanonicalSpongeState U)] [Inhabited (CanonicalSpongeState U)]

/-- **The repaired Lemma 5.8 eager residual holds**: the lazy-side bound
`probEvent_EPaper_toReal_le_lemma5_8Bound` transfers across the eager–lazy bridge. -/
theorem lemma5_8EagerPaperResidual_holds : Lemma5_8EagerPaperResidual StmtIn U :=
  lemma5_8EagerPaperResidual_of_lazy fun P T hT =>
    DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound P T hT

/-- **The §5.6 → §5.8 channel, unconditional**: the honest bad events of the eager
`D_𝔖`-carrier game obey the birthday bound — no residual hypotheses. -/
theorem honestBad_birthday_unconditional
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α) (T : ℕ)
    (hT : IsTotalQueryBound P T) (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        ∃ S : Backtrack.S_BT z.2 st₀,
          E_inv_honest z.2 st₀ S ∨ E_fork_honest z.2 st₀ S ∨ E_time_honest z.2 st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ lemma5_8Bound U T :=
  honestBad_birthday_of_paperResidual lemma5_8EagerPaperResidual_holds P T hT st₀

/-- **Claim 5.21, unconditional**: at the CO25 trace length `T = tₕ + 1 + tₚ + L + tₚᵢ`,
the honest bad events are bounded by the exact `claim5_21Bound` consumed by the
`Hyb₀ → Hyb₁` step — no residual hypotheses. -/
theorem honestBad_claim5_21Bound_unconditional
    {α : Type} (P : OracleComp (duplexSpongeChallengeOracle StmtIn U) α)
    (tₕ tₚ tₚᵢ L : ℕ)
    (hT : IsTotalQueryBound P (tₕ + 1 + tₚ + L + tₚᵢ))
    (st₀ : CanonicalSpongeState U) :
    (Pr[ fun z : α × QueryLog (duplexSpongeChallengeOracle StmtIn U) =>
        ∃ S : Backtrack.S_BT z.2 st₀,
          E_inv_honest z.2 st₀ S ∨ E_fork_honest z.2 st₀ S ∨ E_time_honest z.2 st₀ S |
      do
        let c ← (D_DS StmtIn U).sample
        simulateQ ((D_DS StmtIn U).toImpl c)
          ((simulateQ loggingOracle P).run)]).toReal
      ≤ claim5_21Bound U tₕ tₚ tₚᵢ L :=
  honestBad_claim5_21Bound_of_paperResidual lemma5_8EagerPaperResidual_holds
    P tₕ tₚ tₚᵢ L hT st₀

end DuplexSpongeFS.BirthdayBoundPaper

/-! ## Axiom audit — kernel-clean. -/
#print axioms DuplexSpongeFS.EagerLazyDS.ePaperReduction_holds
#print axioms DuplexSpongeFS.EagerLazyDS.probEvent_EPaper_toReal_le_lemma5_8Bound
#print axioms DuplexSpongeFS.BirthdayBoundPaper.lemma5_8EagerPaperResidual_holds
#print axioms DuplexSpongeFS.BirthdayBoundPaper.honestBad_birthday_unconditional
#print axioms DuplexSpongeFS.BirthdayBoundPaper.honestBad_claim5_21Bound_unconditional
