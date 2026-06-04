/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.SeqCompose
import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Sequential Composition of Two (Oracle) Reductions

  This file gives the definition & properties of the sequential composition of two (oracle)
  reductions. For composition to be valid, we need that the output context (statement + oracle
  statement + witness) for the first (oracle) reduction is the same as the input context for the
  second (oracle) reduction.

  We have refactored the composition logic for `ProtocolSpec` and its associated structures into
  `ProtocolSpec.lean`, and we will use the definitions from there.

  We will prove that the composition of reductions preserve all completeness & soundness properties
  of the reductions being composed (with extra conditions on the extractor).
-/

open OracleComp OracleSpec SubSpec

universe u v

section find_home

variable {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {α β : Type}
    (oa : OracleComp spec α)

end find_home

open ProtocolSpec

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/--
Appending two provers corresponding to two reductions, where the output statement & witness type for
the first prover is equal to the input statement & witness type for the second prover. We also
require a verifier for the first protocol in order to derive the intermediate statement for the
second prover.

This is defined by combining the two provers' private states and functions, with the exception that
the last private state of the first prover is "merged" into the first private state of the second
prover (via outputting the new statement and witness, and then inputting these into the second
prover). -/
def Prover.append (P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Prover oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where

  /- The combined prover's states are the concatenation of the first prover's states and the second
  prover's states (except the first one). -/
  PrvState := Fin.append (m := m + 1) P₁.PrvState (Fin.tail P₂.PrvState) ∘ Fin.cast (by omega)

  /- The combined prover's input function is the first prover's input function, except for when the
  first protocol is empty, in which case it is the second prover's input function -/
  input := fun ctxIn => by
    simp only [Function.comp_apply, Fin.cast_zero]
    exact P₁.input ctxIn

  /- The combined prover sends messages according to the round index `i` as follows:
  - if `i < m`, then it sends the message & updates the state as the first prover
  - if `i = m`, then it sends the message as the first prover, but further returns the beginning
    state of the second prover
  - if `i > m`, then it sends the message & updates the state as the second prover. -/
  sendMessage := fun ⟨i, hDir⟩ state => by
    dsimp [Fin.vappend_eq_append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := by omega
      simp [hi, Fin.vappend_left_of_lt] at hDir ⊢
      simp [this] at state
      exact P₁.sendMessage ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp [hi', Fin.vappend_right_of_not_lt] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.sendMessage ⟨⟨0, by omega⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := by omega
        haveI hi2 : i - (m + 1) + 1 = i - m := by omega
        simp [hi, Fin.vappend_right_of_not_lt] at hDir ⊢
        simp [hi1] at state
        exact P₂.sendMessage ⟨⟨i - m, by omega⟩, hDir⟩ (dcast (by simp [hi2]) state)

  /- Receiving challenges is implemented essentially the same as sending messages, modulo the
  difference in direction. -/
  receiveChallenge := fun ⟨i, hDir⟩ state => by
    dsimp [ProtocolSpec.append, Fin.append, Fin.addCases, Fin.tail,
      Fin.cast, Fin.castLT, Fin.succ, Fin.castSucc] at hDir state ⊢
    by_cases hi : i < m
    · haveI : i < m + 1 := by omega
      simp only [hi, Fin.vappend_left_of_lt, dif_pos (show ↑i + 1 < m + 1 by omega)] at hDir ⊢
      simp only [this, dif_pos] at state
      exact P₁.receiveChallenge ⟨⟨i, hi⟩, hDir⟩ state
    · by_cases hi' : i = m
      · simp [hi', Fin.vappend_right_of_not_lt] at hDir state ⊢
        exact (do
          let ctxIn₂ ← P₁.output state
          letI state₂ := P₂.input ctxIn₂
          P₂.receiveChallenge ⟨⟨0, by omega⟩, hDir⟩ state₂)
      · haveI hi1 : ¬ i < m + 1 := by omega
        haveI hi2 : i - (m + 1) + 1 = i - m := by omega
        simp [hi, Fin.vappend_right_of_not_lt] at hDir ⊢
        simp [hi1] at state
        exact P₂.receiveChallenge ⟨⟨i - m, by omega⟩, hDir⟩ (dcast (by simp [hi2]) state)

  /- The combined prover's output function has two cases:
  - if the second protocol is empty, then it is the composition of the first prover's output
    function, the second prover's input function, and the second prover's output function.
  - if the second protocol is non-empty, then it is the second prover's output function. -/
  output := fun state => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.cast, Fin.last, Fin.subNat] at state
    by_cases hn : n = 0
    · simp only [hn, Nat.add_zero, dif_pos (show m < m + 1 from lt_add_one m)] at state
      exact (do
        let ctxIn₂ ← P₁.output state
        letI state₂ := P₂.input ctxIn₂
        P₂.output (dcast (by simp [hn]) state₂))
    · haveI : m + n - (m + 1) + 1 = n := by omega
      simp only [Order.lt_add_one_iff, add_le_iff_nonpos_right, nonpos_iff_eq_zero, hn, ↓reduceDIte,
        eq_rec_constant] at state
      exact P₂.output (dcast (by simp [this, Fin.last]) state)

/-- Composition of verifiers. Return the conjunction of the decisions of the two verifiers. -/
def Verifier.append (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂) :
      Verifier oSpec Stmt₁ Stmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt transcript => do
    return ← V₂.verify (← V₁.verify stmt transcript.fst) transcript.snd

/-- Composition of reductions boils down to composing the provers and verifiers. -/
def Reduction.append (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂) :
      Reduction oSpec Stmt₁ Wit₁ Stmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := Verifier.append R₁.verifier R₂.verifier

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
  {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
  {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]

open Function Embedding in
def OracleVerifier.append (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun stmt challenges => by
    -- First, invoke the first oracle verifier, handling queries as necessary
    have := V₁.verify stmt (fun chal =>
      by
        simpa [ChallengeIdx.inl, ProtocolSpec.append] using challenges (ChallengeIdx.inl chal))
    simp at this
    -- Then, invoke the second oracle verifier, handling queries as necessary
    -- Return the final output statement
    sorry

  -- Need to provide an embedding `ιₛ₃ ↪ ιₛ₁ ⊕ (pSpec₁ ++ₚ pSpec₂).MessageIdx`
  embed :=
    -- `ιₛ₃ ↪ ιₛ₂ ⊕ pSpec₂.MessageIdx`
    .trans V₂.embed <|
    -- `ιₛ₂ ⊕ pSpec₂.MessageIdx ↪ (ιₛ₁ ⊕ pSpec₁.MessageIdx) ⊕ pSpec₂.MessageIdx`
    .trans (.sumMap V₁.embed (.refl _)) <|
    -- re-associate the sum `_ ↪ ιₛ₁ ⊕ (pSpec₁.MessageIdx ⊕ pSpec₂.MessageIdx)`
    .trans (Equiv.sumAssoc _ _ _).toEmbedding <|
    -- use the equivalence `pSpec₁.MessageIdx ⊕ pSpec₂.MessageIdx ≃ (pSpec₁ ++ₚ pSpec₂).MessageIdx`
    .sumMap (.refl _) MessageIdx.sumEquiv.toEmbedding

  hEq := fun i => by
    rcases h : V₂.embed i with j | j
    · rcases h' : V₁.embed j with k | k
      · have h1 := V₁.hEq j
        have h2 := V₂.hEq i
        simp [h, h'] at h1 h2 ⊢
        exact h2.trans h1
      · have h1 := V₁.hEq j
        have h2 := V₂.hEq i
        simp [h, h', MessageIdx.inl] at h1 h2 ⊢
        exact h2.trans h1
    · have := V₂.hEq i
      simp [h] at this ⊢
      simp [this, MessageIdx.inr]

@[simp]
lemma OracleVerifier.append_toVerifier
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      (OracleVerifier.append V₁ V₂).toVerifier =
        Verifier.append V₁.toVerifier V₂.toVerifier := sorry

/-- Sequential composition of oracle reductions is just the sequential composition of the oracle
  provers and oracle verifiers. -/
def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

@[simp]
lemma OracleReduction.append_toReduction
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      (OracleReduction.append R₁ R₂).toReduction =
        Reduction.append R₁.toReduction R₂.toReduction := by
  ext : 1 <;> simp [toReduction, OracleReduction.append, Reduction.append]

end OracleProtocol

/-! Sequential composition of extractors and state functions

These have the following form: they needs to know the first verifier, and derive the intermediate
statement from running the first verifier on the first statement.

This leads to complications: the verifier is assumed to be a general `OracleComp oSpec`, and so
we also need to have the extractors and state functions to be similarly `OracleComp`s.

The alternative is to consider a fully deterministic (and non-failing) verifier. The non-failing
part is somewhat problematic as we write our verifiers to be able to fail (i.e. implicit failing
via `guard` statements).

As such, the definitions below are temporary until further development. -/

namespace Extractor

/-- The sequential composition of two straightline extractors.

TODO: state a monotone condition on the extractor, namely that if extraction succeeds on a given
query log, then it also succeeds on any extension of that query log -/
def Straightline.append (E₁ : Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₂ pSpec₁)
    (E₂ : Extractor.Straightline oSpec Stmt₂ Wit₂ Wit₃ pSpec₂)
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) :
      Extractor.Straightline oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂) :=
  fun stmt₁ wit₃ transcript proveQueryLog verifyQueryLog => do
    let stmt₂ ← V₁.verify stmt₁ transcript.fst
    let wit₂ ← E₂ stmt₂ wit₃ transcript.snd proveQueryLog verifyQueryLog
    let wit₁ ← E₁ stmt₁ wit₂ transcript.fst proveQueryLog verifyQueryLog
    return wit₁

/-- The round-by-round extractor for the sequential composition of two (oracle) reductions -/
def RoundByRound.append
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂) :
      Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₃ (pSpec₁ ++ₚ pSpec₂)
        (Fin.append (m := m + 1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) where
  eqIn := by
    simp only [Function.comp_apply, Fin.cast_zero]
    exact E₁.eqIn
  extractMid := fun idx stmt₁ tr h => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast] at h ⊢
    by_cases hi : idx < m
    · simp [hi] at h
      have hiSucc : (idx : ℕ) < m + 1 := by omega
      simpa [hiSucc] using E₁.extractMid ⟨idx, hi⟩ stmt₁ (by simpa [hi] using tr.fst) h
    -- do casing
    sorry
  extractOut := fun stmt₁ tr wit₃ => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
    sorry

end Extractor

namespace Verifier

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- The sequential composition of two state functions. -/
def StateFunction.append
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    -- Assume the first verifier is deterministic for now
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) :
      (V₁.append V₂).StateFunction init impl lang₁ lang₃ where
  toFun := fun roundIdx stmt₁ transcript =>
    if h : roundIdx.val ≤ m then
    -- If the round index falls in the first protocol, then we simply invokes the first state fn
      S₁ ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst)
    else
    -- If the round index falls in the second protocol, then we returns the conjunction of
    -- the first state fn on the first protocol's transcript, and the second state fn on the
    -- remaining transcript.
      S₁ ⟨m, by omega⟩ stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst) ∧
      S₂ ⟨roundIdx - m, by omega⟩ (verify stmt₁
        (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst))
        (by simpa [h] using transcript.snd)
  toFun_empty := by
    intro stmt
    split
    · constructor <;> intro h
      · have h' := (S₁.toFun_empty stmt).mp h
        convert h' using 2; exact funext fun i => i.elim0
      · exact (S₁.toFun_empty stmt).mpr (by convert h using 2; exact funext fun i => i.elim0)
    · exact absurd (Nat.zero_le m) ‹_›
  toFun_next := by
    intro roundIdx hDir stmt₁ tr hPrev msg
    by_cases hlt : (roundIdx : ℕ) < m
    · -- first segment: roundIdx.succ ≤ m, both branches are `then`
      have hsucc : (roundIdx : ℕ) + 1 ≤ m := hlt
      have hcs : (roundIdx : ℕ) ≤ m := le_of_lt hlt
      simp only [Fin.val_succ, Fin.coe_castSucc] at *
      rw [dif_pos hsucc] at *
      rw [dif_pos hcs] at hPrev
      have hDir₁ : pSpec₁.dir ⟨roundIdx, hlt⟩ = .P_to_V := by
        have := hDir
        rw [show ((pSpec₁.dir ++ᵛ pSpec₂.dir) roundIdx)
              = pSpec₁.dir ⟨roundIdx, hlt⟩ from Fin.vappend_left_of_lt _ _ _ hlt] at this
        exact this
      have hmsgty : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩ := by
        show Fin.vappend pSpec₁.Type pSpec₂.Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩
        rw [Fin.vappend_left_of_lt _ _ _ hlt]
      have key := S₁.toFun_next ⟨roundIdx, hlt⟩ hDir₁ stmt₁ _ hPrev (cast hmsgty msg)
      convert key using 2
      apply eq_of_heq
      apply HEq.trans (b := (Transcript.concat msg tr).fst)
      · exact cast_heq _ _
      · -- (concat msg tr).fst ≍ concat (cast hmsgty msg) (castP.mp tr.fst)
        apply Function.hfunext
        · congr 1
          simp only [Fin.val_succ]
          omega
        · intro a a' haa'
          have hav : a.val = a'.val := by
            have := Fin.heq_ext_iff (by simp only [Fin.val_succ]; omega) |>.mp haa'
            omega
          simp only [Transcript.concat, Transcript.fst]
          refine HEq.trans (cast_heq _ _) ?_
          -- goal: Fin.snoc tr msg ⟨a.val,_⟩ ≍ Fin.snoc (castP tr.fst) (cast msg) a'
          -- replace the implicit index proof on the LHS by an explicit one
          obtain ⟨av, hav_lt⟩ := a
          simp only [Fin.val_mk, Fin.val_succ] at hav hav_lt ⊢
          rw [show min ((roundIdx : ℕ) + 1) m = (roundIdx : ℕ) + 1 from by omega] at hav_lt
          have ha'_lt : (a' : ℕ) < (roundIdx : ℕ) + 1 := by
            have := a'.isLt; simpa [Fin.val_succ] using this
          simp only [Fin.snoc, Fin.val_mk]
          have hav' : (a' : ℕ) = av := hav.symm
          by_cases hlast : av = roundIdx
          · -- last position: both snocs yield the message
            rw [dif_neg (show ¬ av < roundIdx from by omega),
                dif_neg (show ¬ (a' : ℕ) < roundIdx from by omega)]
            exact HEq.trans (cast_heq _ _)
              (HEq.trans (cast_heq hmsgty msg).symm (cast_heq _ _).symm)
          · -- earlier position: both snocs yield the underlying transcript value
            have hlt' : av < roundIdx := by omega
            rw [dif_pos (show av < roundIdx from hlt'),
                dif_pos (show (a' : ℕ) < roundIdx from by omega)]
            -- goal: cast _ (tr (⟨av,_⟩.castLT _)) ≍ cast _ (castP.mp (Transcript.fst tr) (a'.castLT _))
            refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
            -- goal: tr (⟨av,_⟩.castLT _) ≍ castP.mp (Transcript.fst tr) (a'.castLT _)
            -- strip the function cast `castP.mp` and unfold `Transcript.fst`
            have hmincard : min (roundIdx : ℕ) m = (roundIdx : ℕ) := by omega
            have hFstHeq : (by simpa [hcs] using tr.fst : pSpec₁.Transcript ⟨roundIdx, by omega⟩)
                ≍ Transcript.fst tr := cast_heq _ _
            refine HEq.trans ?_ (dcongr_heq (f₁ := Transcript.fst tr)
              (a₁ := (⟨av, by omega⟩ : Fin (min (roundIdx : ℕ) m)))
              (a₂ := (a'.castLT (show (a' : ℕ) < roundIdx from by omega)))
              (Fin.heq_ext_iff hmincard |>.mpr (by simpa using hav))
              (fun t₁ t₂ ht => by
                have hv : (t₁ : ℕ) = (t₂ : ℕ) := Fin.val_eq_val_of_heq ht
                show pSpec₁.Type _ = pSpec₁.Type _
                congr 1
                ext
                simpa using hv)
              (fun _ _ => HEq.symm hFstHeq))
            -- goal: tr (⟨av,_⟩.castLT _) ≍ Transcript.fst tr ⟨av, _⟩
            unfold Transcript.fst
            refine HEq.trans ?_ (cast_heq _ _).symm
            congr 1
    · -- second segment: roundIdx ≥ m
      push_neg at hlt
      have hnsucc : ¬ ((roundIdx : ℕ) + 1 ≤ m) := by omega
      simp only [Fin.val_succ, Fin.coe_castSucc] at *
      rw [dif_neg hnsucc] at *
      -- the first-segment part of the transcript is unchanged by concatenating a 2nd-segment round
      -- the first-segment fst is unchanged by concatenating a 2nd-segment round (HEq form)
      have hfstHeq : (Transcript.concat msg tr).fst ≍ tr.fst := by
        have hmr : m ≤ (roundIdx : ℕ) := hlt
        have hcard : min ((roundIdx : Fin (m + n)).succ : ℕ) m
            = min ((roundIdx : Fin (m + n)).castSucc : ℕ) m := by
          simp only [Fin.val_succ, Fin.coe_castSucc]; omega
        -- (concat msg tr).fst ≍ tr.fst   (over their min-indexed domains)
        apply Function.hfunext
        · congr 1
        · intro a a' haa'
          have hav : (a : ℕ) = (a' : ℕ) := by
            have := Fin.heq_ext_iff hcard |>.mp haa'
            omega
          simp only [Transcript.concat, Transcript.fst]
          obtain ⟨av, hav_lt⟩ := a
          simp only [Fin.val_mk, Fin.val_succ] at hav hav_lt ⊢
          rw [show min ((roundIdx : ℕ) + 1) m = m from by omega] at hav_lt
          refine HEq.trans (cast_heq _ _) ?_
          refine HEq.trans ?_ (cast_heq _ _).symm
          -- Fin.snoc tr msg ⟨av,_⟩ ≍ tr ⟨av,_⟩  since av < m ≤ roundIdx
          simp only [Fin.snoc, Fin.val_mk]
          rw [dif_pos (show av < roundIdx from by omega)]
          refine HEq.trans (cast_heq _ _) ?_
          congr 1
          ext; simp only [Fin.val_castLT]; omega
      rintro ⟨hS1, hS2⟩
      by_cases hrm : (roundIdx : ℕ) ≤ m
      · -- roundIdx = m: hPrev is the first-segment state fn, contradicted by hS1
        rw [dif_pos hrm] at hPrev
        apply hPrev
        have hrm' : (roundIdx : ℕ) = m := by omega
        convert hS1 using 2
        exact HEq.trans (cast_heq _ _) (HEq.trans hfstHeq.symm (cast_heq _ _).symm)
      · -- roundIdx > m: derive both conjuncts and contradict hPrev's `else` branch
        rw [dif_neg hrm] at hPrev
        apply hPrev
        refine ⟨?_, ?_⟩
        · -- S₁ conjunct: same as hS1 up to the unchanged first-segment transcript
          convert hS1 using 2
          exact eq_of_heq (HEq.trans (cast_heq _ _) (HEq.trans hfstHeq.symm (cast_heq _ _).symm))
        · -- S₂ conjunct: from hS2 via toFun_next contrapositive on the second segment
          have hmlt : m < (roundIdx : ℕ) := by omega
          have hfstCast :
              (by simpa [min_eq_right_of_lt (show m < (roundIdx : ℕ) + 1 from by omega)]
                  using (Transcript.concat msg tr).fst : pSpec₁.Transcript ⟨m, by omega⟩)
              = (by simpa [min_eq_right_of_lt hmlt]
                  using tr.fst : pSpec₁.Transcript ⟨m, by omega⟩) :=
            eq_of_heq (HEq.trans (cast_heq _ _) (HEq.trans hfstHeq (cast_heq _ _).symm))
          -- the second-segment direction at this round
          have hDir₂ : pSpec₂.dir ⟨(roundIdx : ℕ) - m, by omega⟩ = .P_to_V := by
            have h2 := hDir
            rw [show ((pSpec₁.dir ++ᵛ pSpec₂.dir) roundIdx)
                  = pSpec₂.dir ⟨(roundIdx : ℕ) - m, by omega⟩
                from by rw [Fin.vappend_right_of_not_lt _ _ _ (by omega : ¬ (roundIdx : ℕ) < m)]] at h2
            exact h2
          -- the message transported into the second segment's type
          have hmsgty₂ : (pSpec₁ ++ₚ pSpec₂).Type roundIdx
              = pSpec₂.Type ⟨(roundIdx : ℕ) - m, by omega⟩ := by
            show Fin.vappend pSpec₁.Type pSpec₂.Type roundIdx = _
            rw [Fin.vappend_right_of_not_lt _ _ _ (by omega : ¬ (roundIdx : ℕ) < m)]
          -- apply toFun_next contrapositive: from hS2 (at succ) get the state fn at castSucc
          apply Classical.byContradiction
          intro hnot
          have key := S₂.toFun_next ⟨(roundIdx : ℕ) - m, by omega⟩ hDir₂ _ tr.snd hnot
            (cast hmsgty₂ msg)
          -- key : ¬ S₂.toFun (succ) (verify ... tr.fst) (tr.snd.concat msg₂)
          apply key
          convert hS2 using 2
          all_goals
            try exact hfstCast.symm
          all_goals
            try (simp only [Fin.val_succ, Fin.val_mk]; omega)
          -- remaining: (tr.snd).concat msg₂  ≍  (concat msg tr).snd
          -- the second-segment snd gains exactly the new message via snoc
          have hsndcard : ((roundIdx : ℕ) - m) + 1 = ((roundIdx : Fin (m + n)).succ : ℕ) - m := by
            simp only [Fin.val_succ]; omega
          apply Function.hfunext
          · congr 1
          · intro a a' haa'
            -- a : Fin ((roundIdx - m) + 1),  a' : Fin (roundIdx.succ - m)
            have haa : (a : ℕ) = (a' : ℕ) := by
              have := Fin.heq_ext_iff hsndcard |>.mp haa'
              omega
            simp only [Transcript.concat]
            -- evaluate both snocs / snd by casing on the position
            obtain ⟨av, hav_lt⟩ := a
            simp only [Fin.val_mk] at haa hav_lt ⊢
            -- unfold the right `snd` (over the snoc'd transcript)
            unfold Transcript.snd
            rw [dif_neg (show ¬ (roundIdx : Fin (m + n)).succ ≤ m from by
                  simp only [Fin.le_def, Fin.val_succ]; omega),
                dif_neg (show ¬ (roundIdx : Fin (m + n)).castSucc ≤ m from by
                  simp only [Fin.le_def, Fin.coe_castSucc]; omega)]
            simp only [Fin.snoc, Fin.val_mk]
            by_cases hlast : av = (roundIdx : ℕ) - m
            · -- last position: snoc gives msg; snd reads the snoc'd entry at index roundIdx
              rw [dif_neg (show ¬ av < (roundIdx : ℕ) - m from by omega),
                  dif_neg (show ¬ m + (a' : ℕ) < (roundIdx : ℕ) from by omega)]
              refine HEq.trans (cast_heq _ _) ?_
              refine HEq.trans ?_ (cast_heq _ _).symm
              refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
              rfl
            · -- earlier position: snoc gives tr.snd value; snd reads tr at index m+av
              have hlt2 : av < (roundIdx : ℕ) - m := by omega
              rw [dif_pos (show av < (roundIdx : ℕ) - m from hlt2),
                  dif_pos (show m + (a' : ℕ) < (roundIdx : ℕ) from by omega)]
              refine HEq.trans (cast_heq _ _) ?_
              refine HEq.trans ?_ (cast_heq _ _).symm
              refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
              congr 1
              ext
              simp only [Fin.val_castLT]
              omega
  toFun_full := sorry

end Verifier

section Execution

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

-- #print Prover.processRound

-- theorem append_processRound (roundIdx : Fin (m + n)) (stmt : Stmt₁) (wit : Wit₁)
--     (transcript : pSpec₁.FullTranscript) (proveQueryLog : Set (Stmt₁ × Wit₁))
--     (verifyQueryLog : Set (Stmt₂ × Wit₂)) :
--       (P₁.append P₂).processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog =
--         (P₁.processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog) ∧
--         (P₂.processRound roundIdx stmt wit transcript proveQueryLog verifyQueryLog) := placeholder

-- theorem append_runToRound

/-- The challenge type at index `i` of the left protocol coincides with the challenge type at the
  embedded index `ChallengeIdx.inl i` of the appended protocol. This is the response-type equality
  underlying the `SubSpec` inclusion of the left challenge oracle into the appended one. -/
private theorem range_challenge_append_inl (i : pSpec₁.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨ChallengeIdx.inl i, ()⟩
      = [pSpec₁.Challenge]ₒ.Range ⟨i, ()⟩ := by
  show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl i) = pSpec₁.Challenge i
  simp [ChallengeIdx.inl, ProtocolSpec.append]

/-- The challenge type at index `i` of the right protocol coincides with the challenge type at the
  embedded index `ChallengeIdx.inr i` of the appended protocol. This is the response-type equality
  underlying the `SubSpec` inclusion of the right challenge oracle into the appended one. -/
private theorem range_challenge_append_inr (i : pSpec₂.ChallengeIdx) :
    [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨ChallengeIdx.inr i, ()⟩
      = [pSpec₂.Challenge]ₒ.Range ⟨i, ()⟩ := by
  show (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inr i) = pSpec₂.Challenge i
  simp [ChallengeIdx.inr, ProtocolSpec.append]

/-- The left protocol's challenge oracle is a sub-spec of the appended protocol's challenge oracle:
  a query to challenge round `i` of `pSpec₁` is forwarded to round `ChallengeIdx.inl i` of
  `pSpec₁ ++ₚ pSpec₂`, with responses transported back along `range_challenge_append_inl`. -/
instance : [(pSpec₁).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  monadLift := fun q => ⟨⟨ChallengeIdx.inl q.input.1, ()⟩,
    q.cont ∘ (fun r => (range_challenge_append_inl q.input.1) ▸ r)⟩
  onQuery := fun t => ⟨ChallengeIdx.inl t.1, ()⟩
  onResponse := fun t r => (range_challenge_append_inl t.1) ▸ r

/-- The right protocol's challenge oracle is a sub-spec of the appended protocol's challenge oracle:
  a query to challenge round `i` of `pSpec₂` is forwarded to round `ChallengeIdx.inr i` of
  `pSpec₁ ++ₚ pSpec₂`, with responses transported back along `range_challenge_append_inr`. -/
instance : [(pSpec₂).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ where
  monadLift := fun q => ⟨⟨ChallengeIdx.inr q.input.1, ()⟩,
    q.cont ∘ (fun r => (range_challenge_append_inr q.input.1) ▸ r)⟩
  onQuery := fun t => ⟨ChallengeIdx.inr t.1, ()⟩
  onResponse := fun t r => (range_challenge_append_inr t.1) ▸ r

/--
States that running an appended prover `P₁.append P₂` with an initial statement `stmt₁` and
witness `wit₁` behaves as expected: it first runs `P₁` to obtain an intermediate statement
`stmt₂`, witness `wit₂`, and transcript `transcript₁`. Then, it runs `P₂` on `stmt₂` and `wit₂`
to produce the final statement `stmt₃`, witness `wit₃`, and transcript `transcript₂`.
The overall output is `stmt₃`, `wit₃`, and the combined transcript `transcript₁ ++ₜ transcript₂`.
-/
theorem append_run (stmt : Stmt₁) (wit : Wit₁) :
      (P₁.append P₂).run stmt wit = (do
        let ⟨transcript₁, stmt₂, wit₂⟩ ← liftM (P₁.run stmt wit)
        let ⟨transcript₂, stmt₃, wit₃⟩ ← liftM (P₂.run stmt₂ wit₂)
        return ⟨transcript₁ ++ₜ transcript₂, stmt₃, wit₃⟩) := by
  unfold run runToRound
  sorry

-- TODO: Need to define a function that "extracts" a second prover from the combined prover

end Prover

namespace Verifier

variable {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁} {V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂}
  {stmt : Stmt₁}

/-- Running the sequential composition of two verifiers on a transcript of the combined protocol
  is equivalent to running the first verifier on the first part of the transcript, and the second
  verifier on the second part of the transcript, and returning the final statement. -/
theorem append_run (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
      (V₁.append V₂).run stmt tr =
        (do
          let stmt₂ ← V₁.run stmt tr.fst
          let stmt₃ ← V₂.run stmt₂ tr.snd
          return stmt₃) := rfl

end Verifier

namespace Reduction

variable {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

/- Unfortunately this is not true due to sequencing: `(R₁.append R₂).run` runs the two provers
first, then the two verifiers, whereas `R₁.run` and then `R₂.run` runs the first prover and
verifier, then the second prover and verifier.

We need justification to be able to swap the first verifier with the second prover, which would be
true if we interpret / maps this oracle computation (a priori a term of the free monad) into a
commutative monad (such as `Id`, i.e. all oracle queries are answered deterministically, `PMF`, i.e.
all oracle queries are answered probabilistically, `Option`, `ReaderT ρ`, `Set`, `WriterT` into a
commutative monoid, etc.). -/

-- TODO: prove this after VCVio refactor
-- theorem append_run_interp {m : Type → Type} [Monad m] [m.IsCommutative]
--     {interp : OracleImpl oSpec m} : ((R₁.append R₂).run stmt wit).runM interp =
--         (do
--           let ⟨ctx₁, stmt₂, transcript₁⟩ ← liftM (R₁.run stmt wit)
--           let ⟨ctx₂, stmt₃, transcript₂⟩ ← liftM (R₂.run stmt₂ ctx₁.2)
--           return ⟨ctx₂, stmt₃, transcript₁ ++ₜ transcript₂⟩).runM interp := by
--   unfold run append
--   simp [Prover.append_run, Verifier.append_run]
--   placeholder

end Reduction

end Execution

section Security

open scoped NNReal

section Protocol

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}

/-
TODO: when do these theorems hold? The answer may be that when oracle queries are answered according
to a _commutative_ monad, which are then interpreted into a probability distribution.

Unfortunately, this means that `StateT` is out; this works for `ReaderT` and `WriterT` into a
commutative monoid. If we still want composition to work for `StateT`, then we need to have extra
conditions (what are they?)
-/

namespace Reduction

/-- Sequential composition preserves completeness

  Namely, two reductions satisfy completeness with compatible relations (`rel₁`, `rel₂` for `R₁` and
  `rel₂`, `rel₃` for `R₂`), and respective completeness errors `completenessError₁` and
  `completenessError₂`, then their sequential composition `R₁.append R₂` also satisfies
  completeness with respect to `rel₁` and `rel₃`.

  The completeness error of the appended reduction is the sum of the individual errors
  (`completenessError₁ + completenessError₂`). -/
theorem append_completeness
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := by
  unfold completeness at h₁ h₂ ⊢
  intro stmtIn witIn hRelIn
  have h₁' := h₁ stmtIn witIn hRelIn
  clear h₁
  unfold Reduction.append Reduction.run
  simp [Prover.append_run, Verifier.append_run]
  sorry

/-- If two reductions satisfy perfect completeness with compatible relations, then their
  concatenation also satisfies perfect completeness. -/
theorem append_perfectCompleteness (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  dsimp [perfectCompleteness] at h₁ h₂ ⊢
  convert Reduction.append_completeness R₁ R₂ h₁ h₂
  simp only [add_zero]

variable {R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
  {R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

-- Synthesization issues...
-- So maybe no synthesization but simp is fine? Maybe not...
-- instance [R₁.IsComplete rel₁ rel₂] [R₂.IsComplete rel₂ rel₃] :
--     (R₁.append R₂).IsComplete rel₁ rel₃ := by placeholder

end Reduction

namespace Verifier

/-- If two verifiers satisfy soundness with compatible languages and respective soundness errors,
    then their sequential composition also satisfies soundness.
    The soundness error of the appended verifier is the sum of the individual errors. -/
theorem append_soundness {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  sorry

/-- If two verifiers satisfy knowledge soundness with compatible relations and respective knowledge
    errors, then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the appended verifier is the sum of the individual errors. -/
theorem append_knowledgeSoundness
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl
        rel₁ rel₃ (knowledgeError₁ + knowledgeError₂) := by
  sorry

/-- If two verifiers satisfy round-by-round soundness with compatible languages and respective RBR
    soundness errors, then their sequential composition also satisfies round-by-round soundness.
    The RBR soundness error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrSoundness {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  sorry

/-- If two verifiers satisfy round-by-round knowledge soundness with compatible relations and
    respective RBR knowledge errors, then their sequential composition also satisfies
    round-by-round knowledge soundness.
    The RBR knowledge error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrKnowledgeSoundness
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  sorry

end Verifier

end Protocol

section OracleProtocol

variable {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type} [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type} [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type} [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
    {Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [Oₘ₁ : ∀ i, OracleInterface ((pSpec₁.Message i))]
    [Oₘ₂ : ∀ i, OracleInterface ((pSpec₂.Message i))]
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set ((Stmt₁ × ∀ i, OStmt₁ i) × Wit₁)}
    {rel₂ : Set ((Stmt₂ × ∀ i, OStmt₂ i) × Wit₂)}
    {rel₃ : Set ((Stmt₃ × ∀ i, OStmt₃ i) × Wit₃)}

namespace OracleReduction

/-- Sequential composition preserves completeness

  Namely, two oracle reductions satisfy completeness with compatible relations (`rel₁`, `rel₂` for
  `R₁` and `rel₂`, `rel₃` for `R₂`), and respective completeness errors `completenessError₁` and
  `completenessError₂`, then their sequential composition `R₁.append R₂` also satisfies completeness
  with respect to `rel₁` and `rel₃`.

  The completeness error of the appended reduction is the sum of the individual errors
  (`completenessError₁ + completenessError₂`). -/
theorem append_completeness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := by
  unfold completeness
  convert Reduction.append_completeness R₁.toReduction R₂.toReduction h₁ h₂
  simp only [append_toReduction]

/-- If two oracle reductions satisfy perfect completeness with compatible relations, then their
  sequential composition also satisfies perfect completeness. -/
theorem append_perfectCompleteness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  unfold perfectCompleteness Reduction.perfectCompleteness
  convert OracleReduction.append_completeness R₁ R₂ h₁ h₂
  simp

end OracleReduction

namespace OracleVerifier

variable {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))} {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
    {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

/-- If two oracle verifiers satisfy soundness with compatible languages and respective soundness
    errors, then their sequential composition also satisfies soundness.
    The soundness error of the appended verifier is the sum of the individual errors. -/
theorem append_soundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  unfold soundness
  convert Verifier.append_soundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy knowledge soundness with compatible relations and respective
    knowledge errors, then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the appended verifier is the sum of the individual errors. -/
theorem append_knowledgeSoundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl rel₁ rel₃
        (knowledgeError₁ + knowledgeError₂) := by
  unfold knowledgeSoundness
  convert Verifier.append_knowledgeSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy round-by-round soundness with compatible languages and
  respective RBR soundness errors, then their sequential composition also satisfies
  round-by-round soundness. The RBR soundness error of the appended verifier extends the
  individual errors appropriately. -/
theorem append_rbrSoundness (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrSoundnessError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrSoundnessError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrSoundness init impl lang₁ lang₂ rbrSoundnessError₁)
    (h₂ : V₂.rbrSoundness init impl lang₂ lang₃ rbrSoundnessError₂) :
      (V₁.append V₂).rbrSoundness init impl lang₁ lang₃
        (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold rbrSoundness
  convert Verifier.append_rbrSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

/-- If two oracle verifiers satisfy round-by-round knowledge soundness with compatible relations
    and respective RBR knowledge errors, then their sequential composition also satisfies
    round-by-round knowledge soundness.
    The RBR knowledge error of the appended verifier extends the individual errors appropriately. -/
theorem append_rbrKnowledgeSoundness (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {rbrKnowledgeError₁ : pSpec₁.ChallengeIdx → ℝ≥0}
    {rbrKnowledgeError₂ : pSpec₂.ChallengeIdx → ℝ≥0}
    (h₁ : V₁.rbrKnowledgeSoundness init impl rel₁ rel₂ rbrKnowledgeError₁)
    (h₂ : V₂.rbrKnowledgeSoundness init impl rel₂ rel₃ rbrKnowledgeError₂) :
      (V₁.append V₂).rbrKnowledgeSoundness init impl rel₁ rel₃
        (Sum.elim rbrKnowledgeError₁ rbrKnowledgeError₂ ∘ ChallengeIdx.sumEquiv.symm) := by
  unfold rbrKnowledgeSoundness
  convert Verifier.append_rbrKnowledgeSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

end OracleVerifier

end OracleProtocol

end Security
