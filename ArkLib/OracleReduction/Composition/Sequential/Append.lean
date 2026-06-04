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

namespace OracleVerifier.Append

/-! ### Oracle-query routing infrastructure for `OracleVerifier.append`

The composite oracle verifier runs `V₁` then `V₂`, but each `Vᵢ` queries its own oracle context
`oSpec + ([OStmtᵢ]ₒ + [pSpecᵢ.Message]ₒ)`, whereas the composite verifier lives in
`oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)`. The two `QueryImpl` routers below re-route
each verifier's queries into that composite context (cf. the `routeOSpec/routeMsg/...` routers in
`LiftContext/OracleReduction.lean` and the `castMessageImpl` router in `Cast.lean`).

The `pSpec₁`/`pSpec₂` message oracles are carried into the appended message oracle at
`MessageIdx.inl`/`MessageIdx.inr`; the transport across the message-type equality is justified by
the heterogeneous agreement of the appended-message `OracleInterface` instance with `Oₘ₁`/`Oₘ₂`
(`instAppend_inl_heq`/`instAppend_inr_heq`). -/

/-- The appended message type at `MessageIdx.inl k` is `pSpec₁`'s message type at `k`. -/
theorem Message_inl (k : pSpec₁.MessageIdx) :
    (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inl k) = pSpec₁.Message k := by
  unfold ProtocolSpec.Message MessageIdx.inl
  simp [Fin.vappend_eq_append, Fin.append_left]

/-- The appended message type at `MessageIdx.inr k` is `pSpec₂`'s message type at `k`. -/
theorem Message_inr (k : pSpec₂.MessageIdx) :
    (pSpec₁ ++ₚ pSpec₂).Message (MessageIdx.inr k) = pSpec₂.Message k := by
  unfold ProtocolSpec.Message MessageIdx.inr
  simp [Fin.vappend_eq_append, Fin.append_right]

/-- The appended-message `OracleInterface` instance at `MessageIdx.inl k` agrees, heterogeneously,
with `Oₘ₁ k`. -/
theorem instAppend_inl_heq (k : pSpec₁.MessageIdx) :
    HEq (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
            (MessageIdx.inl k)) (Oₘ₁ k) := by
  obtain ⟨⟨k, hk⟩, hdir⟩ := k
  show HEq (instOracleInterfaceMessageAppend (MessageIdx.inl ⟨⟨k, hk⟩, hdir⟩)) _
  unfold instOracleInterfaceMessageAppend MessageIdx.inl
  simp only []
  rw [Fin.fappend₂_left]
  refine dcongr_heq (f₂ := fun h => Oₘ₁ (⟨⟨k, hk⟩, h⟩ : pSpec₁.MessageIdx))
    (proof_irrel_heq _ hdir) (fun t₁ t₂ _ => ?_) (fun _ _ => cast_heq _ _)
  congr 1
  show (pSpec₁.Type ++ᵛ pSpec₂.Type) (Fin.castAdd n ⟨k, hk⟩) = pSpec₁.Type ⟨k, hk⟩
  rw [Fin.vappend_left]

/-- The appended-message `OracleInterface` instance at `MessageIdx.inr k` agrees, heterogeneously,
with `Oₘ₂ k`. -/
theorem instAppend_inr_heq (k : pSpec₂.MessageIdx) :
    HEq (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
            (MessageIdx.inr k)) (Oₘ₂ k) := by
  obtain ⟨⟨k, hk⟩, hdir⟩ := k
  show HEq (instOracleInterfaceMessageAppend (MessageIdx.inr ⟨⟨k, hk⟩, hdir⟩)) _
  unfold instOracleInterfaceMessageAppend MessageIdx.inr
  simp only []
  rw [Fin.fappend₂_right]
  refine dcongr_heq (f₂ := fun h => Oₘ₂ (⟨⟨k, hk⟩, h⟩ : pSpec₂.MessageIdx))
    (proof_irrel_heq _ hdir) (fun t₁ t₂ _ => ?_) (fun _ _ => cast_heq _ _)
  congr 1
  show (pSpec₁.Type ++ᵛ pSpec₂.Type) (Fin.natAdd m ⟨k, hk⟩) = pSpec₂.Type ⟨k, hk⟩
  rw [Fin.vappend_right]

/-- `cast`-form of `instAppend_inl_heq`, matching the `hO` shape required by `emitMessageQuery`. -/
theorem instAppend_inl_cast (k : pSpec₁.MessageIdx) :
    (Oₘ₁ k) = _root_.cast (congrArg OracleInterface (Message_inl k))
      (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        (MessageIdx.inl k)) := by
  apply eq_of_heq
  refine HEq.trans (instAppend_inl_heq (pSpec₂ := pSpec₂) k).symm ?_
  exact (cast_heq _ _).symm

/-- `cast`-form of `instAppend_inr_heq`, matching the `hO` shape required by `emitMessageQuery`. -/
theorem instAppend_inr_cast (k : pSpec₂.MessageIdx) :
    (Oₘ₂ k) = _root_.cast (congrArg OracleInterface (Message_inr k))
      (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂)
        (MessageIdx.inr k)) := by
  apply eq_of_heq
  refine HEq.trans (instAppend_inr_heq (pSpec₁ := pSpec₁) k).symm ?_
  exact (cast_heq _ _).symm

/-- Per-query body emitting a query to the source message interface `O₁` (which agrees, up to the
message-type equality `hMsg`, with the appended-spec interface at the appended message index `j`)
into the appended-spec message oracle. Modelled on `OracleVerifier.castMessageQuery`. -/
private def emitMessageQuery
    {T₁ : Type} (O₁ : OracleInterface T₁)
    (j : (pSpec₁ ++ₚ pSpec₂).MessageIdx) (hMsg : (pSpec₁ ++ₚ pSpec₂).Message j = T₁)
    (hO : O₁ = _root_.cast (congrArg OracleInterface hMsg)
      (instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂) j))
    (q : O₁.Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (O₁.Response q) := by
  subst hMsg
  subst hO
  exact query (spec := oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ))
    (Sum.inr (Sum.inr ⟨j, q⟩))

/-- Emit a `pSpec₁`-message query into the appended message oracle at `MessageIdx.inl`. -/
private def emitMessageInl (i : pSpec₁.MessageIdx) (q : (Oₘ₁ i).Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) ((Oₘ₁ i).Response q) :=
  emitMessageQuery (oSpec := oSpec) (OStmt₁ := OStmt₁)
    (Oₘ₁ i) (MessageIdx.inl i) (Message_inl i) (instAppend_inl_cast (pSpec₂ := pSpec₂) i) q

/-- Emit a `pSpec₂`-message query into the appended message oracle at `MessageIdx.inr`. -/
private def emitMessageInr (i : pSpec₂.MessageIdx) (q : (Oₘ₂ i).Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) ((Oₘ₂ i).Response q) :=
  emitMessageQuery (oSpec := oSpec) (OStmt₁ := OStmt₁)
    (Oₘ₂ i) (MessageIdx.inr i) (Message_inr i) (instAppend_inr_cast (pSpec₁ := pSpec₁) i) q

/-- Router carrying `V₁`'s oracle context into the appended-spec oracle context: `oSpec` and the
input oracle statements `[OStmt₁]ₒ` pass through unchanged; `pSpec₁`-message queries are emitted at
`MessageIdx.inl`. -/
def router₁ : QueryImpl (oSpec + ([OStmt₁]ₒ + [pSpec₁.Message]ₒ))
    (OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ))) :=
  fun q => match q with
    | Sum.inl t =>
        query (spec := oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (Sum.inl t)
    | Sum.inr (Sum.inl t) =>
        query (spec := oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (Sum.inr (Sum.inl t))
    | Sum.inr (Sum.inr ⟨i, q⟩) => emitMessageInl (pSpec₂ := pSpec₂) i q

/-- Emit a query to `V₁`'s output oracle statement `OStmt₂ i`.

FRONTIER (instance-coherence gap): if `V₁.embed i = .inl k`, V₁'s output oracle for `OStmt₂ i` is
`OStmt₁ k` (answered via `Oₛ₁ k`); if `.inr k`, it is the appended `pSpec₁`-message at
`MessageIdx.inl k` (answered via `Oₘ₁ k`). Routing the query `q : (Oₛ₂ i).Query` to that oracle
requires `Oₛ₂ i ≍ Oₛ₁ k` (resp. `Oₘ₁ k`), which is *not* derivable from `V₁.hEq i` (a bare type
equality `OStmt₂ i = OStmt₁ k`): the output-oracle-statement interfaces are free parameters of
`OracleVerifier` (cf. the commented-out `Oₛₒ` field in `OracleReduction/Basic.lean`). This is the
same kind of side condition resolved by `OracleVerifier.LiftContextCoherent` for `liftContext`;
closing it needs an added instance-coherence hypothesis on `OracleVerifier.append`. -/
def emitOStmt₂Query (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (i : ιₛ₂) (q : (Oₛ₂ i).Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) ((Oₛ₂ i).Response q) :=
  sorry

/-- Router carrying `V₂`'s oracle context into the appended-spec oracle context: `oSpec` passes
through; `OStmt₂`-queries are answered via `V₁`'s output oracle statements (`emitOStmt₂Query`);
`pSpec₂`-message queries are emitted at `MessageIdx.inr`. -/
def router₂ (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁) :
    QueryImpl (oSpec + ([OStmt₂]ₒ + [pSpec₂.Message]ₒ))
      (OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ))) :=
  fun q => match q with
    | Sum.inl t =>
        query (spec := oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (Sum.inl t)
    | Sum.inr (Sum.inl ⟨i, q⟩) => emitOStmt₂Query V₁ i q
    | Sum.inr (Sum.inr ⟨i, q⟩) => emitMessageInr (pSpec₁ := pSpec₁) i q

/-- The composite `verify`: run `V₁` (routed by `router₁`) to obtain the intermediate statement,
then run `V₂` (routed by `router₂ V₁`) to obtain the final statement, all inside the appended-spec
oracle context. -/
def verify
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (stmt : Stmt₁) (challenges : (pSpec₁ ++ₚ pSpec₂).Challenges) :
    OptionT (OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ))) Stmt₃ := do
  let stmt₂ ← simulateQ router₁ (V₁.verify stmt (fun chal =>
    by simpa [ChallengeIdx.inl, ProtocolSpec.append] using challenges (ChallengeIdx.inl chal)))
  simulateQ (router₂ V₁) (V₂.verify stmt₂ (fun chal =>
    by simpa [ChallengeIdx.inr, ProtocolSpec.append] using challenges (ChallengeIdx.inr chal)))

end OracleVerifier.Append

open Function Embedding in
def OracleVerifier.append (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := fun _ _ => OptionT.mk (pure none)

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

/-- Sequential composition of oracle reductions is just the sequential composition of the oracle
  provers and oracle verifiers. -/
def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

end OracleProtocol

/-! Sequential composition of extractors and state functions

These have the following form: they needs to know the first verifier, and derive the intermediate
statement from running the first verifier on the first statement.

This leads to complications: the verifier is assumed to be a general `OracleComp oSpec`, and so
we also need to have the extractors and state functions to be similarly `OracleComp`s.

The alternative is to consider a fully deterministic (and non-failing) verifier. The non-failing
part is somewhat problematic as we write our verifiers to be able to fail (i.e. implicit failing
via `guard` statements).

As such, the definitions below isolate the extractor composition interface. -/

namespace Extractor

/-- The sequential composition of two straightline extractors.

Note: state a monotone condition on the extractor, namely that if extraction succeeds on a given
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

/-- The round-by-round extractor for the sequential composition of two (oracle) reductions.

STATEMENT REPAIR (2026-06-04): added a deterministic intermediate-statement function
`verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂` (mirroring `StateFunction.append`). The second
extractor `E₂` operates on the *intermediate* statement `Stmt₂`, which a round-by-round extractor
over the composed protocol must reconstruct from `Stmt₁` and the phase-1 transcript; the appended
extractor has no other way to obtain it. (No downstream consumer references this def yet, so the
signature is free.)

Construction (the extractor processes rounds in *decreasing* order `n+m → … → 0`):
- rounds `idx < m` (entirely in phase 1): defer to `E₁.extractMid`;
- the crossing round `idx = m` (`WitMid₂ 1 → WitMid₁ (last m)`): peel one phase-2 round with
  `E₂.extractMid 0` to land in `WitMid₂ 0 = Wit₂` (via `E₂.eqIn`), then cross into phase 1 with
  `E₁.extractOut` on the intermediate statement `verify stmt₁ tr.fst`;
- rounds `idx > m` (entirely in phase 2): defer to `E₂.extractMid (idx - m)` on `verify stmt₁ tr.fst`;
- `extractOut` (final witness → `WitMid (last)`): for `n > 0` defer to `E₂.extractOut`; for `n = 0`
  the protocol is all phase 1, so cross immediately with `E₁.extractOut` after the trivial
  `E₂.extractOut`/`eqIn` round-trip at the empty phase 2. -/
def RoundByRound.append
    {WitMid₁ : Fin (m + 1) → Type} {WitMid₂ : Fin (n + 1) → Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂) :
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
    · -- `idx ≥ m`.  The combined `WitMid` lands in the `WitMid₂` (phase-2) leg.
      have hmle : m ≤ (idx : ℕ) := by omega
      -- output type `WitMid_combined idx.castSucc`: `WitMid₁ m` if `idx = m`, else `WitMid₂ (idx-m)`
      by_cases hidx : (idx : ℕ) = m
      · -- crossing `idx = m`: input `WitMid₂ 1`, output `WitMid₁ (last m)`.
        -- the combined input witness `h` reduces to `WitMid₂ 1` (its index `idx+1 ≥ m+1`)
        have h1 : WitMid₂ (⟨0, by omega⟩ : Fin n).succ := by
          have : (⟨(idx : ℕ) + 1 - (m + 1) + 1, by omega⟩ : Fin (n + 1))
              = (⟨0, by omega⟩ : Fin n).succ := by ext; simp only [Fin.val_succ]; omega
          rw [← this]
          simpa [show ¬ (idx : ℕ) + 1 < m + 1 from by omega] using h
        -- peel one phase-2 round to `WitMid₂ 0`, then cross via `E₁.extractOut`
        have hwit₂ : WitMid₂ (⟨0, by omega⟩ : Fin n).castSucc :=
          E₂.extractMid ⟨0, by omega⟩
            (verify stmt₁ (by simpa [show min ((idx : ℕ) + 1) m = m from by omega] using tr.fst))
            (by simpa [hidx] using tr.snd) h1
        have hcs0eq : WitMid₂ (⟨0, by omega⟩ : Fin n).castSucc = Wit₂ := by
          rw [show (⟨0, by omega⟩ : Fin n).castSucc = (0 : Fin (n + 1)) from by ext; simp]
          exact E₂.eqIn
        have hwit₂' : Wit₂ := cast hcs0eq hwit₂
        have hout : WitMid₁ (Fin.last m) :=
          E₁.extractOut stmt₁
            (by simpa [show min ((idx : ℕ) + 1) m = m from by omega] using tr.fst) hwit₂'
        -- the output slot is `WitMid₁ m` (`idx < m+1` since `idx = m`)
        rw [dif_pos (show (idx : ℕ) < m + 1 from by omega)]
        exact cast (congrArg WitMid₁ (Fin.ext (by
          first | omega | (simp only [Fin.val_last]; omega)))) hout
      · -- `idx > m`: entirely in phase 2; defer to `E₂.extractMid (idx - m)`.
        have hmlt : m < (idx : ℕ) := by omega
        -- input `h : WitMid₂ ((idx-m)+1)`, output `WitMid₂ (idx-m)`
        have hin : WitMid₂ (⟨(idx : ℕ) - m, by omega⟩ : Fin n).succ := by
          have : (⟨(idx : ℕ) + 1 - (m + 1) + 1, by omega⟩ : Fin (n + 1))
              = (⟨(idx : ℕ) - m, by omega⟩ : Fin n).succ := by
            ext; simp only [Fin.val_succ]; omega
          rw [← this]
          simpa [show ¬ (idx : ℕ) + 1 < m + 1 from by omega] using h
        have hout : WitMid₂ (⟨(idx : ℕ) - m, by omega⟩ : Fin n).castSucc :=
          E₂.extractMid ⟨(idx : ℕ) - m, by omega⟩
            (verify stmt₁ (by simpa [show min ((idx : ℕ) + 1) m = m from by omega] using tr.fst))
            (by simpa [show (idx : ℕ) - m + 1 = (idx : ℕ).succ - m from by omega] using tr.snd) hin
        -- output slot is the phase-2 leg `WitMid₂ (idx - m)` (`¬ idx < m+1`)
        rw [dif_neg (show ¬ (idx : ℕ) < m + 1 from by omega)]
        refine cast ?_ hout
        simp only [eqRec_eq_cast, cast_cast]
        exact congrArg WitMid₂ (Fin.ext (by simp only [Fin.val_castSucc]; omega))
  extractOut := fun stmt₁ tr wit₃ => by
    dsimp [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
    by_cases hn : n = 0
    · -- empty phase 2: `WitMid_combined (last) = WitMid₁ (last m)`; cross via `E₁.extractOut`.
      subst hn
      -- round-trip `wit₃` through the (trivial) `E₂` and into phase 1
      have hwit₂ : Wit₂ := cast E₂.eqIn (E₂.extractOut (verify stmt₁ tr.fst) tr.snd wit₃)
      have hout : WitMid₁ (Fin.last m) := E₁.extractOut stmt₁ tr.fst hwit₂
      rw [dif_pos (show m + 0 < m + 1 from by omega)]
      exact cast (congrArg WitMid₁ (Fin.ext (by
        first | omega | (simp only [Fin.val_last]; omega)))) hout
    · -- `n > 0`: `WitMid_combined (last) = WitMid₂ (last n)`; defer to `E₂.extractOut`.
      have hout : WitMid₂ (Fin.last n) := E₂.extractOut (verify stmt₁ tr.fst) tr.snd wit₃
      rw [dif_neg (show ¬ m + n < m + 1 from by omega)]
      refine cast ?_ hout
      simp only [eqRec_eq_cast, cast_cast]
      exact congrArg WitMid₂ (Fin.ext (by simp only [Fin.val_succ, Fin.val_last]; omega))

end Extractor

namespace Verifier

variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

/-- **Doomed-ness crosses the language.** For a *deterministic* first verifier `V₁ = pure ∘ verify`
with a reachable initial state (`∃ s, s ∈ support init`), if its state function `S₁` is false on a
full transcript, then the intermediate statement `verify stmt tr` lies *outside* `lang₂`.

This is the bridge that makes the un-conjoined composite state function work: it converts the
probabilistic `S₁.toFun_full` (`Pr[… ∈ lang₂ | …] = 0`) into the pointwise membership fact needed to
fire `S₂.toFun_empty` at the phase crossing. -/
private theorem StateFunction.verify_not_mem_lang_of_toFun_full_neg
    {V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁}
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init)
    (stmt : Stmt₁) (tr : pSpec₁.FullTranscript)
    (hNeg : ¬ S₁ (Fin.last m) stmt tr) :
    verify stmt tr ∉ lang₂ := by
  have hPr := S₁.toFun_full stmt tr hNeg
  rw [probEvent_eq_zero_iff] at hPr
  -- `V₁.run stmt tr = pure (verify stmt tr)`, so `verify stmt tr` is a reachable output; the
  -- `Pr = 0` hypothesis then forbids it from lying in `lang₂`.
  obtain ⟨s, hs⟩ := hInit
  refine hPr (verify stmt tr) ?_
  rw [OptionT.mem_support_iff]
  simp only [OptionT.run_mk, support_bind, Set.mem_iUnion]
  refine ⟨s, hs, ?_⟩
  have hrun : (V₁.run stmt tr) = (pure (verify stmt tr) : OptionT (OracleComp oSpec) Stmt₂) := by
    subst hVerify; rfl
  rw [hrun]
  change some (verify stmt tr) ∈ _root_.support
    (StateT.run' (simulateQ impl (pure (some (verify stmt tr)) :
      OracleComp oSpec (Option Stmt₂))) s)
  rw [simulateQ_pure]
  change some (verify stmt tr) ∈ _root_.support
    (Prod.fst <$> (pure (some (verify stmt tr)) : StateT σ ProbComp _).run s)
  rw [StateT.run_pure]
  simp [map_pure]

/-- The sequential composition of two state functions.

STATEMENT REPAIR (2026-06-04): the composite `toFun` now uses the standard "doomed" semantics —
for rounds `> m` it is the *un-conjoined* second state function `S₂ (k-m)` on the phase-2 prefix
(applied to `verify stmt₁ tr.fst`), NOT `S₁(last) ∧ S₂(k-m)`. The prior conjunction-based form made
`toFun_full` FALSE: in the `S₁`-false / `S₂`-true case, `S₂(last)` may legitimately hold on an
out-of-language input via a lucky challenge (rbr soundness bounds this only probabilistically), so
the demanded `Pr = 0` was unobtainable. With the un-conjoined form the doomed-ness propagates
*through the language*: `¬ S₁(last) ⇒` (by `S₁.toFun_full`, the verifier being deterministic)
`verify … ∉ lang₂ ⇒` (by `S₂.toFun_empty`) `¬ S₂ 0`, which `S₂.toFun_next` then carries forward —
so the crossing `toFun_next` at `k = m` holds and `toFun_full` reduces to `S₂.toFun_full`.

STATEMENT REPAIR (2026-06-04): added `hInit : ∃ s, s ∈ support init`. The crossing inversion of
`S₁.toFun_full` (a statement about `Pr[… | … (← init)] = 0`) into the pointwise fact
`verify stmt₁ tr.fst ∉ lang₂` requires at least one reachable initial state `s ∈ support init`;
otherwise the support is empty and the `Pr = 0` hypothesis is vacuous. This is a mild, standard
non-failing-setup assumption (every concrete `init` used downstream samples successfully). -/
def StateFunction.append
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂)
    (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    -- Assume the first verifier is deterministic for now
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) :
      (V₁.append V₂).StateFunction init impl lang₁ lang₃ where
  toFun := fun roundIdx stmt₁ transcript =>
    if h : roundIdx.val ≤ m then
    -- If the round index falls in the first protocol, then we simply invokes the first state fn
      S₁ ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst)
    else
    -- If the round index falls in the second protocol, then we return the second state fn on the
    -- remaining transcript, applied to the intermediate statement `verify stmt₁ tr.fst`. We do
    -- NOT conjoin `S₁(last)`: doomed-ness is carried by `verify … ∉ lang₂` through the language
    -- (see the statement-repair note above), which is exactly what makes `toFun_full` true.
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
      simp only [Fin.val_succ, Fin.val_castSucc] at *
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
          simp only [Fin.val_succ] at hav hav_lt ⊢
          rw [show min ((roundIdx : ℕ) + 1) m = (roundIdx : ℕ) + 1 from by omega] at hav_lt
          have ha'_lt : (a' : ℕ) < (roundIdx : ℕ) + 1 := by
            have := a'.isLt; simpa [Fin.val_succ] using this
          simp only [Fin.snoc]
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
            have hFstHeq : (by simpa [hcs] using tr.fst :
                  pSpec₁.Transcript ⟨roundIdx, Nat.lt_succ_of_lt hlt⟩)
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
      rw [not_lt] at hlt
      have hnsucc : ¬ ((roundIdx : ℕ) + 1 ≤ m) := by omega
      simp only [Fin.val_succ, Fin.val_castSucc] at *
      rw [dif_neg hnsucc] at *
      -- the first-segment part of the transcript is unchanged by concatenating a 2nd-segment round
      -- the first-segment fst is unchanged by concatenating a 2nd-segment round (HEq form)
      have hfstHeq : (Transcript.concat msg tr).fst ≍ tr.fst := by
        have hmr : m ≤ (roundIdx : ℕ) := hlt
        have hcard : min ((roundIdx : Fin (m + n)).succ : ℕ) m
            = min ((roundIdx : Fin (m + n)).castSucc : ℕ) m := by
          simp only [Fin.val_succ, Fin.val_castSucc]; omega
        -- (concat msg tr).fst ≍ tr.fst   (over their min-indexed domains)
        apply Function.hfunext
        · congr 1
        · intro a a' haa'
          have hav : (a : ℕ) = (a' : ℕ) := by
            have := Fin.heq_ext_iff hcard |>.mp haa'
            omega
          simp only [Transcript.concat, Transcript.fst]
          obtain ⟨av, hav_lt⟩ := a
          simp only [Fin.val_succ] at hav hav_lt ⊢
          rw [show min ((roundIdx : ℕ) + 1) m = m from by omega] at hav_lt
          refine HEq.trans (cast_heq _ _) ?_
          refine HEq.trans ?_ (cast_heq _ _).symm
          -- Fin.snoc tr msg ⟨av,_⟩ ≍ tr ⟨av,_⟩  since av < m ≤ roundIdx
          simp only [Fin.snoc]
          rw [dif_pos (show av < roundIdx from by omega)]
          refine HEq.trans (cast_heq _ _) ?_
          congr 1
          ext; simp only [Fin.val_castLT]; omega
      -- The succ-round (`> m`) goal is the second state function on the phase-2 prefix. We will show
      -- `¬ S₂ ((roundIdx - m).succ) (verify stmt₁ tr.fst) (tr.snd.concat msg₂)` (the "clean" form,
      -- where `msg₂` is `msg` transported into the second segment's type), then transport it to the
      -- actual goal via the unchanged first-segment `fst` and the snoc'd `snd`.
      intro hS2
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
      -- The phase-1 prefix as a genuine full transcript (its domain is all `m` rounds since
      -- `roundIdx ≥ m`). All the `verify stmt₁ …` arguments below are this same transcript.
      have hmin : min (roundIdx : ℕ) m = m := by omega
      let trFst : pSpec₁.FullTranscript :=
        (by simpa [hmin] using tr.fst : pSpec₁.FullTranscript)
      have htrFst_heq : (trFst : pSpec₁.FullTranscript) ≍ tr.fst := cast_heq _ _
      -- The "clean" second-segment falsity: `¬ S₂ ((roundIdx - m).succ) (verify … trFst) (tr.snd ∘ msg₂)`.
      -- Two sources, depending on whether this is the phase crossing (`roundIdx = m`) or strictly
      -- inside the second phase (`roundIdx > m`).
      have hClean : ¬ S₂ (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).succ
          (verify stmt₁ trFst) (Transcript.concat (cast hmsgty₂ msg) tr.snd) := by
        by_cases hrm : (roundIdx : ℕ) ≤ m
        · -- phase crossing `roundIdx = m`: `hPrev` is `¬ S₁ (last)`; push doomed-ness through lang₂.
          rw [dif_pos hrm] at hPrev
          have hrm' : (roundIdx : ℕ) = m := by omega
          have hn1 : 0 < n := by
            -- the succ round `roundIdx + 1` lies in `Fin (m + n)`, and `roundIdx + 1 > m`
            have := (roundIdx : Fin (m + n)).isLt; omega
          -- `¬ S₁ (last m) stmt₁ trFst`  (re-index `hPrev`'s `⟨roundIdx, _⟩` as `Fin.last m`)
          have hS1neg : ¬ S₁ (Fin.last m) stmt₁ trFst := by
            intro hc; apply hPrev
            convert hc using 2 <;>
              first
                | (ext; simp only [Fin.val_castSucc, Fin.val_last]; omega)
                | exact HEq.trans (cast_heq _ _) htrFst_heq.symm
          -- `verify stmt₁ trFst ∉ lang₂`
          have hNotMem := StateFunction.verify_not_mem_lang_of_toFun_full_neg
            init impl S₁ verify hVerify hInit _ _ hS1neg
          -- hence `¬ S₂ 0 (verify …) default`
          have hS20 : ¬ S₂ (0 : Fin (n + 1)) (verify stmt₁ trFst) default :=
            fun hc => hNotMem ((S₂.toFun_empty _).mpr hc)
          -- The message transported into `pSpec₂.Type ⟨0, _⟩` (the first phase-2 round's type).
          have hmsgty0 : (pSpec₁ ++ₚ pSpec₂).Type roundIdx
              = pSpec₂.Type (⟨0, hn1⟩ : Fin n) := by
            rw [hmsgty₂]; congr 1; ext; simp only [Fin.val_mk]; omega
          -- the empty phase-2 prefix at round `⟨0,_⟩.castSucc` (its domain is `Fin 0`)
          have hcs0 : (⟨0, hn1⟩ : Fin n).castSucc = (0 : Fin (n + 1)) := by ext; simp
          let empty2 : pSpec₂.Transcript (⟨0, hn1⟩ : Fin n).castSucc := fun i => i.elim0
          -- `S₂.toFun_next` at round `⟨0, _⟩` turns `¬ S₂ 0` into `¬ S₂ 1` after concatenating `msg₂`.
          have hcross : ¬ S₂ (⟨0, hn1⟩ : Fin n).succ (verify stmt₁ trFst)
              (Transcript.concat (cast hmsgty0 msg) empty2) := by
            refine S₂.toFun_next (⟨0, hn1⟩ : Fin n) ?_ _ empty2 ?_ (cast hmsgty0 msg)
            · -- direction at round `0` (= direction at round `roundIdx - m`)
              have : (⟨0, hn1⟩ : Fin n) = ⟨(roundIdx : ℕ) - m, by omega⟩ := by
                ext; simp only [Fin.val_mk]; omega
              rw [this]; exact hDir₂
            · -- `¬ S₂ (0.castSucc) empty2`, where `0.castSucc = (0 : Fin (n+1))` and `empty2 = default`
              intro hc; apply hS20
              convert hc using 2 <;>
                first
                  | exact hcs0.symm
                  | (apply Function.hfunext (by congr 1; exact hcs0); intro a _ _; exact a.elim0)
          -- Transport `hcross` to the `⟨roundIdx - m, _⟩.succ` index (numerically equal to `0.succ`).
          intro hgoal; apply hcross
          convert hgoal using 2 <;>
            first
              | (ext; simp only [Fin.val_succ]; omega)
              | exact HEq.trans (cast_heq _ _) (cast_heq _ _).symm
              | -- `empty2 ≍ tr.snd`  (both empty, domain `Fin 0`)
                (apply Function.hfunext ?_ ?_ <;>
                  first
                    | (congr 1; simp only [Fin.val_castSucc]; omega)
                    | (intro a a' _;
                       exact absurd a.isLt (by simp only [empty2, Fin.val_castSucc]; omega)))
        · -- strictly inside the second phase: `hPrev` is `¬ S₂ (roundIdx - m)`; one `toFun_next` step.
          rw [dif_neg hrm] at hPrev
          -- re-index `hPrev`'s `⟨roundIdx - m, _⟩` as the `castSucc` of `⟨roundIdx - m, _⟩ : Fin n`
          have hPrev' : ¬ S₂ (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).castSucc
              (verify stmt₁ trFst) tr.snd := by
            intro hc; apply hPrev
            -- `hPrev`'s verify-argument is `tr.fst` massaged; it agrees with `trFst`
            convert hc using 2 <;>
              first
                | (ext; simp only [Fin.val_castSucc]; omega)
                | exact HEq.trans (cast_heq _ _) htrFst_heq.symm
          exact S₂.toFun_next ⟨(roundIdx : ℕ) - m, by omega⟩ hDir₂ _ tr.snd hPrev' (cast hmsgty₂ msg)
      -- Transport `hClean` to the actual goal `hS2` (fst unchanged, snd gains the new message).
      -- Rewrite `hClean`'s `⟨roundIdx - m, _⟩.succ` index to the goal's `⟨roundIdx.succ - m, _⟩` form.
      have hsuccIdx : (⟨(roundIdx : ℕ) - m, by omega⟩ : Fin n).succ
          = ⟨((roundIdx : Fin (m + n)).succ : ℕ) - m, by simp only [Fin.val_succ]; omega⟩ := by
        ext; simp only [Fin.val_succ]; omega
      apply hClean
      convert hS2 using 2
      · -- index of the goal's S₂ matches `(roundIdx - m).succ`
        simp only [Fin.val_succ]; omega
      · -- `verify` on the unchanged `fst`: `trFst ≍ (concat msg tr).fst`
        congr 1
        exact eq_of_heq (HEq.trans htrFst_heq (HEq.trans hfstHeq.symm (cast_heq _ _).symm))
      · -- `tr.snd.concat msg₂ ≍ (concat msg tr).snd`
        have hsndcard : ((roundIdx : ℕ) - m) + 1 = ((roundIdx : Fin (m + n)).succ : ℕ) - m := by
          simp only [Fin.val_succ]; omega
        apply Function.hfunext
        · congr 1
        · intro a a' haa'
          have haa : (a : ℕ) = (a' : ℕ) := by
            have := Fin.heq_ext_iff hsndcard |>.mp haa'
            omega
          simp only [Transcript.concat]
          obtain ⟨av, hav_lt⟩ := a
          simp only [Fin.val_mk] at haa hav_lt ⊢
          -- the RHS `(concat msg tr).snd` always lands in the `else` branch (its index `> m`)
          rw [show (Transcript.concat msg tr).snd (⟨(a' : ℕ), a'.isLt⟩ : Fin _)
                = (Transcript.concat msg tr).snd a' from by congr]
          unfold Transcript.snd
          rw [dif_neg (show ¬ (roundIdx : Fin (m + n)).succ ≤ m from by
                simp only [Fin.val_succ]; omega)]
          -- the LHS `Fin.snoc (tr.snd) msg₂`: split on whether `av` is the last position
          simp only [Fin.snoc]
          by_cases hlast : av = (roundIdx : ℕ) - m
          · rw [dif_neg (show ¬ av < (roundIdx : ℕ) - m from by omega),
                dif_neg (show ¬ m + (a' : ℕ) < (roundIdx : ℕ) from by omega)]
            -- both sides are `msg` (the new message), up to casts
            refine HEq.trans (cast_heq _ _) ?_
            refine HEq.trans (cast_heq _ _) ?_
            exact HEq.trans (cast_heq _ _).symm (cast_heq _ _).symm
          · -- earlier position: both read the original `tr.snd` at the same underlying index
            have hlt2 : av < (roundIdx : ℕ) - m := by omega
            -- LHS: the inner `tr.snd` was already unfolded; its `if` is on `roundIdx.castSucc ≤ m`
            rw [dif_pos (show av < (roundIdx : ℕ) - m from hlt2)]
            rw [dif_neg (show ¬ (roundIdx : Fin (m + n)).castSucc ≤ m from by
                  simp only [Fin.val_castSucc]; omega)]
            rw [dif_pos (show m + (a' : ℕ) < (roundIdx : ℕ) from by omega)]
            refine HEq.trans (cast_heq _ _) ?_
            refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
            congr 1
            ext
            simp only [Fin.val_castLT]
            omega
  toFun_full := by
    -- `toFun (last)` on the appended protocol is `S₂ (last)` on the phase-2 transcript (since
    -- `m + n > m`, the `≤ m` branch never fires for the last round when `n > 0`; when `n = 0` the
    -- last round is `m`, the `≤ m` branch fires, and the goal reduces to `S₁.toFun_full`).
    intro stmt₁ tr hNeg
    -- For a *full* transcript `tr : Transcript (last (m+n))`, the partial-transcript `Transcript.fst`
    -- / `Transcript.snd` coincide (over `HEq`) with the full-transcript `FullTranscript.fst`/`.snd`.
    have hmincard : min ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) m = m := by
      simp only [Fin.val_last]; omega
    have hsndcard : ((Fin.last (m + n) : Fin (m + n + 1)) : ℕ) - m = n := by
      simp only [Fin.val_last]; omega
    have htFstHeq : ∀ (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript),
        (Transcript.fst (k := Fin.last (m + n)) T) ≍ FullTranscript.fst T := by
      intro T
      apply Function.hfunext (congrArg Fin hmincard)
      intro a a' ha
      have hval : (a : ℕ) = (a' : ℕ) := by
        have := Fin.heq_ext_iff hmincard |>.mp ha; omega
      simp only [Transcript.fst, FullTranscript.fst]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1; apply Fin.ext; simp only [Fin.coe_castAdd]; omega
    have htSndHeq : ∀ (T : (pSpec₁ ++ₚ pSpec₂).FullTranscript),
        (Transcript.snd (k := Fin.last (m + n)) T) ≍ FullTranscript.snd T := by
      intro T
      apply Function.hfunext (congrArg Fin hsndcard)
      intro a a' ha
      have hval : (a : ℕ) = (a' : ℕ) := by
        have := Fin.heq_ext_iff hsndcard |>.mp ha; omega
      simp only [Transcript.snd, FullTranscript.snd]
      rw [dif_neg (show ¬ (Fin.last (m + n)) ≤ m from by simp only [Fin.val_last]; omega)]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      congr 1; apply Fin.ext; simp only [Fin.coe_natAdd]; omega
    by_cases hn : n = 0
    · -- degenerate: empty second protocol. `toFun (last) = S₁ (last)`, and the appended verifier's
      -- output language is `lang₃`; since `n = 0`, `lang₂`-membership of `verify …` is `lang₃` via
      -- `S₂` being over the empty protocol. We reduce directly to `S₁.toFun_full` composed with the
      -- (trivial, `n = 0`) second verifier run.
      subst hn
      -- last round index is `m ≤ m`, so `toFun (last) = S₁ ⟨m,_⟩`
      rw [dif_pos (show ((Fin.last (m + 0)) : ℕ) ≤ m from by simp)] at hNeg
      -- `¬ S₁ (last m) stmt₁ (tr.fst as full)`, hence `verify stmt₁ tr.fst ∉ lang₂`
      set trFst : pSpec₁.FullTranscript := (FullTranscript.fst tr : pSpec₁.FullTranscript) with htrFst
      have hS1neg : ¬ S₁ (Fin.last m) stmt₁ trFst := by
        intro hc; apply hNeg
        convert hc using 2 <;>
          first
            | (ext; simp only [Fin.val_last]; omega)
            | (congr 1; exact eq_of_heq (HEq.trans (cast_heq _ _) (htFstHeq tr)))
      have hNotMem := StateFunction.verify_not_mem_lang_of_toFun_full_neg
        init impl S₁ verify hVerify hInit _ _ hS1neg
      -- with `n = 0`, the second protocol is empty: `last 0 = 0`, and `S₂.toFun_empty` ties
      -- `S₂ 0 (verify …) default` to `verify … ∈ lang₂`; doomed-ness gives `¬ S₂ (last 0)`.
      have hS2neg : ¬ S₂ (Fin.last 0) (verify stmt₁ trFst) (FullTranscript.snd tr) := by
        intro hc; apply hNotMem
        refine (S₂.toFun_empty _).mpr ?_
        convert hc using 2 <;>
          first
            | (apply Fin.ext; simp)
            | (funext i; exact i.elim0)
      have hPr := S₂.toFun_full (verify stmt₁ trFst) (FullTranscript.snd tr) hS2neg
      -- the appended run collapses to `V₂.run (verify …) tr.snd` (the deterministic `V₁` `pure`-binds)
      have hrun : (V₁.append V₂).run stmt₁ tr
          = V₂.run (verify stmt₁ trFst) (FullTranscript.snd tr) := by
        subst hVerify
        show (do return ← V₂.verify (← (pure (verify stmt₁ trFst))) (FullTranscript.snd tr)) = _
        rw [pure_bind]
        simp only [Verifier.run, bind_pure]
      rw [hrun]; exact hPr
    · -- `n > 0`: last round index `m + n > m`, so `toFun (last) = S₂ (last) (verify …) tr.snd`.
      rw [dif_neg (show ¬ ((Fin.last (m + n)) : ℕ) ≤ m from by simp only [Fin.val_last]; omega)]
        at hNeg
      -- re-index `hNeg`'s `⟨last - m, _⟩` as `Fin.last n`, swapping the partial-transcript fst/snd
      -- for the genuine `FullTranscript.fst`/`.snd` (they agree on a full transcript).
      have hNeg' : ¬ S₂ (Fin.last n)
          (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) := by
        intro hc; apply hNeg
        convert hc using 2 <;>
          first
            | (simp only [Fin.val_last]; omega)
            | -- `verify` on the two notions of phase-1 prefix agree
              (congr 1; exact eq_of_heq (HEq.trans (cast_heq _ _) (htFstHeq tr)))
            | -- the two notions of phase-2 suffix agree
              exact htSndHeq tr
      -- apply `S₂.toFun_full` and identify the appended verifier's run with `V₂`'s
      have hPr := S₂.toFun_full (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) hNeg'
      -- `(V₁.append V₂).run stmt₁ tr = V₂.run (verify stmt₁ tr.fst) tr.snd`:
      -- the appended verifier runs `V₁` (deterministic `pure`) then `V₂`; the `pure` bind collapses.
      have hrun : (V₁.append V₂).run stmt₁ tr
          = V₂.run (verify stmt₁ (FullTranscript.fst tr)) (FullTranscript.snd tr) := by
        subst hVerify
        show (do return ← V₂.verify (← (pure (verify stmt₁ (FullTranscript.fst tr)))) _) = _
        rw [pure_bind]
        simp only [Verifier.run, bind_pure]
      rw [hrun]; exact hPr

end Verifier

section Execution

namespace Prover

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}
    {stmt : Stmt₁} {wit : Wit₁}

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

-- Note: Need to define a function that "extracts" a second prover from the combined prover

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

-- theorem append_run_interp {m : Type → Type} [Monad m] [m.IsCommutative]
--     {interp : OracleImpl oSpec m} : ((R₁.append R₂).run stmt wit).runM interp =
--         (do
--           let ⟨ctx₁, stmt₂, transcript₁⟩ ← liftM (R₁.run stmt wit)
--           let ⟨ctx₂, stmt₃, transcript₂⟩ ← liftM (R₂.run stmt₂ ctx₁.2)
--           return ⟨ctx₂, stmt₃, transcript₁ ++ₜ transcript₂⟩).runM interp := by
--   unfold run append
--   simp [Prover.append_run, Verifier.append_run]

end Reduction

end Execution
