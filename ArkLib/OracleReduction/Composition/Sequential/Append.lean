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

/-- Specialize `V₁.hEq i` to the type equality `OStmt₁ k = OStmt₂ i` under the branch witness
`h : V₁.embed i = Sum.inl k` (oriented source-first, to match the `congrArg OracleInterface`
cast shape used by `OracleVerifier.castMessageQuery`). -/
theorem hEqInl (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (i : ιₛ₂) (k : ιₛ₁) (h : V₁.embed i = Sum.inl k) : OStmt₁ k = OStmt₂ i := by
  have := V₁.hEq i; rw [h] at this; exact this.symm

/-- Specialize `V₁.hEq i` to the type equality `pSpec₁.Message k = OStmt₂ i` under the branch witness
`h : V₁.embed i = Sum.inr k`. -/
theorem hEqInr (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    (i : ιₛ₂) (k : pSpec₁.MessageIdx) (h : V₁.embed i = Sum.inr k) :
    pSpec₁.Message k = OStmt₂ i := by
  have := V₁.hEq i; rw [h] at this; exact this.symm

/-- Per-query body emitting a query to `V₁`'s output oracle interface at an index that `V₁.embed`
maps to an *input* oracle statement `OStmt₁ k` (i.e. `V₁.embed i = .inl k`). The interface `O` (here
`Oₛ₂ i`) agrees, up to the type equality `hSt : OStmt₁ k = T`, with the source interface `Oₛ₁ k` via
the coherence equality `hO`. The query is routed straight into `[OStmt₁]ₒ` at index `k`.

Modelled line-by-line on `emitMessageQuery` / `OracleVerifier.castMessageQuery` (`Cast.lean`): the
`subst hSt; subst hO` collapse turns `O` into the registered source interface `Oₛ₁ k`, so the query
and its response have exactly the oracle-spec types. -/
private def emitOStmtQueryInl
    {T : Type} (O : OracleInterface T)
    (k : ιₛ₁) (hSt : OStmt₁ k = T)
    (hO : O = _root_.cast (congrArg OracleInterface hSt) (Oₛ₁ k))
    (q : O.Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (O.Response q) := by
  subst hSt
  subst hO
  exact query (spec := oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ))
    (Sum.inr (Sum.inl ⟨k, q⟩))

/-- Per-query body for the case `V₁.embed i = .inr k`: `V₁`'s output oracle for `OStmt₂ i` is the
prover's `pSpec₁`-message `pSpec₁.Message k` (answered, in the appended spec, at `MessageIdx.inl k`).
The interface `O` agrees, up to `hSt : pSpec₁.Message k = T`, with `Oₘ₁ k` via `hO`.
After collapsing the casts we delegate to the proven `emitMessageInl` router. -/
private def emitOStmtQueryInr
    {T : Type} (O : OracleInterface T)
    (k : pSpec₁.MessageIdx) (hSt : pSpec₁.Message k = T)
    (hO : O = _root_.cast (congrArg OracleInterface hSt) (Oₘ₁ k))
    (q : O.Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) (O.Response q) := by
  subst hSt
  subst hO
  exact emitMessageInl (pSpec₂ := pSpec₂) (OStmt₁ := OStmt₁) k q

/-- Coherence side condition for `OracleVerifier.append` at the oracle-interface level.

`OracleVerifier.hEq` only records a *type* equality `OStmt₂ i = (source type)`; faithfully routing a
query `q : (Oₛ₂ i).Query` to the underlying source oracle additionally requires the registered
`OracleInterface` instances to agree (the output-oracle-statement interfaces `Oₛ₂` are *free*
parameters of `OracleVerifier`, cf. the commented-out `Oₛₒ` field in `Basic.lean`). This is the
direct analogue of `OracleVerifier.LiftContextCoherent` (#433) for `liftContext`.

`hCohInl`/`hCohInr` state, in the exact `cast (congrArg OracleInterface hSt) (source)` shape consumed
by `emitOStmtQuery{Inl,Inr}`, that `Oₛ₂ i` agrees with the source interface (`Oₛ₁ k` resp. `Oₘ₁ k`)
selected by `V₁.embed i`, conditioned on the corresponding `embed`-branch witness `h`. Honest
verifiers (e.g. the LogUp outer verifier) discharge both by `rfl`/`simp`. -/
class AppendCoherent (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁) : Prop where
  hCohInl : ∀ (i : ιₛ₂) (k : ιₛ₁) (h : V₁.embed i = Sum.inl k),
    (Oₛ₂ i) = _root_.cast (congrArg OracleInterface (hEqInl V₁ i k h)) (Oₛ₁ k)
  hCohInr : ∀ (i : ιₛ₂) (k : pSpec₁.MessageIdx) (h : V₁.embed i = Sum.inr k),
    (Oₛ₂ i) = _root_.cast (congrArg OracleInterface (hEqInr V₁ i k h)) (Oₘ₁ k)

/-- Emit a query to `V₁`'s output oracle statement `OStmt₂ i`, faithfully routed into the
appended-spec oracle context.

If `V₁.embed i = .inl k`, the query is sent to the input oracle statement `OStmt₁ k`; if `.inr k`, it
is sent (via `emitMessageInl`) to the appended `pSpec₁`-message at `MessageIdx.inl k`. The transport
of the query/response across the type equality `V₁.hEq i` is justified by the instance-coherence side
condition `AppendCoherent V₁` (the same kind of side condition resolved by
`OracleVerifier.LiftContextCoherent` for `liftContext`). -/
def emitOStmt₂Query (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [coh : AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (i : ιₛ₂) (q : (Oₛ₂ i).Query) :
    OracleComp (oSpec + ([OStmt₁]ₒ + [(pSpec₁ ++ₚ pSpec₂).Message]ₒ)) ((Oₛ₂ i).Response q) := by
  -- Case on how `V₁.embed` derives `OStmt₂ i`.
  cases h : V₁.embed i with
  | inl k =>
      exact emitOStmtQueryInl (Oₛ₁ := Oₛ₁) (pSpec₂ := pSpec₂)
        (Oₛ₂ i) k (hEqInl V₁ i k h) (coh.hCohInl i k h) q
  | inr k =>
      exact emitOStmtQueryInr (Oₛ₁ := Oₛ₁) (pSpec₂ := pSpec₂)
        (Oₛ₂ i) k (hEqInr V₁ i k h) (coh.hCohInr i k h) q

/-- Router carrying `V₂`'s oracle context into the appended-spec oracle context: `oSpec` passes
through; `OStmt₂`-queries are answered via `V₁`'s output oracle statements (`emitOStmt₂Query`);
`pSpec₂`-message queries are emitted at `MessageIdx.inr`. -/
def router₂ (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁] :
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
    [AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
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
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₃ OStmt₃ (pSpec₁ ++ₚ pSpec₂) where
  verify := OracleVerifier.Append.verify V₁ V₂

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

namespace OracleVerifier.Append

/-- How the composite `(OracleVerifier.append V₁ V₂).embed` evaluates: it factors through
`V₂.embed` then `V₁.embed`.  The three cases match the three coherence sources (input oracle of
`V₁`; `pSpec₁`-message; `pSpec₂`-message). -/
theorem append_embed_eq (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) (i : ιₛ₃) :
    (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂).embed i =
      match V₂.embed i with
      | Sum.inl j => (V₁.embed j).map id MessageIdx.inl
      | Sum.inr j => Sum.inr (MessageIdx.inr j) := by
  rcases h : V₂.embed i with j | j
  · rcases h' : V₁.embed j with k | k <;>
      simp [OracleVerifier.append, Function.Embedding.trans, Function.Embedding.sumMap,
        Equiv.sumAssoc, h, h', Sum.map]
  · simp [OracleVerifier.append, Function.Embedding.trans, Function.Embedding.sumMap,
      Equiv.sumAssoc, h, Sum.map]

/-- `hCohInl`/`hCohInr` in heterogeneous form: the output oracle interface `Oₛ₂ i` is `HEq` to the
routed source interface. This is just the `cast`-removed restatement of the class fields. -/
theorem AppendCoherent.hCohInl_heq (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [c : AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (i : ιₛ₂) (k : ιₛ₁) (h : V₁.embed i = Sum.inl k) : HEq (Oₛ₂ i) (Oₛ₁ k) := by
  rw [c.hCohInl i k h]; exact (cast_heq _ _)

theorem AppendCoherent.hCohInr_heq (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [c : AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (i : ιₛ₂) (k : pSpec₁.MessageIdx) (h : V₁.embed i = Sum.inr k) : HEq (Oₛ₂ i) (Oₘ₁ k) := by
  rw [c.hCohInr i k h]; exact (cast_heq _ _)

/-- **Compositional coherence.** If `V₁` and `V₂` are each `AppendCoherent`, then so is their
composite `OracleVerifier.append V₁ V₂`, viewed as an outer verifier whose appended-protocol message
oracles use the canonical `instOracleInterfaceMessageAppend`. The output oracle interface `Oₛ₃ i`
is routed (through `V₂.embed` then `V₁.embed`) to one of `Oₛ₁`, `Oₘ₁`, or `Oₘ₂`; in each case the
required interface agreement is supplied by `c₂`/`c₁` together with the appended-message agreement
lemmas `instAppend_inl_heq`/`instAppend_inr_heq`. -/
instance AppendCoherent.append
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [c₁ : AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    [c₂ : AppendCoherent (Oₛ₁ := Oₛ₂) (Oₛ₂ := Oₛ₃) (Oₘ₁ := Oₘ₂) V₂] :
    AppendCoherent (Oₛ₁ := Oₛ₁)
      (Oₛ₂ := Oₛ₃)
      (Oₘ₁ := instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))
      (OracleVerifier.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁ V₂) where
  hCohInl := fun i k h => by
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    -- `(append V₁ V₂).embed i = .inl k` forces `V₂.embed i = .inl j`, `V₁.embed j = .inl k`.
    rw [append_embed_eq] at h
    rcases hj : V₂.embed i with j | j <;> rw [hj] at h <;> simp only [] at h
    · rcases hjk : V₁.embed j with k' | k' <;> rw [hjk] at h <;> simp [Sum.map] at h
      subst h
      exact (AppendCoherent.hCohInl_heq (c := c₂) V₂ i j hj).trans
        (AppendCoherent.hCohInl_heq (c := c₁) V₁ j k' hjk)
    · simp [Sum.map] at h
  hCohInr := fun i k h => by
    apply eq_of_heq
    refine HEq.trans ?_ (cast_heq _ _).symm
    rw [append_embed_eq] at h
    rcases hj : V₂.embed i with j | j <;> rw [hj] at h <;> simp only [] at h
    · rcases hjk : V₁.embed j with k' | k' <;> rw [hjk] at h <;> simp [Sum.map] at h
      subst h
      exact (AppendCoherent.hCohInl_heq (c := c₂) V₂ i j hj).trans
        ((AppendCoherent.hCohInr_heq (c := c₁) V₁ j k' hjk).trans
          (instAppend_inl_heq (pSpec₂ := pSpec₂) k').symm)
    · simp [Sum.map] at h
      subst h
      exact (AppendCoherent.hCohInr_heq (c := c₂) V₂ i j hj).trans
        (instAppend_inr_heq (pSpec₁ := pSpec₁) j).symm

end OracleVerifier.Append

/-- **NAMED RESIDUAL (deep, structural router/`simulateQ` interchange).** The plain verifier extracted
from the composite oracle verifier equals the composition of the two extracted plain verifiers.

The LHS `(OracleVerifier.append V₁ V₂).toVerifier` runs the router-composed `OracleVerifier.Append.verify`
(`V₁` via `router₁`, then `V₂` via `router₂ V₁`) under a *single* `simulateQ (simOracle2 oSpec oStmt₁
(messages over the appended spec))`. The RHS runs `V₁.toVerifier` (its own `simulateQ` over
`OStmt₁`/`pSpec₁.Message`) then `V₂.toVerifier` (its own `simulateQ` over `OStmt₂`/`pSpec₂.Message`).
Proving them equal needs the two router-interchange facts:
  * `simulateQ (simOracle2 … appendedMsgs) ∘ simulateQ router₁` collapses to
    `simulateQ (simOracle2 oSpec oStmt₁ pSpec₁.messages)` — i.e. `router₁` followed by the appended
    message oracle answers `pSpec₁`-messages at `MessageIdx.inl` exactly as `V₁`'s own oracle would
    (using `instAppend_inl_heq`/`Message_inl`);
  * likewise `router₂ V₁` followed by the appended oracle answers `pSpec₂`-messages at `MessageIdx.inr`
    (via `instAppend_inr_heq`) and `OStmt₂`-queries via `emitOStmt₂Query` — which, under the
    `AppendCoherent` instance, route to `V₁`'s output oracle statements exactly as `V₂.toVerifier`'s
    own `simOracle2` would, the intermediate `oStmt₂` being `V₁.toVerifier`'s derived output oracles.
This is the structural sibling of `Prover.append_run` (a `simulateQ`/routing interchange rather than a
`runToRound` interchange) and is the deep obstruction here; it is *not* probabilistic. It feeds the
four `OracleVerifier.append_*` security theorems (their `convert … ; simp [append_toVerifier]` steps).
-/
theorem router₁_compose (oStmt : ∀ i, OStmt₁ i) (transcript : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    ((OracleInterface.simOracle2 oSpec oStmt transcript.messages) ∘ₛ router₁ (pSpec₂ := pSpec₂)) =
      OracleInterface.simOracle2 oSpec oStmt transcript.fst.messages := by
  sorry

theorem router₂_compose (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [coh : AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (oStmt : ∀ i, OStmt₁ i) (transcript : (pSpec₁ ++ₚ pSpec₂).FullTranscript) :
    ((OracleInterface.simOracle2 oSpec oStmt transcript.messages) ∘ₛ router₂ V₁) =
      OracleInterface.simOracle2 oSpec (fun i => match h : V₁.embed i with
        | Sum.inl j => (V₁.hEq i ▸ h ▸ oStmt j)
        | Sum.inr j => (V₁.hEq i ▸ h ▸ transcript.fst.messages j))
        transcript.snd.messages := by
  sorry

theorem oStmt_append_congr (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [coh : AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    (oStmt : ∀ i, OStmt₁ i) (transcript : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (i : ιₛ₃) :
    (match h : (OracleVerifier.append V₁ V₂).embed i with
      | Sum.inl j => ((OracleVerifier.append V₁ V₂).hEq i ▸ h ▸ oStmt j : OStmt₃ i)
      | Sum.inr j => ((OracleVerifier.append V₁ V₂).hEq i ▸ h ▸ transcript.messages j : OStmt₃ i))
    =
    (match h : V₂.embed i with
      | Sum.inl j => (V₂.hEq i ▸ h ▸ match h' : V₁.embed j with
          | Sum.inl k => (V₁.hEq j ▸ h' ▸ oStmt k : OStmt₂ j)
          | Sum.inr k => (V₁.hEq j ▸ h' ▸ transcript.fst.messages k : OStmt₂ j) : OStmt₃ i)
      | Sum.inr j => (V₂.hEq i ▸ h ▸ transcript.snd.messages j : OStmt₃ i)) := by
  sorry

@[simp]
lemma OracleVerifier.append_toVerifier
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [coh : OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂) :
      (OracleVerifier.append V₁ V₂).toVerifier =
        Verifier.append V₁.toVerifier V₂.toVerifier := by
  ext ⟨stmt, oStmt⟩ transcript
  apply OptionT.ext
  simp only [OracleVerifier.append, Verifier.append, OracleVerifier.toVerifier, OptionT.run_bind,
    OracleVerifier.Append.verify]
  dsimp only
  rw [simulateQ_optionT_bind']
  rw [QueryImpl.simulateQ_compose, QueryImpl.simulateQ_compose]
  rw [router₁_compose, router₂_compose]
  dsimp only
  congr 1
  refine bind_congr fun x => ?_
  rcases x with _ | stmt₂
  · rfl
  · dsimp only
    congr 1
    refine bind_congr fun y => ?_
    rcases y with _ | stmt₃
    · rfl
    · dsimp only
      congr 1
      funext i
      exact oStmt_append_congr V₁ V₂ oStmt transcript i

/-- Sequential composition of oracle reductions is just the sequential composition of the oracle
  provers and oracle verifiers. -/
def OracleReduction.append (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂) :
      OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₃ OStmt₃ Wit₃ (pSpec₁ ++ₚ pSpec₂) where
  prover := Prover.append R₁.prover R₂.prover
  verifier := OracleVerifier.append R₁.verifier R₂.verifier

/-- The verifier of a composed oracle reduction is again `AppendCoherent` (its `verifier` field is
definitionally `OracleVerifier.append R₁.verifier R₂.verifier`), so chains of `OracleReduction.append`
synthesize their coherence side conditions automatically from the leaves. -/
instance OracleVerifier.Append.AppendCoherent.oracleReductionAppend
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₂) (Oₛ₂ := Oₛ₃) (Oₘ₁ := Oₘ₂) R₂.verifier] :
    OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₃)
      (Oₘ₁ := instOracleInterfaceMessageAppend (pSpec₁ := pSpec₁) (pSpec₂ := pSpec₂))
      (OracleReduction.append (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁ R₂).verifier :=
  OracleVerifier.Append.AppendCoherent.append R₁.verifier R₂.verifier

@[simp]
lemma OracleReduction.append_toReduction
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
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

section Security

open scoped NNReal

section Protocol

variable {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
    {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
    [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)}
    {rel₃ : Set (Stmt₃ × Wit₃)}

namespace Reduction

/-- **NAMED RESIDUAL — reduces to the single keystone `Prover.append_run`.** Unlike the soundness
theorems (which quantify over arbitrary malicious provers), completeness uses the *honest* composite
prover `(R₁.prover).append (R₂.prover)`, so the run factoring is exactly `Prover.append_run` (the deep
keystone in this file, whose per-round seam/interior reductions are all proven; only the right-block
run induction + output assembly remain). Once `Prover.append_run` is available, the proof is:
1. rewrite `(R₁.append R₂).run` via `Prover.append_run` (prover side) + `Verifier.append_run` (proven,
   `rfl`, verifier side) into the sequential `R₁.run >>= R₂.run` shape;
2. push the success-probability through the bind: the phase-1 output `(stmt₂, wit₂) ∈ rel₂` holds
   except w.p. `completenessError₁` (by `h₁`), and conditioned on it the phase-2 output is in `rel₃`
   except w.p. `completenessError₂` (by `h₂`);
3. union bound ⇒ total error `completenessError₁ + completenessError₂`.
The genuinely-deep dependency is therefore *only* `Prover.append_run`; the probabilistic step is the
standard two-stage success-probability union bound. -/
theorem reduction_append_completeness
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := by
  sorry

theorem reduction_append_perfectCompleteness
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  unfold perfectCompleteness at h₁ h₂ ⊢
  simpa using reduction_append_completeness R₁ R₂ h₁ h₂

end Reduction

namespace Verifier

/-- **NAMED RESIDUAL (deep, arbitrary-prover seam decomposition).** Sequential composition preserves
soundness with the additive error `soundnessError₁ + soundnessError₂`.

The remaining obstruction is *not* `Prover.append_run` (which only factors an *honest* `P₁.append P₂`):
soundness quantifies over an *arbitrary malicious* prover `P` over `pSpec₁ ++ₚ pSpec₂`, so the proof
must decompose `P` at the seam round `m` into a `pSpec₁`-phase malicious prover `P↾₁` (running rounds
`0..m-1`, with `P`'s round-`m` output context as its `output`) and a `pSpec₂`-phase malicious prover
`P↾₂` (resuming from that context). Then:
1. `Verifier.append_run` (proven, `rfl`) splits `(V₁.append V₂).run = V₁.run tr.fst >>= V₂.run tr.snd`.
2. The bad event `stmtOut ∈ lang₃` decomposes through the intermediate statement `stmt₂`:
   either `stmt₂ ∉ lang₂` (bounded by `h₁` applied to `P↾₁`, since `stmt₁ ∉ lang₁`) or
   `stmt₂ ∈ lang₂` and `stmtOut ∈ lang₃` (bounded by `h₂` applied to `P↾₂`).
3. A union bound over these two events gives `soundnessError₁ + soundnessError₂`.
The genuinely new content is the malicious-prover seam decomposition (no analogue of the honest
`Prover.append` exists in the codebase yet) plus the probabilistic union bound; both are deep. -/
theorem append_soundness {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  sorry

/-- **NAMED RESIDUAL (deep, arbitrary-prover seam decomposition + extractor composition).**
Sequential composition preserves straightline knowledge soundness with additive error.

The composite straightline extractor is `Extractor.Straightline.append` (proven, above): it runs `V₁`
to derive the intermediate statement, then `E₂` then `E₁`. The remaining obstruction mirrors
`append_soundness`: the malicious prover `P` over `pSpec₁ ++ₚ pSpec₂` must be seam-decomposed into
phase-1 / phase-2 malicious provers so that `h₁`/`h₂` (the per-phase extractor guarantees) apply, and
the bad knowledge event `(stmtIn, witIn') ∉ relIn ∧ (stmtOut, witOut) ∈ relOut` must be union-bounded
through the intermediate `(stmt₂, wit₂)` pair. The extractor query-log routing across the seam
(`proveQueryLog.fst` / `verifyQueryLog`) is the additional new content over `append_soundness`. -/
theorem append_knowledgeSoundness
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl
        rel₁ rel₃ (knowledgeError₁ + knowledgeError₂) := by
  sorry

/-- **NAMED RESIDUAL (deep) + DOCUMENTED STATEMENT GAP (missing side conditions).**
Sequential composition preserves round-by-round soundness, with the per-round error obtained by
routing through `ChallengeIdx.sumEquiv`.

The composite state function is intended to be `Verifier.StateFunction.append` (proven, above), which
witnesses the existential in the target `rbrSoundness`. *However*, `StateFunction.append` carries two
side hypotheses that this theorem's statement does not currently provide, so as stated the theorem
cannot be discharged via the intended route (a faithful proof must thread these in):
  * `hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩` — the first verifier must be
    *deterministic & non-failing*. The crossing inversion of `S₁.toFun_full` into the pointwise
    `verify … ∉ lang₂` (the mechanism that makes the composite `toFun_full` true, per the
    `StateFunction.append` statement-repair note) requires `V₁` to be a `pure`-verifier.
  * `hInit : ∃ s, s ∈ support init` — at least one reachable initial state, else the `Pr = 0`
    inversion is vacuous.
With those two hypotheses added (or a more general `StateFunction.append` that drops determinism), the
remaining content is: instantiate the composite state function, then per challenge round `i` of the
appended protocol case on whether `i` lies in phase 1 (defer to `h₁`'s round bound, the appended
challenge index `ChallengeIdx.inl i` carrying error `rbrSoundnessError₁ i`) or phase 2 (defer to
`h₂`, `ChallengeIdx.inr`), the partial transcript split by the proven `Transcript.fst`/`.snd`
transports — a per-round probabilistic argument with no honest-prover seam (rbr soundness is
single-round, so no `Prover.append_run` is needed here). -/
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

/-- **NAMED RESIDUAL (deep) + DOCUMENTED STATEMENT GAP (missing side conditions).**
Sequential composition preserves round-by-round knowledge soundness.

The composite knowledge state function / round-by-round extractor are intended to be the proven
`Verifier.StateFunction.append` (for the state-function leg) and `Extractor.RoundByRound.append` (the
round-by-round extractor, proven above, which threads the intermediate statement via a deterministic
`verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂`). As with `append_rbrSoundness`, the statement is
missing the two side hypotheses that the intended state-function construction requires:
  * `hVerify` (V₁ deterministic & non-failing) — also supplies the very `verify` function that
    `Extractor.RoundByRound.append` consumes; without it neither the state-function nor the extractor
    leg can be instantiated;
  * `hInit : ∃ s, s ∈ support init`.
With those added, the residue is the per-round knowledge bound: case on phase-1 vs phase-2 of the
appended challenge index, defer to `h₁`/`h₂`, and identify the composite `extractMid`/`extractOut`
(per `Extractor.RoundByRound.append`'s construction) with the per-phase extractors across the seam. -/
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

variable {Stmt₁ : Type} {ιₛ₁ : Type} {OStmt₁ : ιₛ₁ → Type}
    [Oₛ₁ : ∀ i, OracleInterface (OStmt₁ i)]
    {Wit₁ : Type}
    {Stmt₂ : Type} {ιₛ₂ : Type} {OStmt₂ : ιₛ₂ → Type}
    [Oₛ₂ : ∀ i, OracleInterface (OStmt₂ i)]
    {Wit₂ : Type}
    {Stmt₃ : Type} {ιₛ₃ : Type} {OStmt₃ : ιₛ₃ → Type}
    [Oₛ₃ : ∀ i, OracleInterface (OStmt₃ i)]
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

theorem append_completeness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    {completenessError₁ completenessError₂ : ℝ≥0}
    (h₁ : R₁.completeness init impl rel₁ rel₂ completenessError₁)
    (h₂ : R₂.completeness init impl rel₂ rel₃ completenessError₂) :
      (R₁.append R₂).completeness init impl
        rel₁ rel₃ (completenessError₁ + completenessError₂) := by
  unfold completeness
  convert Reduction.reduction_append_completeness R₁.toReduction R₂.toReduction h₁ h₂
  simp only [append_toReduction]

theorem append_perfectCompleteness
    (R₁ : OracleReduction oSpec Stmt₁ OStmt₁ Wit₁ Stmt₂ OStmt₂ Wit₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) R₁.verifier]
    (R₂ : OracleReduction oSpec Stmt₂ OStmt₂ Wit₂ Stmt₃ OStmt₃ Wit₃ pSpec₂)
    (h₁ : R₁.perfectCompleteness init impl rel₁ rel₂)
    (h₂ : R₂.perfectCompleteness init impl rel₂ rel₃) :
      (R₁.append R₂).perfectCompleteness init impl rel₁ rel₃ := by
  unfold perfectCompleteness
  convert Reduction.reduction_append_perfectCompleteness R₁.toReduction R₂.toReduction h₁ h₂
  simp only [append_toReduction]

end OracleReduction

namespace OracleVerifier

variable {lang₁ : Set (Stmt₁ × (∀ i, OStmt₁ i))}
    {lang₂ : Set (Stmt₂ × (∀ i, OStmt₂ i))}
    {lang₃ : Set (Stmt₃ × (∀ i, OStmt₃ i))}

theorem append_soundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {soundnessError₁ soundnessError₂ : ℝ≥0}
    (h₁ : V₁.soundness init impl lang₁ lang₂ soundnessError₁)
    (h₂ : V₂.soundness init impl lang₂ lang₃ soundnessError₂) :
      (V₁.append V₂).soundness init impl lang₁ lang₃ (soundnessError₁ + soundnessError₂) := by
  unfold soundness
  convert Verifier.append_soundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

theorem append_knowledgeSoundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
    (V₂ : OracleVerifier oSpec Stmt₂ OStmt₂ Stmt₃ OStmt₃ pSpec₂)
    {knowledgeError₁ knowledgeError₂ : ℝ≥0}
    (h₁ : V₁.knowledgeSoundness init impl rel₁ rel₂ knowledgeError₁)
    (h₂ : V₂.knowledgeSoundness init impl rel₂ rel₃ knowledgeError₂) :
      (V₁.append V₂).knowledgeSoundness init impl rel₁ rel₃
        (knowledgeError₁ + knowledgeError₂) := by
  unfold knowledgeSoundness
  convert Verifier.append_knowledgeSoundness V₁.toVerifier V₂.toVerifier h₁ h₂
  simp only [append_toVerifier]

theorem append_rbrSoundness (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
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

theorem append_rbrKnowledgeSoundness
    (V₁ : OracleVerifier oSpec Stmt₁ OStmt₁ Stmt₂ OStmt₂ pSpec₁)
    [OracleVerifier.Append.AppendCoherent (Oₛ₁ := Oₛ₁) (Oₛ₂ := Oₛ₂) (Oₘ₁ := Oₘ₁) V₁]
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

/-! ### Left-block run characterization support

The following support lemmas (proven by `Fin.induction` + the HEq transport toolkit) establish that running the appended prover `P₁.append P₂` up to a *left-half* round `j ≤ m` is heterogeneously the `liftM` (along the left challenge `SubSpec`) of running `P₁` up to round `j`.  The keystone is `append_runToRound_left`; its seam specialization `append_runToRound_seam` (target round `m`) is the entry point for `append_run`. -/

/-- Support lemma: PrvState of the appended prover matches `P₁`'s on the left half. -/
theorem append_PrvState_castLE (j : Fin (m + 1)) :
    (P₁.append P₂).PrvState (j.castLE (by omega)) = P₁.PrvState j := by
  unfold Prover.append
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) (j.castLE (by omega)) : Fin (m + 1 + n)) = Fin.castAdd n j from by
        ext; simp]
  rw [Fin.append_left]

/-- Support lemma `append_Transcript_castLE`: the appended-protocol transcript type at a left-half
round equals `pSpec₁`'s transcript type. -/
theorem append_Transcript_castLE (j : Fin (m + 1)) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (j.castLE (by omega)) = pSpec₁.Transcript j := by
  show ((pSpec₁ ++ₚ pSpec₂).take _ _).FullTranscript = (pSpec₁.take _ _).FullTranscript
  unfold ProtocolSpec.FullTranscript ProtocolSpec.take
  apply pi_congr
  intro i
  have hi : (i : ℕ) < m := by
    have h1 := i.isLt
    have h2 := j.isLt
    simp only [Fin.val_castLE] at h1
    omega
  simp only [Fin.take_apply, Fin.vappend_eq_append]
  rw [show (Fin.castLE (by omega) i : Fin (m + n)) = Fin.castAdd n ⟨i, hi⟩ from by ext; simp]
  rw [Fin.append_left]
  congr 1

/-- Support lemma `append_input_heq`: the appended prover's `input` is heterogeneously equal to
`P₁`'s `input`. -/
theorem append_input_heq :
    HEq ((P₁.append P₂).input (stmt, wit)) (P₁.input (stmt, wit)) := by
  unfold Prover.append
  dsimp only
  simp only [id_eq]
  exact HEq.rfl

/-- Support lemma `prodMk_heq`: heterogeneous congruence for pairs whose component types vary. -/
theorem prodMk_heq {α α' β β' : Type _} {a : α} {a' : α'} {b : β} {b' : β'}
    (hα : α = α') (hβ : β = β') (ha : HEq a a') (hb : HEq b b') :
    HEq (Prod.mk a b) (Prod.mk a' b') := by
  subst hα hβ
  rw [eq_of_heq ha, eq_of_heq hb]

/-- Support lemma `pure_heq_pure`: heterogeneous congruence for `pure` in `OracleComp`, lifting a
HEq of values (over equal element types) to a HEq of the pure computations. -/
theorem pure_heq_pure {ι : Type} {spec : OracleSpec ι} {α α' : Type _} {a : α} {a' : α'}
    (hα : α = α') (ha : HEq a a') :
    HEq (pure a : OracleComp spec α) (pure a' : OracleComp spec α') := by
  subst hα
  rw [eq_of_heq ha]

/-- HEq congruence for `sendMessage`: equal message index and HEq state imply HEq results. -/
theorem sendMessage_heq_congr {P : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {idx₁ idx₂ : pSpec₁.MessageIdx} (hidx : idx₁ = idx₂)
    {s₁ : P.PrvState idx₁.1.castSucc} {s₂ : P.PrvState idx₂.1.castSucc} (hs : HEq s₁ s₂) :
    HEq (P.sendMessage idx₁ s₁) (P.sendMessage idx₂ s₂) := by
  subst hidx
  rw [eq_of_heq hs]

/-- HEq congruence for `receiveChallenge`: equal challenge index and HEq state imply HEq results. -/
theorem receiveChallenge_heq_congr {P : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {idx₁ idx₂ : pSpec₁.ChallengeIdx} (hidx : idx₁ = idx₂)
    {s₁ : P.PrvState idx₁.1.castSucc} {s₂ : P.PrvState idx₂.1.castSucc} (hs : HEq s₁ s₂) :
    HEq (P.receiveChallenge idx₁ s₁) (P.receiveChallenge idx₂ s₂) := by
  subst hidx
  rw [eq_of_heq hs]

/-- Split a HEq of pairs (over componentwise-equal types) into HEqs of the components. -/
theorem prod_heq_split {α α' β β' : Type _} (hα : α = α') (hβ : β = β')
    {a : α} {a' : α'} {b : β} {b' : β'} (h : HEq (Prod.mk a b) (Prod.mk a' b')) :
    HEq a a' ∧ HEq b b' := by
  subst hα hβ
  rw [heq_iff_eq] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
  exact ⟨HEq.rfl, HEq.rfl⟩

/-- HEq congruence for monadic `bind` in `OracleComp` where the element types may differ
propositionally.  If the bound computations are HEq (over equal element types) and the
continuations send HEq inputs to HEq outputs, the binds are HEq. -/
theorem bind_heq_congr {ι : Type} {spec : OracleSpec ι} {α α' β β' : Type _}
    (hα : α = α') (hβ : β = β')
    {ma : OracleComp spec α} {ma' : OracleComp spec α'}
    {f : α → OracleComp spec β} {f' : α' → OracleComp spec β'}
    (hma : HEq ma ma') (hf : ∀ (a : α) (a' : α'), HEq a a' → HEq (f a) (f' a')) :
    HEq (ma >>= f) (ma' >>= f') := by
  subst hα hβ
  rw [eq_of_heq hma]
  have : f = f' := funext fun a => eq_of_heq (hf a a HEq.rfl)
  rw [this]

/-- HEq congruence for `OracleComp.liftComp` (along the canonical query-level `MonadLiftT`): HEq
inputs (over equal element types) give HEq lifts.  Unlike `liftM_heq_congr`, `liftComp` depends only
on the *query-level* `MonadLiftT (OracleQuery spec) (OracleQuery superSpec)`, which is canonical, so
this avoids the OracleComp-level `MonadLiftT` instance diamond. -/
theorem liftComp_heq_congr {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [MonadLiftT (OracleQuery spec) (OracleQuery superSpec)] {α α' : Type}
    (hα : α = α') {ma : OracleComp spec α} {ma' : OracleComp spec α'} (hma : HEq ma ma') :
    HEq (OracleComp.liftComp ma superSpec) (OracleComp.liftComp ma' superSpec) := by
  subst hα
  rw [eq_of_heq hma]


/-- HEq congruence for `liftM` (along a fixed transitive `MonadLiftT` of `OracleComp`s): HEq inputs
(over equal element types) give HEq lifts. -/
theorem liftM_heq_congr {ι ι' : Type} {spec : OracleSpec ι} {superSpec : OracleSpec ι'}
    [MonadLiftT (OracleComp spec) (OracleComp superSpec)] {α α' : Type}
    (hα : α = α') {ma : OracleComp spec α} {ma' : OracleComp spec α'} (hma : HEq ma ma') :
    HEq (liftM ma : OracleComp superSpec α) (liftM ma' : OracleComp superSpec α') := by
  subst hα
  rw [eq_of_heq hma]

/-- HEq congruence: `liftM` (the `OracleQuery → OracleComp` embedding over the SAME spec) of HEq
queries (over equal response types) gives HEq computations. -/
theorem liftM_query_heq {ιs : Type} {spec : OracleSpec ιs} {α α' : Type}
    (hα : α = α') {q : OracleQuery spec α} {q' : OracleQuery spec α'} (hq : HEq q q') :
    HEq (liftM q : OracleComp spec α) (liftM q' : OracleComp spec α') := by
  subst hα; rw [eq_of_heq hq]

/-- HEq of two oracle queries over the same spec whose inputs agree and whose response types are
propositionally equal, with HEq continuations. -/
theorem oracleQuery_heq {ιs : Type} {spec : OracleSpec ιs} {α α' : Type}
    {t t' : spec.Domain} (ht : t = t')
    {f : spec.Range t → α} {f' : spec.Range t' → α'} (hα : α = α') (hf : HEq f f') :
    HEq (OracleQuery.mk t f) (OracleQuery.mk t' f') := by
  subst ht; subst hα; rw [eq_of_heq hf]

/-- **OracleComp-level lift-coherence.**  Lifting `mx : OracleComp spec` first through an intermediate
spec `midSpec` and then to `superSpec` agrees, as a *function*, with lifting it directly to
`superSpec`, provided the two query-level `MonadLiftT`s cohere
(`OracleQuery.liftM_eq_liftM_liftM`, which is `rfl` for the canonical `+`/transitive instances).
Proved by induction on `mx`: the `query_bind` head reduces both sides to `q.cont <$> liftM (...)`
where the inner lifts coincide by `hquery`.

This is the bridge that defuses the `OracleComp`-level `MonadLiftT` instance diamond: the *transitive*
instance `instMonadLiftTOfMonadLift spec midSpec superSpec` lifts as
`liftComp (liftComp mx midSpec) superSpec`, while the *direct* instance lifts as
`liftComp mx superSpec`. -/
theorem liftComp_liftComp {ι₁ ι₂ ι₃ : Type} {spec : OracleSpec ι₁} {midSpec : OracleSpec ι₂}
    {superSpec : OracleSpec ι₃}
    [MonadLiftT (OracleQuery spec) (OracleQuery midSpec)]
    [MonadLiftT (OracleQuery midSpec) (OracleQuery superSpec)]
    [hsd : MonadLiftT (OracleQuery spec) (OracleQuery superSpec)]
    (hquery : ∀ (t : spec.Domain),
      OracleComp.liftComp
          (liftM (spec.query t) : OracleComp midSpec (spec.Range t)) superSpec
        = (liftM (spec.query t) : OracleComp superSpec (spec.Range t)))
    {α : Type} (mx : OracleComp spec α) :
    OracleComp.liftComp (OracleComp.liftComp mx midSpec) superSpec
      = OracleComp.liftComp mx superSpec := by
  induction mx using OracleComp.inductionOn with
  | pure x => simp
  | query_bind t k ih =>
    -- Distribute both `liftComp`s through the outer bind; the tails match by `ih`.
    rw [OracleComp.liftComp_bind, OracleComp.liftComp_bind, OracleComp.liftComp_bind]
    rw [show (fun x => OracleComp.liftComp (OracleComp.liftComp (k x) midSpec) superSpec)
          = (fun x => OracleComp.liftComp (k x) superSpec) from funext ih]
    -- Reduce the (single-query) head on both sides; the inner lift coheres by `hquery`.
    congr 1
    rw [OracleComp.liftComp_query, OracleComp.liftComp_map]
    simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]
    rw [hquery t, OracleComp.liftComp_query]
    simp only [OracleQuery.cont_query, id_map, OracleQuery.input_query]


/-- `processRound` resolved at a message (`P_to_V`) round (mirror of the library's
`processRound_challenge`). -/
theorem processRound_message {ι : Type} {oSpec : OracleSpec ι} {StmtIn WitIn StmtOut WitOut : Type}
    {N : ℕ} {pSpec : ProtocolSpec N}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin N)
    (hDir : pSpec.dir j = .P_to_V)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let ⟨msg, newState⟩ ← prover.sendMessage ⟨j, hDir⟩ state
      return ⟨transcript.concat msg, newState⟩) := by
  rw [Prover.processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  dsimp only
  split <;> rename_i hDir'
  · exact absurd (hDir.symm.trans hDir') (by decide)
  · rfl

/-- Generic HEq congruence for `Fin.snoc` over dependent codomain families.  If the lengths agree,
the codomain families are HEq, the tuples are HEq and the appended elements are HEq, the two snocs
are HEq. -/
theorem Fin_snoc_heq {N N' : ℕ} (hN : N = N')
    {β : Fin (N + 1) → Type _} {β' : Fin (N' + 1) → Type _} (hβ : HEq β β')
    {T : (j : Fin N) → β j.castSucc} {T' : (j : Fin N') → β' j.castSucc} (hT : HEq T T')
    {x : β (Fin.last N)} {x' : β' (Fin.last N')} (hx : HEq x x') :
    HEq (Fin.snoc T x) (Fin.snoc T' x') := by
  subst hN
  obtain rfl : β = β' := eq_of_heq hβ
  rw [eq_of_heq hT, eq_of_heq hx]

/-- Dependent function-application HEq congruence: HEq functions (over equal domain and HEq
codomain families) applied to HEq arguments give HEq results. -/
theorem heq_app {α α' : Type _} {β : α → Type _} {β' : α' → Type _}
    (hα : α = α') (hβ : HEq β β')
    {f : (a : α) → β a} {g : (a : α') → β' a} (hfg : HEq f g)
    {a : α} {a' : α'} (haa : HEq a a') :
    HEq (f a) (g a') := by
  subst hα
  obtain rfl : β = β' := eq_of_heq hβ
  rw [eq_of_heq hfg, eq_of_heq haa]

/-- The appended-protocol message type at a left round equals `pSpec₁`'s. -/
theorem append_Message_castLE (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V) (hDir₁ : pSpec₁.dir i = .P_to_V) :
    (pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩ = pSpec₁.Message ⟨i, hDir₁⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
  rw [Fin.vappend_eq_append,
    show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]

/-- HEq congruence for `Transcript.concat` across left-round transcripts of the appended and the
`pSpec₁` protocols.  `Transcript.concat = Fin.snoc`; compared as dependent functions on `Fin (·.succ)`
via `Function.hfunext`, splitting each index into the appended `msg` (last) or an interior entry
read from the transcript. -/
theorem concat_heq (i : Fin m)
    {t : (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc}
    {t' : pSpec₁.Transcript i.castSucc}
    {msg : (pSpec₁ ++ₚ pSpec₂).«Type» (i.castLE (by omega))} {msg' : pSpec₁.«Type» i}
    (ht : HEq t t') (hm : HEq msg msg') :
    HEq (Transcript.concat msg t) (Transcript.concat msg' t') := by
  unfold Transcript.concat
  have hlenC : (↑(i.castLE (show m ≤ m + n by omega)).castSucc : ℕ) = ↑i.castSucc := by simp
  -- The two `Fin.snoc`s differ only in (equal) length, (HEq) codomain family, tuple and element.
  refine Fin_snoc_heq hlenC ?_ ht ?_
  · -- codomain families agree: for `j < m`, the appended `«Type»` coincides with `pSpec₁`'s.
    have hsucc : (↑(i.castLE (show m ≤ m + n by omega)).succ : ℕ) = ↑i.succ := by simp
    apply Function.hfunext (by congr 1)
    intro b b' hbb
    have hbv : (b : ℕ) = (b' : ℕ) :=
      Fin.heq_ext_iff hsucc |>.mp hbb
    apply heq_of_eq
    show (pSpec₁ ++ₚ pSpec₂).«Type» _ = pSpec₁.«Type» _
    -- Both indices have value `< m` (or, for the last, `= m`), but only `< m` codomain entries
    -- are read; in all cases the appended `«Type»` at a left index equals `pSpec₁`'s.
    rcases lt_or_eq_of_le (show (↑b : ℕ) ≤ m by
        have := b.isLt; simp only [Fin.val_succ] at this; omega) with hbm | hbm
    · rw [show (Fin.castLE (by omega) b : Fin (m + n)) = Fin.castAdd n ⟨b, hbm⟩ from by ext; simp]
      show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.castAdd n _) = _
      rw [Fin.vappend_eq_append, Fin.append_left]
      congr 1
      ext; simpa using hbv
    · -- `b = m` only when `b` is the last index of the snoc domain; the families still agree there
      -- because both sides evaluate the message type, equal by `append_Message_castLE`.
      exfalso
      have := b.isLt
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
  · -- the appended message ≍ `pSpec₁`'s message (`hm`).
    exact hm

/-- The appended protocol's direction at a left-half round matches `pSpec₁`'s. -/
theorem append_dir_castLE (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = pSpec₁.dir i := by
  show Fin.vappend pSpec₁.dir pSpec₂.dir (i.castLE (by omega)) = pSpec₁.dir i
  rw [Fin.vappend_eq_append,
    show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]

variable {P₁ : Prover oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁}
    {P₂ : Prover oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂}

/-- State-type equality used to transport the appended prover's state into `P₁`'s state at the
`castSucc` of a left round. -/
theorem append_PrvState_castSucc (i : Fin m) :
    (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc = P₁.PrvState i.castSucc := by
  rw [show (i.castLE (by omega)).castSucc = (i.castSucc).castLE (by omega) from by ext; simp,
    append_PrvState_castLE i.castSucc]

/-- State-type equality at the `succ` of a left round. -/
theorem append_PrvState_succ (i : Fin m) :
    (P₁.append P₂).PrvState (i.castLE (by omega)).succ = P₁.PrvState i.succ := by
  rw [show (i.castLE (by omega)).succ = (i.succ).castLE (by omega) from by ext; simp,
    append_PrvState_castLE i.succ]

/-- Transcript-type equality at the `castSucc` of a left round. -/
theorem append_Transcript_castSucc (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc = pSpec₁.Transcript i.castSucc := by
  rw [show (i.castLE (by omega)).castSucc = (i.castSucc).castLE (by omega) from by ext; simp]
  exact append_Transcript_castLE i.castSucc

/-- Transcript-type equality at the `succ` of a left round. -/
theorem append_Transcript_succ (i : Fin m) :
    (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ = pSpec₁.Transcript i.succ := by
  rw [show (i.castLE (by omega)).succ = (i.succ).castLE (by omega) from by ext; simp]
  exact append_Transcript_castLE i.succ

/-- **Left-round `sendMessage` reduction.**  The appended prover's `sendMessage` at a left round
`i < m` reduces (heterogeneously) to `P₁`'s `sendMessage`. -/
theorem append_sendMessage_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V)
    (hDir₁ : pSpec₁.dir i = .P_to_V)
    (state : (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨i.castLE (by omega), hDir⟩ state)
        (P₁.sendMessage ⟨i, hDir₁⟩ (cast (append_PrvState_castSucc i) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hlt : (↑(i.castLE (show m ≤ m + n by omega)) : ℕ) < m := by simp
  rw [id_eq, dif_pos hlt]
  have hidxeq : (⟨⟨↑(i.castLE (show m ≤ m + n by omega)), hlt⟩, by exact hDir₁⟩
      : pSpec₁.MessageIdx) = ⟨i, hDir₁⟩ := by ext; simp
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  exact sendMessage_heq_congr hidxeq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Left-round `receiveChallenge` reduction.**  The appended prover's `receiveChallenge` at a
left round `i < m` reduces (heterogeneously) to `P₁`'s `receiveChallenge`. -/
theorem append_receiveChallenge_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P)
    (hDir₁ : pSpec₁.dir i = .V_to_P)
    (state : (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨i.castLE (by omega), hDir⟩ state)
        (P₁.receiveChallenge ⟨i, hDir₁⟩ (cast (append_PrvState_castSucc i) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hlt : (↑(i.castLE (show m ≤ m + n by omega)) : ℕ) < m := by simp
  rw [dif_pos hlt]
  have hidxeq : (⟨⟨↑(i.castLE (show m ≤ m + n by omega)), hlt⟩, by exact hDir₁⟩
      : pSpec₁.ChallengeIdx) = ⟨i, hDir₁⟩ := by ext; simp
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  exact receiveChallenge_heq_congr hidxeq ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Left-round `getChallenge` reduction.**  The appended protocol's `getChallenge` at a left
challenge round `i < m` is heterogeneously equal to the `liftM` (along the left challenge `SubSpec`
`[pSpec₁.Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ`) of `pSpec₁`'s `getChallenge`.  The two
single queries coincide on the (value-equal) challenge index `i.castLE = ChallengeIdx.inl ⟨i,_⟩`; the
response types differ only by the propositional `range_challenge_append_inl` transport carried by the
SubSpec `onResponse`, so the queries are HEq. -/
theorem append_getChallenge_left (i : Fin m)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P)
    (hDir₁ : pSpec₁.dir i = .V_to_P) :
    HEq ((pSpec₁ ++ₚ pSpec₂).getChallenge ⟨i.castLE (by omega), hDir⟩)
        (liftM (pSpec₁.getChallenge ⟨i, hDir₁⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) := by
  unfold ProtocolSpec.getChallenge
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
      = pSpec₁.Challenge ⟨i, hDir₁⟩ := by
    show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
    rw [Fin.vappend_eq_append,
      show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]
  show HEq (liftM (OracleSpec.query (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        ⟨⟨i.castLE (by omega), hDir⟩, ()⟩))
      (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩) :
        OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
  -- Make the OracleQuery-level lift explicit so both sides are `liftM (· : OracleQuery superSpec)`.
  rw [show (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩) :
          OracleComp [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _)
        = liftM (liftM (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩)
            : OracleQuery [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ _) from rfl]
  refine liftM_query_heq hChalEq ?_
  rw [OracleSpec.query_def]
  show HEq (OracleQuery.mk (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) ⟨⟨i.castLE (by omega), hDir⟩, ()⟩ id)
      (MonadLift.monadLift (OracleSpec.query (spec := [pSpec₁.Challenge]ₒ) ⟨⟨i, hDir₁⟩, ()⟩))
  rw [SubSpec.liftM_eq_lift]
  refine oracleQuery_heq ?_ hChalEq ?_
  · -- inputs agree: `⟨i.castLE, hDir⟩ = onQuery ⟨i,hDir₁⟩ = ⟨ChallengeIdx.inl ⟨i,hDir₁⟩, ()⟩`.
    show (⟨⟨i.castLE (by omega), hDir⟩, ()⟩ : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Domain)
      = ⟨ChallengeIdx.inl ⟨i, hDir₁⟩, ()⟩
    congr 1
  · -- continuations: `id ≍ onResponse ⟨i,hDir₁⟩`, which is the `range_challenge_append_inl` transport.
    simp only [OracleQuery.cont_query, OracleQuery.input_query, Function.id_comp]
    have hdom : [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range ⟨⟨i.castLE (by omega), hDir⟩, ()⟩
        = [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ.Range
            ((inferInstance : [(pSpec₁).Challenge]ₒ ⊂ₒ [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ).onQuery
              ⟨⟨i, hDir₁⟩, ()⟩) := by
      show (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
        = (pSpec₁ ++ₚ pSpec₂).Challenge (ChallengeIdx.inl ⟨i, hDir₁⟩)
      congr 1
    refine Function.hfunext hdom (fun a a' haa => ?_)
    refine haa.trans ?_
    -- `a' ≍ onResponse ⟨i,hDir₁⟩ a'`; `onResponse` is a type-level `▸` (= `cast`) transport.
    dsimp only [SubSpec.onResponse]
    refine HEq.symm ?_
    generalize_proofs h
    exact cast_heq h a'

/-- `processRound` resolved at a challenge (`V_to_P`) round (mirror of `processRound_message`). -/
theorem processRound_challenge' {ι : Type} {oSpec : OracleSpec ι}
    {StmtIn WitIn StmtOut WitOut : Type} {N : ℕ} {pSpec : ProtocolSpec N}
    (prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) (j : Fin N)
    (hDir : pSpec.dir j = .V_to_P)
    (currentResult : OracleComp (oSpec + [pSpec.Challenge]ₒ)
      (pSpec.Transcript j.castSucc × prover.PrvState j.castSucc)) :
    prover.processRound j currentResult = (do
      let ⟨transcript, state⟩ ← currentResult
      let challenge ← pSpec.getChallenge ⟨j, hDir⟩
      letI newState := (← prover.receiveChallenge ⟨j, hDir⟩ state) challenge
      return ⟨transcript.concat challenge, newState⟩) := by
  rw [Prover.processRound_def]
  apply bind_congr
  rintro ⟨transcript, state⟩
  dsimp only
  split <;> rename_i hDir'
  · rfl
  · exact absurd (hDir.symm.trans hDir') (by decide)

/-- **Left-round `processRound` compatibility (message branch).**  Working scratch lemma to inspect
the message-round goal shape. -/
theorem append_processRound_left_message (i : Fin m) (hDir₁ : pSpec₁.dir i = .P_to_V)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc
        × (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc))
    (cur₁ : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (pSpec₁.Transcript i.castSucc × P₁.PrvState i.castSucc))
    (hcur : HEq curA (liftM cur₁ :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
    HEq ((P₁.append P₂).processRound (i.castLE (by omega)) curA)
      (liftM (P₁.processRound i cur₁) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .P_to_V := by
    rw [append_dir_castLE]; exact hDir₁
  rw [processRound_message (P₁.append P₂) (i.castLE (by omega)) hDir curA,
    processRound_message P₁ i hDir₁ cur₁]
  -- Push the outer `liftM` through the RHS `do`-block (keep binds explicit, no `map` rewrite).
  simp only [liftM_bind, liftM_pure]
  -- Outer bind over the (HEq) input results.
  refine bind_heq_congr
    (by rw [append_Transcript_castSucc i, append_PrvState_castSucc i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_castSucc i) (append_PrvState_castSucc i) hr
  dsimp only
  -- Collapse the double `liftM` on the RHS (composition of lifts oSpec → appended spec).
  have hcollapse : (liftM (liftM (P₁.sendMessage ⟨i, hDir₁⟩ s') :
        OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
      = liftM (P₁.sendMessage ⟨i, hDir₁⟩ s' : OracleComp oSpec _) := by
    rfl
  rw [hcollapse]
  -- Normalize the RHS continuation `liftM (pure _) = pure _`.
  simp only [liftM_pure]
  -- Bind over the (HEq) `sendMessage` computations, then `pure (concat, newState)`.
  apply bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    (β := (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ
      × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
    (β' := pSpec₁.Transcript i.succ × P₁.PrvState i.succ)
    (α := (pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩
      × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
    (α' := pSpec₁.Message ⟨i, hDir₁⟩ × P₁.PrvState i.succ)
    (by rw [append_Message_castLE i hDir hDir₁, append_PrvState_succ i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i])
  · -- `sendMessage` HEq (lifted): both sides are oSpec→S lifts (direct vs transitive, defeq) of
    -- HEq-equal `sendMessage` computations (`append_sendMessage_left` + `s ≍ s'`).
    have hαeq : ((pSpec₁ ++ₚ pSpec₂).Message ⟨i.castLE (by omega), hDir⟩
          × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
        = (pSpec₁.Message ⟨i, hDir₁⟩ × P₁.PrvState i.succ) := by
      rw [append_Message_castLE i hDir hDir₁, append_PrvState_succ i]
    have hbase : HEq ((P₁.append P₂).sendMessage ⟨i.castLE (by omega), hDir⟩ s)
        (P₁.sendMessage ⟨i, hDir₁⟩ s') :=
      (append_sendMessage_left i hDir hDir₁ s).trans
        (sendMessage_heq_congr rfl ((cast_heq _ _).trans hs))
    -- Lift the base `sendMessage` HEq (`hbase`) through the lift to `S`.
    --
    -- The goal's two `liftM`s both lift `OracleComp oSpec → S`, but via DIFFERENT `MonadLiftT`
    -- instances: the goal's RHS (`liftM_bind`-pushed `P₁.processRound` side) uses the *transitive*
    -- instance `instMonadLiftTOfMonadLift oSpec (oSpec + [pSpec₁.Challenge]ₒ) S`, whereas the
    -- appended-prover side and `liftM_heq_congr` use the *direct* instance
    -- `instMonadLiftTOfMonadLift oSpec oSpec S`.  These two `monadLift`s are EQUAL as functions
    -- (`liftComp_liftComp`: the transitive lift `liftComp (liftComp · mid) super` equals the direct
    -- `liftComp · super`, the single-query coherence being `rfl` for the canonical `+` instances),
    -- but they are NOT defeq at the `OracleComp` structure level.  We bridge them via
    -- `liftComp_liftComp` and then apply `liftM_heq_congr` on the (common) direct instance.
    -- The goal is `liftM (appended.sendMessage ..) ≍ liftM (P₁.sendMessage ..)`, where the LHS
    -- lifts `OracleComp oSpec → S` via the DIRECT instance and the RHS via the TRANSITIVE instance
    -- `oSpec → oSpec+[pSpec₁.Challenge]ₒ → S`.  Definitionally the transitive RHS unfolds to the
    -- nested `liftComp (liftComp (P₁.sendMessage ..) (oSpec+[pSpec₁.Challenge]ₒ)) S`; expose that via
    -- `show`, collapse it to the direct `liftComp (P₁.sendMessage ..) S` via `liftComp_liftComp`,
    -- and likewise expose the LHS as the direct `liftComp (appended.sendMessage ..) S`.
    show HEq (OracleComp.liftComp ((P₁.append P₂).sendMessage ⟨i.castLE (by omega), hDir⟩ s)
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
        (OracleComp.liftComp
          (OracleComp.liftComp (P₁.sendMessage ⟨i, hDir₁⟩ s') (oSpec + [pSpec₁.Challenge]ₒ))
          (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
    rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)
      (P₁.sendMessage ⟨i, hDir₁⟩ s')]
    -- Both sides are now `liftComp · (oSpec+[(pSpec₁++pSpec₂).Challenge]ₒ)` on the (HEq) base
    -- `sendMessage` computations; close via the query-level `liftComp` HEq congruence.
    exact liftComp_heq_congr (spec := oSpec)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq hbase
  · rintro ⟨msg, ns⟩ ⟨msg', ns'⟩ hmsg
    refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_
    obtain ⟨hm, hns⟩ :=
      prod_heq_split (append_Message_castLE i hDir hDir₁) (append_PrvState_succ i) hmsg
    refine prodMk_heq (append_Transcript_succ i) (append_PrvState_succ i) ?_ hns
    -- `Transcript.concat msg t ≍ Transcript.concat msg' t'`
    exact concat_heq i ht hm

/-- **Left-round `processRound` compatibility (challenge branch).**  The `V_to_P` analogue of
`append_processRound_left_message`: at a left challenge round `i < m`, the appended prover's
`processRound` (heterogeneously) equals the `liftM` of `P₁`'s, assuming the run-up-to inputs are
HEq.  Mirrors the message branch, with `getChallenge` (`append_getChallenge_left`) and
`receiveChallenge` (`append_receiveChallenge_left`) in place of `sendMessage`, plus the extra
function-application of the `receiveChallenge` result to the sampled challenge. -/
theorem append_processRound_left_challenge (i : Fin m) (hDir₁ : pSpec₁.dir i = .V_to_P)
    (curA : OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      ((pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).castSucc
        × (P₁.append P₂).PrvState (i.castLE (by omega)).castSucc))
    (cur₁ : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (pSpec₁.Transcript i.castSucc × P₁.PrvState i.castSucc))
    (hcur : HEq curA (liftM cur₁ :
      OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)) :
    HEq ((P₁.append P₂).processRound (i.castLE (by omega)) curA)
      (liftM (P₁.processRound i cur₁) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  have hDir : (pSpec₁ ++ₚ pSpec₂).dir (i.castLE (by omega)) = .V_to_P := by
    rw [append_dir_castLE]; exact hDir₁
  rw [processRound_challenge' (P₁.append P₂) (i.castLE (by omega)) hDir curA,
    processRound_challenge' P₁ i hDir₁ cur₁]
  simp only [liftM_bind, liftM_pure]
  refine bind_heq_congr
    (by rw [append_Transcript_castSucc i, append_PrvState_castSucc i])
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) hcur ?_
  rintro ⟨t, s⟩ ⟨t', s'⟩ hr
  obtain ⟨ht, hs⟩ := prod_heq_split (append_Transcript_castSucc i) (append_PrvState_castSucc i) hr
  dsimp only
  -- Collapse the RHS double-lifts (oSpec'-level transitive ⇒ direct) of the challenge-oracle
  -- computations.  Here both `getChallenge` and `receiveChallenge` already live in the appended
  -- challenge oracle on the RHS after the inner `liftM`; the outer `liftM` to the full spec is the
  -- challenge `SubSpec` lift, common to both sides.
  -- Challenge value type equality.
  have hChalEq : (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
      = pSpec₁.Challenge ⟨i, hDir₁⟩ := by
    show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (i.castLE (by omega)) = pSpec₁.«Type» i
    rw [Fin.vappend_eq_append,
      show (i.castLE (show m ≤ m + n by omega)) = Fin.castAdd n i from by ext; simp, Fin.append_left]
  -- Bind over the (HEq) `getChallenge` computations.
  refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
    hChalEq
    (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_ ?_
  · -- `getChallenge` HEq, lifted to the full spec.  Both sides lift the appended challenge oracle
    -- `[(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ` into the full spec via the same `+`-right `SubSpec`; the
    -- underlying `getChallenge` HEq is `append_getChallenge_left`.
    exact liftM_heq_congr (spec := [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hChalEq
      (append_getChallenge_left i hDir hDir₁)
  · -- continuation: bind over `receiveChallenge`, then `pure (concat, f challenge)`.
    rintro chalA chal₁ hchal
    -- Collapse the RHS double-lift of `receiveChallenge` (transitive oSpec→S ⇒ direct).
    have hcollapse : (liftM (liftM (P₁.receiveChallenge ⟨i, hDir₁⟩ s') :
          OracleComp (oSpec + [pSpec₁.Challenge]ₒ) _) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _)
        = liftM (P₁.receiveChallenge ⟨i, hDir₁⟩ s' : OracleComp oSpec _) := by rfl
    rw [hcollapse]
    -- `receiveChallenge` returns `Challenge → State`; the bind result `f` is applied to the
    -- challenge.  HEq of the receiveChallenge computations:
    have hrecvBase : HEq ((P₁.append P₂).receiveChallenge ⟨i.castLE (by omega), hDir⟩ s)
        (P₁.receiveChallenge ⟨i, hDir₁⟩ s') :=
      (append_receiveChallenge_left i hDir hDir₁ s).trans
        (receiveChallenge_heq_congr rfl ((cast_heq _ _).trans hs))
    refine bind_heq_congr (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
      (α := (pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
        → (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
      (α' := pSpec₁.Challenge ⟨i, hDir₁⟩ → P₁.PrvState i.succ)
      (β := (pSpec₁ ++ₚ pSpec₂).Transcript (i.castLE (by omega)).succ
        × (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
      (β' := pSpec₁.Transcript i.succ × P₁.PrvState i.succ)
      (by rw [hChalEq, append_PrvState_succ i])
      (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_ ?_
    · -- lifted `receiveChallenge` HEq, transitive RHS ⇒ direct via `liftComp_liftComp`.
      have hαeq : ((pSpec₁ ++ₚ pSpec₂).Challenge ⟨i.castLE (by omega), hDir⟩
            → (P₁.append P₂).PrvState (i.castLE (by omega)).succ)
          = (pSpec₁.Challenge ⟨i, hDir₁⟩ → P₁.PrvState i.succ) := by
        rw [hChalEq, append_PrvState_succ i]
      show HEq (OracleComp.liftComp ((P₁.append P₂).receiveChallenge ⟨i.castLE (by omega), hDir⟩ s)
              (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
          (OracleComp.liftComp
            (OracleComp.liftComp (P₁.receiveChallenge ⟨i, hDir₁⟩ s') (oSpec + [pSpec₁.Challenge]ₒ))
            (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ))
      rw [liftComp_liftComp (spec := oSpec) (midSpec := oSpec + [pSpec₁.Challenge]ₒ)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) (fun t => rfl)
        (P₁.receiveChallenge ⟨i, hDir₁⟩ s')]
      exact liftComp_heq_congr (spec := oSpec)
        (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) hαeq hrecvBase
    · -- `pure (concat chal t, f chal)`: concat + function-application HEq.
      rintro fA f₁ hf
      refine pure_heq_pure (spec := oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ)
        (by rw [append_Transcript_succ i, append_PrvState_succ i]) ?_
      refine prodMk_heq (append_Transcript_succ i) (append_PrvState_succ i) ?_ ?_
      · -- `concat chalA t ≍ concat chal₁ t'`
        exact concat_heq i ht hchal
      · -- `fA chalA ≍ f₁ chal₁`: application of HEq (non-dependent) functions to HEq arguments.
        refine heq_app hChalEq ?_ hf hchal
        -- codomain families are the constant `fun _ => PrvState succ`; HEq via the state equality.
        rw [hChalEq, append_PrvState_succ i]

/-- **The corrected well-founded `append_runToRound_left`.**  Running the appended prover up to a
left-half round `j ≤ m` (embedded as `j.castLE` into `Fin (m + n + 1)`) is heterogeneously equal to
the `liftM` (along the left challenge `SubSpec`) of running `P₁` up to round `j`. -/
theorem append_runToRound_left (j : Fin (m + 1)) :
    HEq ((P₁.append P₂).runToRound (j.castLE (by omega)) stmt wit)
      (liftM (P₁.runToRound j stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
  induction j using Fin.induction with
  | zero =>
    rw [show ((0 : Fin (m + 1)).castLE (by omega) : Fin (m + n + 1)) = 0 from by ext; simp]
    rw [Prover.runToRound_zero_of_prover_first, Prover.runToRound_zero_of_prover_first]
    rw [liftM_pure]
    have hT : Transcript 0 (pSpec₁ ++ₚ pSpec₂) = Transcript 0 pSpec₁ := by
      unfold ProtocolSpec.Transcript ProtocolSpec.FullTranscript
      apply pi_congr; intro i; exact absurd i.isLt (by simp)
    have hS : (P₁.append P₂).PrvState 0 = P₁.PrvState 0 := append_PrvState_castLE 0
    apply pure_heq_pure
    · rw [hT, hS]
    · apply prodMk_heq
      · exact hT
      · exact hS
      · exact Subsingleton.helim hT _ _
      · exact append_input_heq
  | succ i ih =>
    -- Express the left-embedded successor index as a successor in `Fin (m + n)`.
    have hidx : ((i.succ).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
        = (i.castLE (show m ≤ m + n by omega)).succ := by ext; simp
    rw [hidx, Prover.runToRound_succ]
    rw [Prover.runToRound_succ]
    -- Goal: `processRound (i.castLE) appended (runToRound (i.castLE).castSucc appended)
    --        ≍ liftM (processRound i P₁ (runToRound i.castSucc P₁))`.
    -- `ih` carries the run up to the seam-predecessor round: `runToRound (i.castSucc.castLE) appended
    --   ≍ liftM (runToRound i.castSucc P₁)`.  Normalize its index to `(i.castLE).castSucc`.
    have hcur : HEq ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (liftM (P₁.runToRound i.castSucc stmt wit) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) := by
      have hcastSucc : (i.castSucc.castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
          = (i.castLE (show m ≤ m + n by omega)).castSucc := by ext; simp
      rw [← hcastSucc]; exact ih
    -- Case-split on the direction of the left round `i`.
    cases hd : pSpec₁.dir i with
    | V_to_P => ?_
    | P_to_V => ?_
    · -- `V_to_P` (challenge round): close via the proven challenge-branch lemma.
      exact append_processRound_left_challenge i hd
        ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (P₁.runToRound i.castSucc stmt wit) hcur
    · -- `P_to_V` (message round): close directly via the proven message-branch lemma.
      exact append_processRound_left_message i hd
        ((P₁.append P₂).runToRound (i.castLE (by omega)).castSucc stmt wit)
        (P₁.runToRound i.castSucc stmt wit) hcur

/-- **Seam specialization of `append_runToRound_left`.**  Running the appended prover up to the
*seam* round `m` (the last round of `pSpec₁`, embedded as `(Fin.last m).castLE` into the appended
protocol) is heterogeneously equal to the `liftM` of running `P₁` to its last round — i.e. the full
honest run of `P₁`'s message phase.  This is the entry point for assembling `Prover.append_run`:
after the seam, the continuation runs `P₂` (rounds `m+1 .. m+n`) starting from `P₁.output`-fed
`P₂.input`. -/
theorem append_runToRound_seam :
    HEq ((P₁.append P₂).runToRound ((Fin.last m).castLE (by omega)) stmt wit)
      (liftM (P₁.runToRound (Fin.last m) stmt wit) :
        OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂).Challenge]ₒ) _) :=
  append_runToRound_left (Fin.last m)

/-! ### Right-block run characterization support (in progress)

The right block mirrors the left, but the appended prover's right half is indexed through
`Fin.natAdd (m + 1)` (interior rounds `m+1 .. m+n`) and—crucially—the **seam round** `m`
(`Prover.append`'s `i = m` branch) is *not* a uniform right round: it threads `P₁.output >>= P₂.input`
before `P₂`'s round-`0` step.  We record here the proven right-half state transport; the remaining
right reductions and the seam-merge lemma are the documented obstruction of `append_run`. -/

/-- PrvState of the appended prover at a *right interior* round `m + 1 + k` (`k : Fin n`) equals
`P₂`'s state at round `k + 1`.  Mirror of `append_PrvState_castLE` via `Fin.append_right`/`Fin.tail`
(here `Fin.tail P₂.PrvState ∘ Fin.cast` reduces to `P₂.PrvState ∘ Fin.succ` on the right). -/
theorem append_PrvState_natAdd_succ (k : Fin n) :
    (P₁.append P₂).PrvState (Fin.natAdd (m + 1) k |>.cast (by omega)) = P₂.PrvState k.succ := by
  unfold Prover.append
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) (Fin.natAdd (m + 1) k |>.cast (by omega)) : Fin (m + 1 + n))
        = Fin.natAdd (m + 1) k from by ext; simp]
  rw [Fin.append_right]
  rfl

/-- The appended protocol's direction at a *right interior* round `Fin.natAdd m k` (`k : Fin n`)
matches `pSpec₂`'s direction at `k`.  Mirror of `append_dir_castLE` via `Fin.append_right`. -/
theorem append_dir_natAdd (k : Fin n) :
    (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = pSpec₂.dir k := by
  show Fin.vappend pSpec₁.dir pSpec₂.dir (Fin.natAdd m k) = pSpec₂.dir k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-- The appended-protocol message type at a right interior round equals `pSpec₂`'s. -/
theorem append_Message_natAdd (k : Fin n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V) (hDir₂ : pSpec₂.dir k = .P_to_V) :
    (pSpec₁ ++ₚ pSpec₂).Message ⟨Fin.natAdd m k, hDir⟩ = pSpec₂.Message ⟨k, hDir₂⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.natAdd m k) = pSpec₂.«Type» k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-- The appended-protocol challenge type at a right interior round equals `pSpec₂`'s. -/
theorem append_Challenge_natAdd (k : Fin n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P) (hDir₂ : pSpec₂.dir k = .V_to_P) :
    (pSpec₁ ++ₚ pSpec₂).Challenge ⟨Fin.natAdd m k, hDir⟩ = pSpec₂.Challenge ⟨k, hDir₂⟩ := by
  show Fin.vappend pSpec₁.«Type» pSpec₂.«Type» (Fin.natAdd m k) = pSpec₂.«Type» k
  rw [Fin.vappend_eq_append, Fin.append_right]

/-! ### Seam-round reductions

The seam round `m` is the genuinely-new monadic-interleaving step of `Prover.append` (the `i = m`
branch): it threads `P₁.output state >>= P₂.input` before `P₂`'s round-`0` step.  We characterize the
two seam shapes (`sendMessage`/`receiveChallenge`) heterogeneously in terms of `P₁.output` /
`P₂.input` / `P₂`'s round-0 step.  These feed the seam-round `processRound` in the right-block run. -/

/-- State-type equality: the appended prover's state at the seam-round `castSucc` index `m`
(the state going INTO the seam round) equals `P₁`'s last state. -/
theorem append_PrvState_seam_castSucc (hn : 0 < n) :
    (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc = P₁.PrvState (Fin.last m) := by
  have := append_PrvState_castLE (P₁ := P₁) (P₂ := P₂) (Fin.last m)
  rw [show ((Fin.last m).castLE (show m + 1 ≤ m + n + 1 by omega) : Fin (m + n + 1))
        = (⟨m, by omega⟩ : Fin (m + n)).castSucc from by ext; simp] at this
  exact this

/-- **Seam-round `sendMessage` reduction.**  At the seam round `m` (the `i = m` branch of
`Prover.append.sendMessage`), the appended prover's `sendMessage` is heterogeneously equal to
`P₁.output state >>= fun ctx => P₂.sendMessage ⟨0,_⟩ (P₂.input ctx)`. -/
theorem append_sendMessage_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, by omega⟩ = .P_to_V)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .P_to_V)
    (state : (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨⟨m, by omega⟩, hDir⟩ state)
      (do
        let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) state)
        P₂.sendMessage ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) : OracleComp oSpec _) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) < m := by simp
  rw [id_eq, dif_neg hnlt]
  have heqm : (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) = m := by simp
  rw [dif_pos heqm]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  -- Both sides are `P₁.output (·) >>= fun ctx => P₂.sendMessage ⟨0,_⟩ (P₂.input ctx)` over oSpec;
  -- the seam's internally-cast `state` and our `cast _ state` target the same `P₁.PrvState (last m)`.
  refine bind_heq_congr (α := Stmt₂ × Wit₂) (α' := Stmt₂ × Wit₂) rfl
    (by congr 1) ?_ ?_
  · apply heq_of_eq; congr 1
  · rintro c c' rfl; rfl

/-- **Seam-round `receiveChallenge` reduction.**  The `V_to_P` analogue of `append_sendMessage_seam`:
at the seam round `m`, the appended prover's `receiveChallenge` is heterogeneously equal to
`P₁.output state >>= fun ctx => P₂.receiveChallenge ⟨0,_⟩ (P₂.input ctx)`. -/
theorem append_receiveChallenge_seam (hn : 0 < n)
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir ⟨m, by omega⟩ = .V_to_P)
    (hDir₂ : pSpec₂.dir ⟨0, hn⟩ = .V_to_P)
    (state : (P₁.append P₂).PrvState (⟨m, by omega⟩ : Fin (m + n)).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨⟨m, by omega⟩, hDir⟩ state)
      (do
        let ctxIn₂ ← P₁.output (cast (append_PrvState_seam_castSucc hn) state)
        P₂.receiveChallenge ⟨⟨0, hn⟩, hDir₂⟩ (P₂.input ctxIn₂) : OracleComp oSpec _) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) < m := by simp
  rw [dif_neg hnlt]
  have heqm : (↑(⟨m, by omega⟩ : Fin (m + n)) : ℕ) = m := by simp
  rw [dif_pos heqm]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  refine bind_heq_congr (α := Stmt₂ × Wit₂) (α' := Stmt₂ × Wit₂) rfl
    (by congr 1) ?_ ?_
  · apply heq_of_eq; congr 1
  · rintro c c' rfl; rfl

/-! ### Right interior-round reductions

The right *interior* rounds `m+1 .. m+n-1` are the `i > m` branch of `Prover.append`: uniform `P₂`
rounds.  These mirror the left-block reductions (`append_sendMessage_left` etc.), now indexed through
`Fin.natAdd m k` (`k : Fin n`, `k > 0`); the appended step reduces heterogeneously to `P₂`'s step at
round `k`, with the state transported by `append_PrvState_natAdd_castSucc`. -/

/-- State-type equality: the appended prover's state at the interior right round `Fin.natAdd m k`'s
`castSucc` (state going INTO interior round `k`, where `k > 0`) equals `P₂`'s state at `k`. -/
theorem append_PrvState_natAdd_castSucc (k : Fin n) (hk : 0 < (k : ℕ)) :
    (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc = P₂.PrvState k.castSucc := by
  have hpred : (⟨(k : ℕ) - 1, by omega⟩ : Fin n).succ = k.castSucc := by ext; simp; omega
  have := append_PrvState_natAdd_succ (P₁ := P₁) (P₂ := P₂) ⟨(k : ℕ) - 1, by omega⟩
  rw [hpred] at this
  rw [show ((Fin.natAdd m k).castSucc : Fin (m + n + 1))
        = (Fin.natAdd (m + 1) (⟨(k : ℕ) - 1, by omega⟩ : Fin n)).cast (by omega) from by
        ext; simp; omega]
  exact this

/-- State-type equality at the interior right round `succ` index (state AFTER interior round `k`,
`k > 0`).  Equals `P₂.PrvState k.succ`. -/
theorem append_PrvState_natAdd_interior_succ (k : Fin n) (hk : 0 < (k : ℕ)) :
    (P₁.append P₂).PrvState (Fin.natAdd m k).succ = P₂.PrvState k.succ := by
  have := append_PrvState_natAdd_succ (P₁ := P₁) (P₂ := P₂) k
  rw [show ((Fin.natAdd m k).succ : Fin (m + n + 1))
        = (Fin.natAdd (m + 1) k).cast (by omega) from by ext; simp; omega]
  exact this

/-- **Right interior-round `sendMessage` reduction.**  At an interior right round `Fin.natAdd m k`
(`k : Fin n`, `k > 0`, the `i > m` branch of `Prover.append.sendMessage`), the appended prover's
`sendMessage` is heterogeneously equal to `P₂`'s `sendMessage` at round `k`. -/
theorem append_sendMessage_natAdd (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .P_to_V)
    (hDir₂ : pSpec₂.dir k = .P_to_V)
    (state : (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc) :
    HEq ((P₁.append P₂).sendMessage ⟨Fin.natAdd m k, hDir⟩ state)
      (P₂.sendMessage ⟨k, hDir₂⟩ (cast (append_PrvState_natAdd_castSucc k hk) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(Fin.natAdd m k) : ℕ) < m := by simp
  rw [id_eq, dif_neg hnlt]
  have hne : (↑(Fin.natAdd m k) : ℕ) ≠ m := by simp; omega
  rw [dif_neg hne]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  have hkeq : (⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ : Fin n) = k := by ext; simp
  have hdir₂' : pSpec₂.dir ⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ = .P_to_V := by
    rw [hkeq]; exact hDir₂
  have hidx : (⟨⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩, hdir₂'⟩ : pSpec₂.MessageIdx)
      = ⟨k, hDir₂⟩ := by ext; simp
  refine sendMessage_heq_congr hidx ?_
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)

/-- **Right interior-round `receiveChallenge` reduction.**  Mirror of `append_sendMessage_natAdd`
for the `V_to_P` direction. -/
theorem append_receiveChallenge_natAdd (k : Fin n) (hk : 0 < (k : ℕ))
    (hDir : (pSpec₁ ++ₚ pSpec₂).dir (Fin.natAdd m k) = .V_to_P)
    (hDir₂ : pSpec₂.dir k = .V_to_P)
    (state : (P₁.append P₂).PrvState (Fin.natAdd m k).castSucc) :
    HEq ((P₁.append P₂).receiveChallenge ⟨Fin.natAdd m k, hDir⟩ state)
      (P₂.receiveChallenge ⟨k, hDir₂⟩ (cast (append_PrvState_natAdd_castSucc k hk) state)) := by
  unfold Prover.append
  dsimp only [Fin.vappend_eq_append]
  have hnlt : ¬ (↑(Fin.natAdd m k) : ℕ) < m := by simp
  rw [dif_neg hnlt]
  have hne : (↑(Fin.natAdd m k) : ℕ) ≠ m := by simp; omega
  rw [dif_neg hne]
  simp only [eq_mpr_eq_cast, eq_mp_eq_cast]
  apply HEq.trans (cast_heq _ _)
  have hkeq : (⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ : Fin n) = k := by ext; simp
  have hdir₂' : pSpec₂.dir ⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩ = .V_to_P := by
    rw [hkeq]; exact hDir₂
  have hidx : (⟨⟨(↑(Fin.natAdd m k) : ℕ) - m, by simp⟩, hdir₂'⟩ : pSpec₂.ChallengeIdx)
      = ⟨k, hDir₂⟩ := by ext; simp
  refine receiveChallenge_heq_congr hidx ?_
  exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)

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
  -- **WIP — left block DONE; ALL per-round seam+interior reductions now PROVEN; run-assembly
  -- (transcript-prefix family + right-block run induction + output) remains.**
  --
  -- Strategy: expose `run` as `runToRound (Fin.last (m+n))` ≫ `output` (`run_eq_runToRound_last`),
  -- then factor the full run at the seam `k = ⟨m,_⟩` via the keystone
  -- `runToRound_eq_bind_continueFromTo`:
  --   (P₁.append P₂).runToRound (last (m+n)) stmt wit
  --     = (P₁.append P₂).runToRound ⟨m,_⟩ stmt wit
  --         >>= continueFromTo (P₁.append P₂) stmt wit ⟨m,_⟩ (last (m+n)).
  -- The first factor = `append_runToRound_seam` (PROVEN): ≍ `liftM (P₁.runToRound (last m))`.
  --
  -- PROVEN per-round handles (all #print-axioms clean), ready to feed the run induction:
  --   • SEAM round `m` (`i = m` branch): `append_sendMessage_seam` / `append_receiveChallenge_seam`
  --     reduce the seam step to `P₁.output (cast _ state) >>= fun ctx => P₂.{send,recv} ⟨0,_⟩
  --     (P₂.input ctx)` — exactly the `liftM (P₁.run) >>= fun ⟨_,s₂,w₂⟩ => liftM (P₂.run s₂ w₂)`
  --     boundary (state transport `append_PrvState_seam_castSucc`, dir `append_dir_natAdd ⟨0,_⟩`).
  --   • RIGHT interior rounds `m+1..m+n-1` (`i > m` branch): `append_sendMessage_natAdd` /
  --     `append_receiveChallenge_natAdd` reduce to `P₂`'s step at round `k`; state transports
  --     `append_PrvState_natAdd_castSucc` / `_interior_succ`; types `append_{dir,Message,Challenge}_natAdd`.
  --
  -- (T) Transcript-PREFIX family — NOW DISCHARGED (committed infrastructure):
  --   The prefix/snoc commutation `Transcript.concat msg (transcript₁ ++ₜ tr₂)
  --   ≍ transcript₁ ++ₜ (Transcript.concat msg tr₂)` is proven as
  --   `ProtocolSpec.FullTranscript.concat_append_right` (SeqCompose.lean), itself the
  --   `FullTranscript`-level instance of `Fin.happend_hconcat_eq` (the keystone prefix/snoc
  --   commutation for `Fin.happend`, with helpers `Fin.hconcat_heq` / `Fin.happend_heq_right`, in
  --   Data/Fin/Tuple/Lemmas.lean).  The seam boundary `transcript₁ ++ₜ (default : Transcript 0)
  --   ≍ transcript₁` is `Fin.happend_empty` (`++ₜ` on an empty right block is the identity, `rfl`),
  --   and the partial-transcript seam state `(pSpec₁++pSpec₂).Transcript ⟨m,_⟩ ≍ transcript₁` is the
  --   proven `append_Transcript_castLE` (`Fin.last m`).  All #print-axioms clean.
  --
  -- REMAINING OBSTRUCTION (the genuinely new content, blocking assembly):
  --   (R) Right-block run induction.  By `Fin.induction` on `k : Fin (n+1)`, with the prefix `(T)`
  --       threaded: `continueFromTo (P₁++P₂) stmt wit ⟨m,_⟩ (natAdd m k) rSeam`
  --       ≍ (do `⟨tr₂,s₂'⟩ ← P₂.runToRound k (P₂.input (←P₁.output …)) …; pure (transcript₁ ++ₜ tr₂, …)`)
  --       — base `k=0` is `continueFromTo_self` (+ the seam-boundary (T) facts above); succ steps peel
  --       via `continueFromTo_succ_of_ne` + `processRound_{message,challenge}` and the PROVEN per-round
  --       seam/interior reductions above, now closing the transcript-prefix conjunct with (T).  This is
  --       the right-block analogue of `append_processRound_left_*` + `append_runToRound_left`, with the
  --       additional `transcript₁` prefix carried by `concat_append_right` at every `concat` step.
  --   (O) `output` assembly: combine via `++ₜ` (`append_fst`/`append_snd`) + `P₂.output` tail
  --       (`output` branch of `Prover.append`, incl. `n = 0` degenerate seam where the right block is
  --       empty and `P₁.output >>= P₂.input >>= P₂.output` collapses).
  --
  -- All round-local reductions AND the transcript-prefix family (T) are discharged; the residue is the
  -- right-block run induction (R) wiring the per-round reductions + (T) prefix commutation, plus the
  -- output assembly (O).  A `HEq` engineering task on the now-complete reduction+transcript layer,
  -- with NO remaining monadic-interleaving or transcript-prefix gap.
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
