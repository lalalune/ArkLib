/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.Cast
import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Casting for structures of oracle reductions

  We define custom dependent casts (registered as `DCast` instances) for the following structures:
  - `(Oracle)Prover`
  - `(Oracle)Verifier`
  - `(Oracle)Reduction`

  Note that casting for `ProtocolSpec`s and related structures are defined in
  `OracleReduction/ProtocolSpec/Cast.lean`.

  We also show that casting preserves execution (up to casting of the transcripts) and thus security
  properties.
-/

open OracleComp

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n₁ n₂ : ℕ} {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂}
  (hn : n₁ = n₂) (hSpec : pSpec₁.cast hn = pSpec₂)

open ProtocolSpec

namespace Prover

/-- Casting the prover of a non-oracle reduction across an equality of `ProtocolSpec`s. -/
protected def cast (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  PrvState := P.PrvState ∘ Fin.cast (congrArg (· + 1) hn.symm)
  input := P.input
  sendMessage := fun i st => do
    let ⟨msg, newSt⟩ ← P.sendMessage (i.cast hn.symm (cast_symm hSpec)) st
    return ⟨(Message.cast_idx_symm hSpec) ▸ msg, newSt⟩
  receiveChallenge := fun i st => do
    let f ← P.receiveChallenge (i.cast hn.symm (cast_symm hSpec)) st
    return fun chal => f (Challenge.cast_idx hSpec ▸ chal)
  output := P.output ∘ (fun st => _root_.cast (by simp) st)

@[simp]
theorem cast_id :
    Prover.cast rfl rfl = (id : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁ → _) := by
  funext; simp [Prover.cast]; ext <;> simp
  · funext _ _; simp [MessageIdx.cast, bind_pure]
  · funext _ _; simp [ChallengeIdx.cast]
  · rfl

instance instDCast₂ : DCast₂ Nat ProtocolSpec
    (fun _ pSpec => Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  dcast₂ := Prover.cast
  dcast₂_id := Prover.cast_id

end Prover

namespace OracleProver

/-- Casting the oracle prover of a non-oracle reduction across an equality of `ProtocolSpec`s.

Internally invokes the `Prover.cast` function. -/
protected def cast (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₂ :=
  Prover.cast hn hSpec P

@[simp]
theorem cast_id :
    OracleProver.cast rfl rfl =
      (id : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁ → _) := by
  exact Prover.cast_id

instance instDCast₂OracleProver : DCast₂ Nat ProtocolSpec
    (fun _ pSpec => OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) where
  dcast₂ := OracleProver.cast
  dcast₂_id := OracleProver.cast_id

end OracleProver

namespace Verifier

/-- Casting the verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

This boils down to casting the (full) transcript. -/
protected def cast (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
    Verifier oSpec StmtIn StmtOut pSpec₂ where
  verify := fun stmt transcript => V.verify stmt (dcast₂ hn.symm (dcast_symm hn hSpec) transcript)

@[simp]
theorem cast_id : Verifier.cast rfl rfl = (id : Verifier oSpec StmtIn StmtOut pSpec₁ → _) := by
  ext; simp [Verifier.cast]

instance instDCast₂Verifier :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier oSpec StmtIn StmtOut pSpec) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp [Verifier.cast]

theorem cast_eq_dcast₂ {V : Verifier oSpec StmtIn StmtOut pSpec₁} :
    V.cast hn hSpec = dcast₂ hn hSpec V := rfl

end Verifier

namespace OracleVerifier

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]

/-- Transport a query to the message oracle `[pSpec₁.Message]ₒ` into an `OracleComp` over the
casted spec, given that the underlying oracle interface `O₁` agrees with the casted message
interface `Oₘ₂ i₂` up to the type equality `hMsg`. This is the per-query body used to assemble
`castMessageImpl`. -/
private def castMessageQuery
    {T₁ : Type} (O₁ : OracleInterface T₁)
    (i₂ : pSpec₂.MessageIdx) (hMsg : pSpec₂.Message i₂ = T₁)
    (hO : O₁ = _root_.cast (congrArg OracleInterface hMsg) (Oₘ₂ i₂))
    (q : O₁.Query) :
    OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ)) (O₁.Response q) := by
  subst hMsg
  subst hO
  -- now `O₁ = Oₘ₂ i₂`, so the query to the message oracle at `i₂` has the right response type
  exact query (spec := oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ)) (Sum.inr (Sum.inr ⟨i₂, q⟩))

/-- The translation of a query to the prover messages `[pSpec₁.Message]ₒ` into a query to the
casted prover messages `[pSpec₂.Message]ₒ`. Given a query `⟨i, q⟩` to message `i`, we cast the
message index to `pSpec₂` via `MessageIdx.cast`, transport the query along the equality of oracle
interfaces `hOₘ`, query the corresponding `pSpec₂` message, and transport the response back. -/
def castMessageImpl
    (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec))) :
    QueryImpl [pSpec₁.Message]ₒ (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ))) :=
  fun q =>
    castMessageQuery (oSpec := oSpec) (OStmtIn := OStmtIn) (Oₘ₂ := Oₘ₂)
      (Oₘ₁ q.1) (q.1.cast hn hSpec) (Message.cast_idx hSpec)
      (by rw [hOₘ q.1, dcast_eq_root_cast]) q.2

open Function in
/-- Casting the oracle verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

The oracle queries that the underlying verifier makes to the prover messages of `pSpec₁` are
translated, via `castMessageImpl`, into queries to the prover messages of `pSpec₂`. -/
protected def cast
    (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₂ where
  verify := fun stmt challenges =>
    let impl : QueryImpl (oSpec + ([OStmtIn]ₒ + [pSpec₁.Message]ₒ))
      (OracleComp (oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ))) :=
      fun q => match q with
        | Sum.inl t =>
            query (spec := oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ)) (Sum.inl t)
        | Sum.inr (Sum.inl t) =>
            query (spec := oSpec + ([OStmtIn]ₒ + [pSpec₂.Message]ₒ)) (Sum.inr (Sum.inl t))
        | Sum.inr (Sum.inr t) => castMessageImpl hn hSpec hOₘ t
    simulateQ impl (V.verify stmt (dcast₂ hn.symm (dcast_symm hn hSpec) challenges))
  embed := V.embed.trans
    (Embedding.sumMap
      (Equiv.refl _).toEmbedding
      ⟨MessageIdx.cast hn hSpec, MessageIdx.cast_injective hn hSpec⟩)
  hEq := fun i => by
    simp [Embedding.sumMap, Equiv.refl]
    have := V.hEq i
    rw [this]
    split
    next a b h' => simp [h']
    next a b h' => simp [h']; exact (Message.cast_idx hSpec).symm

variable (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))

-- @[simp]
-- theorem cast_id :
--     OracleVerifier.cast rfl rfl (fun i => rfl) =
--       (id : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁ → _) := by
--   placeholder

-- Need to cast oracle interface as well
-- instance instDCast₂OracleVerifier : DCast₃ Nat ProtocolSpec
--     (fun _ pSpec => OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) where
--   dcast₂ := OracleVerifier.cast
--   dcast₂_id := OracleVerifier.cast_id

@[simp]
theorem cast_toVerifier (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁) :
    (OracleVerifier.cast hn hSpec hOₘ V).toVerifier = Verifier.cast hn hSpec V.toVerifier := by
  subst hn
  subst hSpec
  -- The casted message oracle interface coincides with the original (the `rfl`-cast is the
  -- identity on indices and the `dcast` is trivial), so we may identify the two instances.
  have hOₘ' : Oₘ₁ = Oₘ₂ := by
    funext i
    have := hOₘ i
    simp only [MessageIdx.cast_id, id_eq, dcast_eq] at this
    exact this
  subst hOₘ'
  simp only [OracleVerifier.cast, OracleVerifier.toVerifier, Verifier.cast,
    dcast_eq, dcast₂_eq, FullTranscript.cast_eq_dcast₂]
  congr 1
  funext stmt transcript
  -- Split the produced-statement computation from the output-oracle-statement assembly.
  congr 1
  · -- The inner message routing re-emits every query unchanged, hence is the identity query
    -- implementation; the inner `simulateQ` therefore disappears, leaving identical computations.
    -- Isolate the inner `simulateQ ROUTING X`, rewrite the target `X` as `simulateQ id' X`, and
    -- match the implementations per query.
    congr 1
    refine Eq.trans ?_ (simulateQ_id' _)
    refine congrFun (congrArg (fun s => simulateQ s) ?_) _
    funext q
    rcases q with t | t | ⟨i, q⟩
    · rfl
    · rfl
    · simp only [castMessageImpl, castMessageQuery, MessageIdx.cast_id, id_eq]; rfl
  · -- The output-oracle-statement assembly: the embed through `id.sumMap id` is `V.embed` itself,
    -- so both continuations select the same oracle statement.  We case on `V.embed i`; in each
    -- branch the `id`-sumMap leaves the chosen index unchanged.
    funext stmtOut
    refine congrArg pure (Prod.ext rfl (funext fun i => ?_))
    -- Both dependent matches select the same branch: the `(refl).sumMap id` embed and the bare
    -- `V.embed` agree, and the payload casts are definitionally equal.  We eliminate on the shared
    -- typing witness `V.hEq i` together with `V.embed i` so the split is type-correct.
    simp only [Function.Embedding.trans_apply, Function.Embedding.coe_sumMap,
      Equiv.coe_toEmbedding, Equiv.coe_refl, Function.Embedding.coeFn_mk, MessageIdx.cast_id]
    split <;> rename_i j heq <;> split <;> rename_i j' heq' <;>
      rw [heq'] at heq <;>
      simp_all only [Sum.map_inl, Sum.map_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, id_eq] <;>
      subst_vars <;>
      -- The two payloads are transports of the same value along proof-irrelevant equalities (and
      -- the `rfl`-cast transcript), hence equal up to `HEq`.  Rewrite each `▸` as a `cast` and
      -- strip it via `cast_heq`.
      (apply eq_of_heq
       simp only [eqRec_eq_cast]
       refine (cast_heq _ _).trans ((cast_heq _ _).trans (HEq.symm ?_))
       exact (cast_heq _ _).trans ((cast_heq _ _).trans HEq.rfl))

end OracleVerifier

namespace Reduction

/-- Casting the reduction of a non-oracle reduction across an equality of `ProtocolSpec`s, which
  casts the underlying prover and verifier. -/
protected def cast (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  prover := R.prover.cast hn hSpec
  verifier := R.verifier.cast hn hSpec

@[simp]
theorem cast_id :
    Reduction.cast rfl rfl = (id : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁ → _) := by
  funext x
  simp only [Reduction.cast, id]
  congr 1
  exact congr_fun (Prover.cast_id (pSpec₁ := pSpec₁)) _

instance instDCast₂Reduction :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  dcast₂ := Reduction.cast
  dcast₂_id := Reduction.cast_id

end Reduction

namespace OracleReduction

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))

/-- Casting the oracle reduction across an equality of `ProtocolSpec`s, which casts the underlying
  prover and verifier. -/
protected def cast (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₂ where
  prover := R.prover.cast hn hSpec
  verifier := R.verifier.cast hn hSpec hOₘ

-- @[simp]
-- theorem cast_id :
--     OracleReduction.cast rfl rfl (fun _ => rfl) =
--       (id : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁ → _) := by
--   ext : 2 <;> simp [OracleReduction.cast]

-- Need to cast oracle interface as well
-- instance instDCast₂OracleReduction :
--     DCast₂ Nat ProtocolSpec
--     (fun _ pSpec => OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
-- where
--   dcast₂ := OracleReduction.cast
--   dcast₂_id := OracleReduction.cast_id

@[simp]
theorem cast_toReduction
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    (R.cast hn hSpec hOₘ).toReduction = Reduction.cast hn hSpec R.toReduction := by
  simp [OracleReduction.cast, Reduction.cast, OracleReduction.toReduction, OracleProver.cast]

end OracleReduction

section Execution

-- TODO: show that the execution of everything is the same, modulo casting of transcripts
variable {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂} (hSpec : pSpec₁.cast hn = pSpec₂)

namespace Prover

-- TODO: need to cast [pSpec₁.Challenge]ₒ to [pSpec₂.Challenge]ₒ, where they have the default
-- instance `challengeOracleInterface`

theorem cast_processRound (j : Fin n₁)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁)
    (currentResult : OracleComp (oSpec + [pSpec₁.Challenge]ₒ)
      (Transcript j.castSucc pSpec₁ × P.PrvState j.castSucc)) :
    P.processRound j currentResult =
      cast (by subst_vars; simp [Prover.cast]; rfl)
        ((P.cast hn hSpec).processRound (Fin.cast hn j)
          (cast (by subst_vars; simp [Prover.cast]; rfl) currentResult)) := by
  subst hn; subst hSpec; congr 1; ext <;> simp [Prover.cast]
  · funext _ _; simp [MessageIdx.cast, bind_pure]
  · funext _ _; simp [ChallengeIdx.cast]
  · rfl

theorem cast_runToRound (j : Fin (n₁ + 1)) (stmt : StmtIn) (wit : WitIn)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    P.runToRound j stmt wit =
      cast (by subst_vars; simp [Prover.cast]; rfl)
        ((P.cast hn hSpec).runToRound (Fin.cast (congrArg (· + 1) hn) j) stmt wit) := by
  subst hn; subst hSpec; congr 1; ext <;> simp [Prover.cast]
  · funext _ _; simp [MessageIdx.cast, bind_pure]
  · funext _ _; simp [ChallengeIdx.cast]
  · rfl

theorem cast_run (stmt : StmtIn) (wit : WitIn)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    P.run stmt wit =
      cast (by subst_vars; simp; rfl) ((P.cast hn hSpec).run stmt wit) := by
  subst hn; subst hSpec; simp only [Prover.cast_id, id_eq]; rfl

end Prover

namespace Verifier

variable (V : Verifier oSpec StmtIn StmtOut pSpec₁)

/-- The casted verifier produces the same output as the original verifier. -/
@[simp]
theorem cast_run (stmt : StmtIn) (transcript : FullTranscript pSpec₁) :
    V.run stmt transcript = (V.cast hn hSpec).run stmt (transcript.cast hn hSpec) := by
  simp only [Verifier.run, Verifier.cast, FullTranscript.cast, dcast₂]
  unfold Transcript.cast
  simp

end Verifier

namespace Reduction

variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁)

theorem cast_run (stmt : StmtIn) (wit : WitIn) :
    R.run stmt wit =
      cast (by subst_vars; simp; rfl) ((R.cast hn hSpec).run stmt wit) := by
  subst hn; subst hSpec; simp only [Reduction.cast_id, id_eq]; rfl

end Reduction

end Execution

section Security

open NNReal

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [inst₁ : ∀ i, SampleableType (pSpec₁.Challenge i)]
  [inst₂ : ∀ i, SampleableType (pSpec₂.Challenge i)]
  (hChallenge : ∀ i, inst₁ i = dcast (by simp) (inst₂ (i.cast hn hSpec)))

section Protocol

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

namespace Reduction

variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁)

-- @[simp]
-- theorem cast_completeness (ε : ℝ≥0) (hComplete : R.completeness init impl relIn relOut ε) :
--     (R.cast hn hSpec).completeness init impl relIn relOut ε := by
--   placeholder

-- @[simp]
-- theorem cast_perfectCompleteness (hComplete : R.perfectCompleteness init impl relIn relOut) :
--     (R.cast hn hSpec).perfectCompleteness init impl relIn relOut :=
--   cast_completeness hn hSpec R 0 hComplete

end Reduction

namespace Verifier

variable (V : Verifier oSpec StmtIn StmtOut pSpec₁)

@[simp]
theorem cast_rbrKnowledgeSoundness (ε : pSpec₁.ChallengeIdx → ℝ≥0)
    (hRbrKs : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    (V.cast hn hSpec).rbrKnowledgeSoundness init impl relIn relOut
      (ε ∘ (ChallengeIdx.cast hn.symm (cast_symm hSpec))) := by
  sorry

end Verifier

end Protocol

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))
  {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
  {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}

namespace OracleReduction

variable (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁)

-- @[simp]
-- theorem cast_completeness (ε : ℝ≥0) (hComplete : R.completeness init impl relIn relOut ε) :
--     (R.cast hn hSpec hOₘ).completeness init impl relIn relOut ε := by
--   unfold completeness
--   rw [cast_toReduction]
--   exact Reduction.cast_completeness hn hSpec R.toReduction ε hComplete

-- @[simp]
-- theorem cast_perfectCompleteness (hComplete : R.perfectCompleteness init impl relIn relOut) :
--     (R.cast hn hSpec hOₘ).perfectCompleteness init impl relIn relOut :=
--   cast_completeness hn hSpec hOₘ R 0 hComplete

end OracleReduction

namespace OracleVerifier

variable (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁)

@[simp]
theorem cast_rbrKnowledgeSoundness (ε : pSpec₁.ChallengeIdx → ℝ≥0)
    (hRbrKs : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    (V.cast hn hSpec hOₘ).rbrKnowledgeSoundness init impl relIn relOut
      (ε ∘ (ChallengeIdx.cast hn.symm (cast_symm hSpec))) := by
  unfold rbrKnowledgeSoundness
  rw [cast_toVerifier]
  exact Verifier.cast_rbrKnowledgeSoundness hn hSpec V.toVerifier ε hRbrKs

end OracleVerifier

end OracleProtocol

end Security
