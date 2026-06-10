/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKnowledgeStateFunction
import ArkLib.OracleReduction.Composition.Sequential.AppendRightPartialProjections

/-!
# Unconditional round-by-round soundness append keystone (`append_rbrSoundness_keystone`)

This file discharges the **phase-2** half of the round-by-round soundness append keystone and
assembles the unconditional keystone `Verifier.append_rbrSoundness_keystone`: from the two
components' `rbrSoundness` (`h₁`/`h₂`) alone — plus the standard structural side conditions of the
deterministic-`V₁` message-seam, `Subsingleton σ` regime — it proves

  `(V₁.append V₂).rbrSoundness init impl lang₁ lang₃
      (Sum.elim rbrSoundnessError₁ rbrSoundnessError₂ ∘ ChallengeIdx.sumEquiv.symm)`,

which is exactly the conclusion of the named residual `Verifier.appendRbrSoundnessResidual`
(`Append.lean`). The discharge of that residual under these side conditions is
`append_rbrSoundness_residual_msg` below.

## Why the plain phase-2 is provable after all — the *doomed-escape* composite state function

The earlier keystone (`append_rbrSoundness_keystone_ofPhase2Residual`, `AppendRbrKeystone.lean`)
isolated phase 2 as the residual `appendRbrSoundnessPhase2Residual`, with the obstruction analysis:
against the *fixed* composite state function `StateFunction.append`, the phase-2 flip event carries
mass on the in-language seam event `verify stmtIn tr.fst ∈ lang₂`, which `h₂` (quantified only over
`stmtIn ∉ lang₂`) cannot control. That analysis is correct *for that state function* — but
`rbrSoundness` is **existential** in the state function, and the obstruction disappears for the
standard "doomed-escape" composite used in the round-by-round literature: on phase-2 rounds we take

  `verify stmt₁ tr.fst ∈ lang₂ ∨ S₂ (k - m) (verify stmt₁ tr.fst) tr.snd`

(i.e. the appended state is *also* true whenever the seam-crossing statement is in `lang₂`). Then:

* `toFun_empty` / `toFun_full` are inherited verbatim from the proven `StateFunction.append`
  (the escape disjunct is absent at round `0` and only *weakens* the negation at the last round);
* `toFun_next` keeps the escape clause stable across phase-2 prover messages (the phase-1
  truncation is unchanged, `transcript_concat_fst`), and at the crossing the falsity of
  `S₁ (last m)` *forces* `verify stmt₁ tr.fst ∉ lang₂`
  (`StateFunction.verify_notMem_lang_of_full_false`, the doomed-ness language-crossing brick);
* the phase-2 **flip event** now *implies* `verify stmtIn tr.fst ∉ lang₂` (from the `castSucc`
  negation), confining all flip mass to seam statements where `h₂` has content.

The probabilistic seam then follows the proven knowledge-side template
(`appendRbrKnowledgeSoundnessPhase2_subsingleton` / `appendRbrKnowledgePhase2SeamReconcile_proof`):
seam-factor the appended partial run (`phase2_body_heq`), split the simulated experiment across the
seam (`simulateQ_run'_bind_of_subsingleton`, the `Subsingleton σ` stateless regime), condition on
the realized phase-1 output `ctx`, case on `verify stmtIn ctx.1 ∈ lang₂` (in-language: the flip
event is pointwise *false*, probability `0`; out-of-language: apply `h₂` to the amnesiac
re-injection prover `Prover.sndAmnesiac`), and reconcile the inner game across the right
challenge-oracle seam (`evalDist_run'_challengeSeam_right`).
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

universe u v

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Stmt₂ Stmt₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  {lang₁ : Set Stmt₁} {lang₂ : Set Stmt₂} {lang₃ : Set Stmt₃}

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Dependent congruence for a (plain) state function's `toFun`, statement-aware.** The plain
analogue of `kToFun_congr_stmt`: equal round indices, equal statements, and heterogeneously-equal
transcripts give equal `toFun` propositions. Generic over the protocol, so it serves both the
`pSpec₁` (phase-1 reindex) and `pSpec₂` (phase-2 collapse) transports. -/
theorem sToFun_congr_stmt {N : ℕ} {p : ProtocolSpec N} {Stmt : Type}
    (f : (r : Fin (N + 1)) → Stmt → p.Transcript r → Prop)
    {r₁ r₂ : Fin (N + 1)} (hr : r₁ = r₂) {s₁ s₂ : Stmt} (hs : s₁ = s₂)
    {t₁ : p.Transcript r₁} {t₂ : p.Transcript r₂} (ht : HEq t₁ t₂) :
    f r₁ s₁ t₁ = f r₂ s₂ t₂ := by
  subst hr; subst hs; rw [eq_of_heq ht]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] in
/-- **Doomed-ness crosses the language** (public restatement of the brick used inside
`StateFunction.append`). For a *deterministic* first verifier `V₁ = pure ∘ verify` with a reachable
initial state, if its state function `S₁` is false on a full transcript then the intermediate
statement `verify stmt tr` lies *outside* `lang₂`. This converts the probabilistic `S₁.toFun_full`
into the pointwise membership fact that both the doomed-escape `toFun_next` crossing and the
phase-2 flip-event confinement consume. -/
theorem StateFunction.verify_notMem_lang_of_full_false
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


/-- **The doomed variant of a state function.** Same verifier, same languages; the state is
additionally *true* whenever the input statement already lies in the input language. All three
state-function laws are inherited from `S` with no transcript-dependent content: the escape
disjunct `stmt ∈ langIn` ignores the transcript entirely, `toFun_empty`'s backward direction is
`S.toFun_empty.mpr` on the second disjunct, and `toFun_full` only ever consumes the negation of the
second disjunct.

Dooming the *second* component before feeding it to the proven `StateFunction.append` yields the
standard round-by-round composition carrier: on phase-2 rounds the composite reads
`verify stmt₁ tr.fst ∈ lang₂ ∨ S₂ … (verify stmt₁ tr.fst) tr.snd`, so a phase-2 flip event records
`verify stmt₁ tr.fst ∉ lang₂` — confining the per-round bound to seam statements where `h₂` has
content — while avoiding entirely the dependent-cast surgery of re-deriving the appended
state-function laws. -/
def StateFunction.doom {N : ℕ} {p : ProtocolSpec N} {StmtIn StmtOut : Type}
    {langIn : Set StmtIn} {langOut : Set StmtOut} {V : Verifier oSpec StmtIn StmtOut p}
    (S : V.StateFunction init impl langIn langOut) :
    V.StateFunction init impl langIn langOut where
  toFun := fun k stmt tr => stmt ∈ langIn ∨ S.toFun k stmt tr
  toFun_empty := fun stmt =>
    ⟨Or.inl, fun h => h.elim (fun hmem => hmem) (fun hS => (S.toFun_empty stmt).mpr hS)⟩
  toFun_next := fun k hdir stmt tr hneg msg => by
    rintro (hmem | hS)
    · exact hneg (Or.inl hmem)
    · exact S.toFun_next k hdir stmt tr (fun hcs => hneg (Or.inr hcs)) msg hS
  toFun_full := fun stmt tr hneg =>
    S.toFun_full stmt tr (fun hS => hneg (Or.inr hS))

/-- The doomed state function evaluates as the escape disjunction (definitional unfolding,
exposed as a `simp`-friendly equation). -/
theorem StateFunction.doom_toFun {N : ℕ} {p : ProtocolSpec N} {StmtIn StmtOut : Type}
    {langIn : Set StmtIn} {langOut : Set StmtOut} {V : Verifier oSpec StmtIn StmtOut p}
    (S : V.StateFunction init impl langIn langOut)
    (k : Fin (N + 1)) (stmt : StmtIn) (tr : p.Transcript k) :
    (S.doom).toFun k stmt tr = (stmt ∈ langIn ∨ S.toFun k stmt tr) := rfl

/-- **The doomed-escape composite state function**: the proven `StateFunction.append` applied to
`S₁` and the doomed `S₂.doom`. On phase-1 rounds it is `S₁` on the truncation
(`StateFunction.append_toFun_le`); on phase-2 rounds it is
`verify stmt₁ tr.fst ∈ lang₂ ∨ S₂ (roundIdx - m) (verify stmt₁ tr.fst) tr.snd`
(`StateFunction.append_toFun_gt` + `StateFunction.doom_toFun`). -/
noncomputable def StateFunction.appendDoomed
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩)
    (hInit : ∃ s, s ∈ support init) :
    (V₁.append V₂).StateFunction init impl lang₁ lang₃ :=
  StateFunction.append init impl V₁ V₂ S₁ (S₂.doom) verify hVerify hInit

/-- **Phase-1 projection of the doomed composite** — inherited verbatim from
`StateFunction.append_toFun_le`. -/
theorem StateFunction.appendDoomed_toFun_le
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (transcript : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx) :
    (StateFunction.appendDoomed V₁ V₂ S₁ S₂ verify hVerify hInit).toFun roundIdx stmt₁ transcript
      = S₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using transcript.fst) :=
  StateFunction.append_toFun_le V₁ V₂ S₁ (S₂.doom) verify hVerify hInit h stmt₁ transcript

/-- **Phase-2 projection of the doomed composite**: the escape disjunction at the `verify`-fed
seam statement — `StateFunction.append_toFun_gt` composed with `StateFunction.doom_toFun`. -/
theorem StateFunction.appendDoomed_toFun_gt
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (S₁ : V₁.StateFunction init impl lang₁ lang₂) (S₂ : V₂.StateFunction init impl lang₂ lang₃)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init)
    {roundIdx : Fin (m + n + 1)} (h : ¬ roundIdx.val ≤ m) (stmt₁ : Stmt₁)
    (transcript : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx) :
    (StateFunction.appendDoomed V₁ V₂ S₁ S₂ verify hVerify hInit).toFun roundIdx stmt₁ transcript
      = (verify stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst) ∈ lang₂ ∨
          S₂.toFun ⟨roundIdx - m, by omega⟩
            (verify stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using transcript.fst))
            (by simpa [h] using transcript.snd)) :=
  StateFunction.append_toFun_gt V₁ V₂ S₁ (S₂.doom) verify hVerify hInit h stmt₁ transcript

end Verifier
