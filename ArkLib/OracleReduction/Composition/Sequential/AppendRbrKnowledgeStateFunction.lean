/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.OracleReduction.Composition.Sequential.AppendRbrKeystone

/-!
# The composite round-by-round *knowledge* state function — `Verifier.KnowledgeStateFunction.append`

This file constructs the witness-threaded analogue of the proven `Verifier.StateFunction.append`
(`Append.lean`): the composite round-by-round **knowledge** state function for the appended verifier
`V₁.append V₂`, built against the proven composite round-by-round extractor
`Extractor.RoundByRound.append E₁ E₂ verify`. With it the residual `kSF` of
`Verifier.append_rbrKnowledgeSoundness_keystone` (`AppendRbrKeystone.lean`) is discharged.

The `toFun` carrier mirrors `StateFunction.append`: on a phase-1 round (`roundIdx.val ≤ m`) it is the
inner knowledge state function `kSF₁` on the transcript's phase-1 truncation; on a phase-2 round it is
`kSF₂` on the `verify`-fed intermediate statement and the transcript's phase-2 tail. The only new
ingredient relative to `StateFunction.append` is the intermediate-witness leg: the appended extractor's
combined `WitMid` carrier `Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` projects to `WitMid₁`
on phase-1 rounds and `WitMid₂` on phase-2 rounds (`appendWitMid_le` / `appendWitMid_gt`), and the
state function casts the supplied combined witness into the appropriate leg before feeding it to
`kSF₁` / `kSF₂`.
-/

open OracleComp OracleSpec ProtocolSpec SubSpec
open scoped ENNReal NNReal

universe u v

namespace Verifier

variable {ι : Type} {oSpec : OracleSpec ι} {Stmt₁ Wit₁ Stmt₂ Wit₂ Stmt₃ Wit₃ : Type}
  {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}
  [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)]
  {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/-- **Phase-1 projection of the composite `WitMid` carrier.** For a round index `roundIdx.val ≤ m`,
the appended extractor's combined intermediate-witness type
`Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` evaluated at `roundIdx` is `WitMid₁`'s leg at the
re-indexed `⟨roundIdx, _⟩ : Fin (m+1)`. -/
theorem appendWitMid_le {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    {roundIdx : Fin (m+n+1)} (h : roundIdx.val ≤ m) :
    (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx
      = WitMid₁ ⟨roundIdx, by omega⟩ := by
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) roundIdx : Fin (m+1+n)) = Fin.castAdd n ⟨roundIdx, by omega⟩ from by
    ext; simp]
  rw [Fin.append_left]

/-- **Phase-2 projection of the composite `WitMid` carrier.** For a round index `¬ roundIdx.val ≤ m`,
the appended extractor's combined intermediate-witness type
`Fin.append WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast _` evaluated at `roundIdx` is `WitMid₂`'s leg at the
re-indexed `⟨roundIdx - m, _⟩ : Fin (n+1)`. -/
theorem appendWitMid_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    {roundIdx : Fin (m+n+1)} (h : ¬ roundIdx.val ≤ m) :
    (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) roundIdx
      = WitMid₂ ⟨roundIdx - m, by omega⟩ := by
  dsimp only [Function.comp_apply]
  rw [show (Fin.cast (by omega) roundIdx : Fin (m+1+n))
        = Fin.natAdd (m+1) ⟨roundIdx-(m+1), by omega⟩ from by ext; simp; omega]
  rw [Fin.append_right]; show Fin.tail WitMid₂ _ = _; unfold Fin.tail; congr 1
  ext; simp only [Fin.val_succ]; omega

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-1 projection of the composite `extractMid`.** For a round index `idx < m` (entirely in
phase 1), the appended extractor's `extractMid` defers — heterogeneously, up to the witness/transcript
type casts — to `E₁.extractMid ⟨idx,hi⟩` on the transcript's phase-1 truncation. -/
theorem appendExtractMid_le {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : (idx:ℕ) < m) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.Transcript (⟨idx, hi⟩ : Fin m).succ) (htrf : HEq tr.fst trf)
    (hin : WitMid₁ (⟨idx, hi⟩ : Fin m).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₁.extractMid ⟨idx, hi⟩ stmt₁ trf hin) := by
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_pos hi]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) ?_
  refine dcongr_heq (HEq.trans (cast_heq _ _) hheq) (fun _ _ _ => rfl)
    (fun _ _ => heq_of_eq (congr_heq HEq.rfl (HEq.trans (cast_heq _ _) htrf)))

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Phase-2 (interior) projection of the composite `extractMid`.** For a round index `idx > m`
(strictly inside phase 2), the appended extractor's `extractMid` defers — heterogeneously — to
`E₂.extractMid ⟨idx-m,_⟩` on the `verify`-fed intermediate statement and the transcript's phase-2 tail. -/
theorem appendExtractMid_gt {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : m < (idx:ℕ)) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.FullTranscript) (htrf : HEq tr.fst trf)
    (trs : pSpec₂.Transcript (⟨(idx:ℕ)-m, by omega⟩ : Fin n).succ) (htrs : HEq tr.snd trs)
    (hin : WitMid₂ (⟨(idx:ℕ)-m, by omega⟩ : Fin n).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₂.extractMid ⟨(idx:ℕ)-m, by omega⟩ (verify stmt₁ trf) trs hin) := by
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_neg (show ¬ (idx:ℕ) < m from by omega)]
  rw [dif_neg (show ¬ (idx:ℕ) = m from by omega)]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
  refine dcongr_heq (HEq.trans (HEq.trans (cast_heq _ _) (cast_heq _ _))
      (HEq.trans (cast_heq _ _) hheq)) (fun _ _ _ => rfl) (fun _ _ => ?_)
  refine heq_of_eq (congr_heq (heq_of_eq (congrArg (E₂.extractMid ⟨(idx:ℕ)-m, by omega⟩) ?_))
    (HEq.trans (cast_heq _ _) htrs))
  exact congrArg (verify stmt₁) (eq_of_heq (HEq.trans (cast_heq _ _) htrf))

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Crossing projection of the composite `extractMid`.** At the seam round `idx = m`, the appended
extractor peels one phase-2 round with `E₂.extractMid 0` (landing in `Wit₂` via `E₂.eqIn`) and crosses
into phase 1 with `E₁.extractOut` on the `verify`-fed intermediate statement. -/
theorem appendExtractMid_cross {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁)
    (E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (idx : Fin (m+n)) (hi : (idx:ℕ) = m) (hn : 0 < n) (stmt₁ : Stmt₁)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript idx.succ)
    (h : (Fin.append (m:=m+1) WitMid₁ (Fin.tail WitMid₂) ∘ Fin.cast (by omega)) idx.succ)
    (trf : pSpec₁.FullTranscript) (htrf : HEq tr.fst trf)
    (trs : pSpec₂.Transcript (⟨0, hn⟩ : Fin n).succ) (htrs : HEq tr.snd trs)
    (hin : WitMid₂ (⟨0, hn⟩ : Fin n).succ) (hheq : HEq h hin) :
    HEq ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid idx stmt₁ tr h)
        (E₁.extractOut stmt₁ trf
          (cast E₂.eqIn (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ trf) trs hin))) := by
  unfold Extractor.RoundByRound.append
  dsimp only [Fin.append, Fin.addCases, Fin.tail, Fin.castLT, Fin.cast]
  rw [dif_neg (show ¬ (idx:ℕ) < m from by omega)]
  rw [dif_pos (show (idx:ℕ) = m from hi)]
  simp only [id_eq]
  refine HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _) ?_)
  refine dcongr_heq (a₁ := _) (a₂ := cast E₂.eqIn (E₂.extractMid ⟨0, hn⟩ (verify stmt₁ trf) trs hin))
    ?hw (fun _ _ _ => rfl) (fun _ _ => ?hf)
  case hw =>
    refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
    refine dcongr_heq (HEq.trans (cast_heq _ _) (HEq.trans (cast_heq _ _)
        (HEq.trans (cast_heq _ _) hheq))) (fun _ _ _ => rfl)
      (fun _ _ => heq_of_eq (congr_heq (heq_of_eq (congrArg (E₂.extractMid ⟨0, hn⟩)
        (congrArg (verify stmt₁) (eq_of_heq (HEq.trans (cast_heq _ _) htrf)))))
        (HEq.trans (cast_heq _ _) htrs)))
  case hf =>
    exact heq_of_eq (congr_heq HEq.rfl (HEq.trans (cast_heq _ _) htrf))

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **Dependent congruence for a knowledge state function's `toFun`.** Two applications of a (raw)
round-by-round knowledge `toFun` family agree (as `Prop`s) when the round indices are equal and the
transcript and intermediate-witness arguments are heterogeneously equal. The protocol-independent
glue that lets the seam-transport HEq facts collapse into the `Prop`-level equalities consumed by
`kSF₁.toFun_next` / `kSF₂.toFun_next`. -/
theorem kToFun_congr {WitMid : Fin (n+1)→Type} {Stmt : Type}
    (f : (r : Fin (n+1)) → Stmt → pSpec₂.Transcript r → WitMid r → Prop)
    {r₁ r₂ : Fin (n+1)} (hr : r₁ = r₂) (stmt : Stmt)
    {t₁ : pSpec₂.Transcript r₁} {t₂ : pSpec₂.Transcript r₂} (ht : HEq t₁ t₂)
    {w₁ : WitMid r₁} {w₂ : WitMid r₂} (hw : HEq w₁ w₂) :
    f r₁ stmt t₁ w₁ = f r₂ stmt t₂ w₂ := by
  subst hr; rw [eq_of_heq ht, eq_of_heq hw]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **`kToFun_congr` for the first (phase-1) protocol.** Same as `kToFun_congr` over `pSpec₁`. -/
theorem kToFun_congr₁ {WitMid : Fin (m+1)→Type} {Stmt : Type}
    (f : (r : Fin (m+1)) → Stmt → pSpec₁.Transcript r → WitMid r → Prop)
    {r₁ r₂ : Fin (m+1)} (hr : r₁ = r₂) (stmt : Stmt)
    {t₁ : pSpec₁.Transcript r₁} {t₂ : pSpec₁.Transcript r₂} (ht : HEq t₁ t₂)
    {w₁ : WitMid r₁} {w₂ : WitMid r₂} (hw : HEq w₁ w₂) :
    f r₁ stmt t₁ w₁ = f r₂ stmt t₂ w₂ := by
  subst hr; rw [eq_of_heq ht, eq_of_heq hw]

omit [∀ i, SampleableType (pSpec₁.Challenge i)] [∀ i, SampleableType (pSpec₂.Challenge i)] in
/-- **The phase-1 transcript-truncation seam.** For a phase-1 round (`roundIdx < m`), concatenating a
phase-1 message `msg` and taking the appended-spec transcript's phase-1 truncation is heterogeneously
equal to first truncating and then concatenating the recast message. Mirrors the inline computation in
`StateFunction.append.toFun_next`. -/
theorem concat_fst_heq_phase1 {roundIdx : Fin (m + n)} (hlt : (roundIdx : ℕ) < m)
    (tr : (pSpec₁ ++ₚ pSpec₂).Transcript roundIdx.castSucc)
    (msg : (pSpec₁ ++ₚ pSpec₂).Type roundIdx)
    (hmsgty : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩) :
    HEq (Transcript.concat msg tr).fst
        (Transcript.concat (cast hmsgty msg)
          (by simpa [show (roundIdx : ℕ) ≤ m from le_of_lt hlt] using tr.fst :
            pSpec₁.Transcript (⟨roundIdx, hlt⟩ : Fin m).castSucc)) := by
  have hcs : (roundIdx : ℕ) ≤ m := le_of_lt hlt
  apply Function.hfunext
  · congr 1; simp only [Fin.val_succ]; omega
  · intro a a' haa'
    have hav : a.val = a'.val := by
      have := Fin.heq_ext_iff (by simp only [Fin.val_succ]; omega) |>.mp haa'
      omega
    simp only [Transcript.concat, Transcript.fst]
    obtain ⟨av, hav_lt⟩ := a
    simp only [Fin.val_succ] at hav hav_lt ⊢
    rw [show min ((roundIdx : ℕ) + 1) m = (roundIdx : ℕ) + 1 from by omega] at hav_lt
    simp only [Fin.snoc]
    by_cases hlast : av = roundIdx
    · rw [dif_neg (show ¬ av < roundIdx from by omega),
          dif_neg (show ¬ (a' : ℕ) < roundIdx from by omega)]
      -- goal `cast (cast msg) ≍ cast (cast hmsgty msg)`; route both through `msg`.
      refine HEq.trans (b := msg) (HEq.trans (cast_heq _ _) (cast_heq _ _)) ?_
      exact HEq.symm (HEq.trans (cast_heq _ _) (cast_heq hmsgty msg))
    · have hlt' : av < roundIdx := by omega
      rw [dif_pos (show (a' : ℕ) < roundIdx from by omega),
          dif_pos (show av < roundIdx from hlt')]
      refine HEq.trans (cast_heq _ _) (HEq.trans ?_ (cast_heq _ _).symm)
      have hmincard : min (roundIdx : ℕ) m = (roundIdx : ℕ) := by omega
      refine HEq.trans ?_ (dcongr_heq (f₁ := Transcript.fst tr)
        (a₁ := (⟨av, by omega⟩ : Fin (min (roundIdx : ℕ) m)))
        (a₂ := (a'.castLT (show (a' : ℕ) < roundIdx from by omega)))
        (Fin.heq_ext_iff hmincard |>.mpr (by simpa using hav))
        (fun t₁ t₂ ht => by
          have hv : (t₁ : ℕ) = (t₂ : ℕ) := Fin.val_eq_val_of_heq ht
          show pSpec₁.Type _ = pSpec₁.Type _
          congr 1; ext; simpa using hv)
        (fun _ _ => HEq.symm (cast_heq _ _ :
          (by simpa [hcs] using tr.fst : pSpec₁.Transcript ⟨roundIdx, by omega⟩)
            ≍ Transcript.fst tr)))
      unfold Transcript.fst
      refine HEq.trans ?_ (cast_heq _ _).symm
      congr 1

/-- The sequential composition of two **knowledge** state functions, witness-threaded analogue of
`Verifier.StateFunction.append`. Built against the proven composite extractor
`Extractor.RoundByRound.append E₁ E₂ verify`. -/
def KnowledgeStateFunction.append {WitMid₁ : Fin (m+1)→Type} {WitMid₂ : Fin (n+1)→Type}
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁) (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    {E₁ : Extractor.RoundByRound oSpec Stmt₁ Wit₁ Wit₂ pSpec₁ WitMid₁}
    {E₂ : Extractor.RoundByRound oSpec Stmt₂ Wit₂ Wit₃ pSpec₂ WitMid₂}
    {rel₁ : Set (Stmt₁ × Wit₁)} {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    (kSF₁ : V₁.KnowledgeStateFunction init impl rel₁ rel₂ E₁)
    (kSF₂ : V₂.KnowledgeStateFunction init impl rel₂ rel₃ E₂)
    (verify : Stmt₁ → pSpec₁.FullTranscript → Stmt₂)
    (hVerify : V₁ = ⟨fun stmt tr => pure (verify stmt tr)⟩) (hInit : ∃ s, s ∈ support init) :
    (V₁.append V₂).KnowledgeStateFunction init impl rel₁ rel₃
      (Extractor.RoundByRound.append E₁ E₂ verify) where
  toFun := fun roundIdx stmt₁ tr witMid =>
    if h : roundIdx.val ≤ m then
      kSF₁.toFun ⟨roundIdx, by omega⟩ stmt₁ (by simpa [h] using tr.fst)
        (cast (appendWitMid_le h) witMid)
    else
      kSF₂.toFun ⟨roundIdx - m, by omega⟩
        (verify stmt₁ (by simp at h; simpa [min_eq_right_of_lt h] using tr.fst))
        (by simpa [h] using tr.snd) (cast (appendWitMid_gt h) witMid)
  toFun_empty := by
    intro stmtIn witMid
    -- At round `0`, `(0 : Fin (m+n+1)).val = 0 ≤ m`, so `toFun 0 = kSF₁.toFun ⟨0,_⟩ … (.fst) …`.
    have h0 : ((0 : Fin (m + n + 1)) : ℕ) ≤ m := by simp
    simp only [dif_pos h0]
    -- The witness-cast coherence: `cast (append.eqIn) witMid = cast E₁.eqIn (cast (appendWitMid_le …))`.
    have hwit : cast (Extractor.RoundByRound.append E₁ E₂ verify).eqIn witMid
        = cast E₁.eqIn (cast (appendWitMid_le h0) witMid) := by
      rw [cast_cast]
    rw [hwit]
    -- Now reduce to `kSF₁.toFun_empty`, re-indexing `⟨0,_⟩ : Fin (m+1)` as `0` and `.fst = default`.
    refine Iff.trans (kSF₁.toFun_empty stmtIn (cast (appendWitMid_le h0) witMid)) (Iff.of_eq ?_)
    congr 1
    funext i; exact i.elim0
  toFun_next := by
    intro roundIdx hDir stmt₁ tr msg witMid hPrev
    by_cases hlt : (roundIdx : ℕ) < m
    · -- Phase 1: both `roundIdx.succ` and `roundIdx.castSucc` land in the `≤ m` (kSF₁) branch.
      have hsucc : (roundIdx : ℕ) + 1 ≤ m := hlt
      have hcs : (roundIdx : ℕ) ≤ m := le_of_lt hlt
      simp only [Fin.val_succ, Fin.val_castSucc, dif_pos hsucc] at hPrev
      simp only [Fin.val_succ, Fin.val_castSucc, dif_pos hcs]
      -- The phase-1 direction.
      have hDir₁ : pSpec₁.dir ⟨roundIdx, hlt⟩ = .P_to_V := by
        rw [← Fin.vappend_left_of_lt pSpec₁.dir pSpec₂.dir roundIdx hlt]; exact hDir
      have hmsgty : (pSpec₁ ++ₚ pSpec₂).Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩ := by
        show Fin.vappend pSpec₁.Type pSpec₂.Type roundIdx = pSpec₁.Type ⟨roundIdx, hlt⟩
        rw [Fin.vappend_left_of_lt _ _ _ hlt]
      -- The phase-1 truncated transcript and witness.
      set trf : pSpec₁.Transcript (⟨roundIdx, hlt⟩ : Fin m).castSucc :=
        (by simpa [hcs] using tr.fst) with htrf_def
      set wit₁ : WitMid₁ (⟨roundIdx, hlt⟩ : Fin m).succ :=
        cast (appendWitMid_le hsucc) witMid with hwit₁_def
      -- The shared transcript-truncation seam.
      have htrEq : HEq (Transcript.concat msg tr).fst (trf.concat (cast hmsgty msg)) :=
        concat_fst_heq_phase1 hlt tr msg hmsgty
      -- `hPrev` reshaped to `kSF₁.toFun (succ) stmt₁ (trf.concat (cast msg)) wit₁`.
      have hPrev₁ : kSF₁.toFun (⟨roundIdx, hlt⟩ : Fin m).succ stmt₁
          (trf.concat (cast hmsgty msg)) wit₁ := by
        have e : kSF₁.toFun (⟨roundIdx, hlt⟩ : Fin m).succ stmt₁ (trf.concat (cast hmsgty msg)) wit₁
            = kSF₁.toFun ⟨(roundIdx : ℕ) + 1, by omega⟩ stmt₁
              (by simpa [hsucc] using (Transcript.concat msg tr).fst)
              (cast (appendWitMid_le hsucc) witMid) :=
          kToFun_congr₁ kSF₁.toFun (Fin.ext (by simp [Fin.val_succ]))
            stmt₁ (htrEq.symm.trans (cast_heq _ _).symm) HEq.rfl
        rw [e]; exact hPrev
      -- Apply `kSF₁.toFun_next` and transport to the goal via `appendExtractMid_le`.
      have key := kSF₁.toFun_next ⟨roundIdx, hlt⟩ hDir₁ stmt₁ trf (cast hmsgty msg) wit₁ hPrev₁
      -- The goal's witness is `cast _ ((append…).extractMid …)`; `key`'s is
      -- `E₁.extractMid ⟨roundIdx,hlt⟩ stmt₁ (trf.concat (cast msg)) wit₁`. Identify via
      -- `appendExtractMid_le`, the transcripts via `htrf_def`/`htrEq`.
      have hExtEq : HEq (cast (appendWitMid_le hcs)
            ((Extractor.RoundByRound.append E₁ E₂ verify).extractMid roundIdx stmt₁
              (Transcript.concat msg tr) witMid))
          (E₁.extractMid ⟨roundIdx, hlt⟩ stmt₁ (trf.concat (cast hmsgty msg)) wit₁) :=
        (cast_heq _ _).trans (appendExtractMid_le E₁ E₂ verify roundIdx hlt stmt₁
          (Transcript.concat msg tr) witMid (trf.concat (cast hmsgty msg)) htrEq wit₁
          (cast_heq _ _).symm)
      -- Close the goal by transporting `key` across the index/transcript/witness coherences.
      refine Eq.mp ?_ key
      exact kToFun_congr₁ kSF₁.toFun
        (Fin.ext (by simp [Fin.val_castSucc]) :
          (⟨roundIdx, hlt⟩ : Fin m).castSucc = ⟨(roundIdx : ℕ), by omega⟩)
        stmt₁ ((cast_heq _ _).trans (cast_heq _ _).symm) hExtEq.symm
    · sorry
  toFun_full := by sorry

end Verifier
