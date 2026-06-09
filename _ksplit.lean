import ArkLib.OracleReduction.Composition.Sequential.Append
open OracleSpec OracleComp ProtocolSpec
namespace KSplit
variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

theorem messages_fst_heq (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (k : pSpec₁.MessageIdx) :
    HEq (tr.fst.messages k) (tr.messages (MessageIdx.inl k)) := by
  show HEq (tr.fst k.val) (tr (MessageIdx.inl k).val)
  unfold FullTranscript.fst
  simp only [MessageIdx.inl]
  exact cast_heq _ _

theorem messages_snd_heq (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (k : pSpec₂.MessageIdx) :
    HEq (tr.snd.messages k) (tr.messages (MessageIdx.inr k)) := by
  show HEq (tr.snd k.val) (tr (MessageIdx.inr k).val)
  unfold FullTranscript.snd
  simp only [MessageIdx.inr]
  exact cast_heq _ _

theorem challenges_fst_heq (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : ChallengeIdx pSpec₁) :
    HEq (tr.fst.challenges i) (tr.challenges (ChallengeIdx.inl i)) := by
  show HEq (tr.fst i.val) (tr (ChallengeIdx.inl i).val)
  unfold FullTranscript.fst
  simp only [ChallengeIdx.inl]
  exact cast_heq _ _

theorem challenges_snd_heq (tr : FullTranscript (pSpec₁ ++ₚ pSpec₂)) (i : ChallengeIdx pSpec₂) :
    HEq (tr.snd.challenges i) (tr.challenges (ChallengeIdx.inr i)) := by
  show HEq (tr.snd i.val) (tr (ChallengeIdx.inr i).val)
  unfold FullTranscript.snd
  simp only [ChallengeIdx.inr]
  exact cast_heq _ _
end KSplit
