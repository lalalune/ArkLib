import re

with open("ArkLib/ProofSystem/ToyProblem/Spec/General.lean", "r") as f:
    content = f.read()

# 1. Remove protocol62_knowledgeSound_residual
residual_pattern = r"/\*\* Named bridge residual\.\*\*.*theorem protocol62_knowledgeSound_residual.*?=.*?\n\n"
content = re.sub(residual_pattern, "", content, flags=re.DOTALL)

# 2. Update protocol62_knowledgeSound
# It originally took hBridge and returned (verifier ...).knowledgeSoundness ...
ks_pattern = r"theorem protocol62_knowledgeSound\n    \[SampleableType F\] \[SampleableType ι\] \[Nonempty ι\] \[Nonempty F\]\n    \{σ : Type\} \(init : ProbComp σ\)\n    \(impl : QueryImpl \[\]ₒ \(StateT σ ProbComp\)\)\n    \(C : Set \(ι → F\)\) \(δ : ℝ≥0\)\n    \(encode : \(Fin k → F\) → \(ι → F\)\)\n    \(_hδ_pos : 0 < δ\)\n    \(_hδ_lt_min : δ < \(minRelHammingDistCode C : ℝ≥0\)\)\n    \(decode : ToyPrefix ι F k → \(Fin k → F\) × \(Fin k → F\)\).*?protocol62_knowledgeSound_residual t init impl C δ encode decode hBridge"

replacement = """theorem protocol62_knowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Nonempty F]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) → (ι → F))
    (_hδ_pos : 0 < δ)
    (_hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0))
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  protocol62_knowledgeSoundnessViaRewinding C δ decode"""

content = re.sub(ks_pattern, replacement, content, flags=re.DOTALL)

# 3. Remove protocol62_rbrKnowledgeSound_residual
rbr_residual_pattern = r"/\*\* Named bridge residual\.\*\*.*theorem protocol62_rbrKnowledgeSound_residual.*?=.*?\n\n"
content = re.sub(rbr_residual_pattern, "", content, flags=re.DOTALL)

# 4. Update protocol62_rbrKnowledgeSound
rbr_ks_pattern = r"theorem protocol62_rbrKnowledgeSound\n    \[SampleableType F\] \[SampleableType ι\] \[Nonempty ι\] \[Nonempty F\]\n    \{σ : Type\} \(init : ProbComp σ\)\n    \(impl : QueryImpl \[\]ₒ \(StateT σ ProbComp\)\)\n    \(C : Set \(ι → F\)\) \(δ : ℝ≥0\)\n    \(encode : \(Fin k → F\) → \(ι → F\)\)\n    \(_hδ_pos : 0 < δ\)\n    \(_hδ_lt_min : δ < \(minRelHammingDistCode C : ℝ≥0\)\)\n    \(decode : ToyPrefix ι F k → \(Fin k → F\) × \(Fin k → F\)\).*?protocol62_rbrKnowledgeSound_residual t init impl C δ encode decode hBridge"

rbr_replacement = """theorem protocol62_rbrKnowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Nonempty F]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) → (ι → F))
    (_hδ_pos : 0 < δ)
    (_hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0))
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  protocol62_knowledgeSoundnessViaRewinding C δ decode"""

content = re.sub(rbr_ks_pattern, rbr_replacement, content, flags=re.DOTALL)

# 5. Clean up the #print axioms
content = re.sub(r"#print axioms ToyProblem.Spec.protocol62_knowledgeSound_residual\n", "", content)

with open("ArkLib/ProofSystem/ToyProblem/Spec/General.lean", "w") as f:
    f.write(content)

