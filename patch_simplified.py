import re

with open("ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean", "r") as f:
    content = f.read()

# 1. Remove simplifiedIOR_knowledgeSound_residual
res_pattern = r"/\*\* Named bridge residual\.\*\*.*theorem simplifiedIOR_knowledgeSound_residual.*?=.*?\n\n"
content = re.sub(res_pattern, "", content, flags=re.DOTALL)

# 2. Update simplifiedIOR_knowledgeSound
ks_pattern = r"theorem simplifiedIOR_knowledgeSound\n    \[SampleableType F\] \[Nonempty ι\] \[Nonempty F\]\n    \{σ : Type\} \(init : ProbComp σ\)\n    \(impl : QueryImpl \[\]ₒ \(StateT σ ProbComp\)\)\n    \(C : Set \(ι → F\)\) \(δ : ℝ≥0\)\n    \(encode : \(Fin k → F\) → \(ι → F\)\)\n    \(_hδ_pos : 0 < δ\)\n    \(_hδ_lt_min : δ < \(minRelHammingDistCode C : ℝ≥0\)\)\n    \(decode : ToyProblem.Spec.ToyPrefix ι F k → \(Fin k → F\) × \(Fin k → F\)\).*?simplifiedIOR_knowledgeSound_residual init impl C δ encode decode hBridge"

replacement = """theorem simplifiedIOR_knowledgeSound
    [SampleableType F] [Nonempty ι] [Nonempty F]
    {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp))
    (C : Set (ι → F)) (δ : ℝ≥0)
    (encode : (Fin k → F) → (ι → F))
    (_hδ_pos : 0 < δ)
    (_hδ_lt_min : δ < (minRelHammingDistCode C : ℝ≥0))
    (decode : ToyProblem.Spec.ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (ToyProblem.Spec.outputRelation k C δ)
      (ToyProblem.Spec.toyStmtOf (ι := ι) (F := F) (k := k))
      (ToyProblem.Spec.toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  ToyProblem.Spec.protocol62_knowledgeSoundnessViaRewinding C δ decode"""

content = re.sub(ks_pattern, replacement, content, flags=re.DOTALL)

# 3. Clean up the #print axioms
content = re.sub(r"#print axioms simplifiedIOR_knowledgeSound_residual\n", "", content)
content = re.sub(r"#print axioms ToyProblem.SimplifiedIOR.simplifiedIOR_knowledgeSound_residual\n", "", content)

with open("ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean", "w") as f:
    f.write(content)

