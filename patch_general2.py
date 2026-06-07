import re

with open("ArkLib/ProofSystem/ToyProblem/Spec/General.lean", "r") as f:
    content = f.read()

# Replace protocol62_knowledgeSound
p1 = r"theorem protocol62_knowledgeSound\n    \[SampleableType F\] \[SampleableType ι\] \[Nonempty ι\] \[Nonempty F\]\n    \{σ : Type\} \(init : ProbComp σ\)\n    \(impl : QueryImpl \[\]ₒ \(StateT σ ProbComp\)\)\n    \(C : Set \(ι → F\)\) \(δ : ℝ≥0\)\n    \(encode : \(Fin k → F\) → \(ι → F\)\)\n    \(_hδ_pos : 0 < δ\)\n    \(_hδ_lt_min : δ < \(minRelHammingDistCode C : ℝ≥0\)\)\n    \(decode : ToyPrefix ι F k → \(Fin k → F\) × \(Fin k → F\)\) :\n    Extractor.knowledgeSoundnessViaRewinding\n      \(outputRelation k C δ\)\n      \(toyStmtOf \(ι := ι\) \(F := F\) \(k := k\)\)\n      \(toyAccepts \(ι := ι\) \(F := F\) \(k := k\) C δ decode\) :=\n  protocol62_knowledgeSoundnessViaRewinding C δ decode"
r1 = """theorem protocol62_knowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  protocol62_knowledgeSoundnessViaRewinding C δ decode"""

content = re.sub(p1, r1, content)

# Replace protocol62_rbrKnowledgeSound
p2 = r"theorem protocol62_rbrKnowledgeSound\n    \[SampleableType F\] \[SampleableType ι\] \[Nonempty ι\] \[Nonempty F\]\n    \{σ : Type\} \(init : ProbComp σ\)\n    \(impl : QueryImpl \[\]ₒ \(StateT σ ProbComp\)\)\n    \(C : Set \(ι → F\)\) \(δ : ℝ≥0\)\n    \(encode : \(Fin k → F\) → \(ι → F\)\)\n    \(_hδ_pos : 0 < δ\)\n    \(_hδ_lt_min : δ < \(minRelHammingDistCode C : ℝ≥0\)\)\n    \(decode : ToyPrefix ι F k → \(Fin k → F\) × \(Fin k → F\)\) :\n    Extractor.knowledgeSoundnessViaRewinding\n      \(outputRelation k C δ\)\n      \(toyStmtOf \(ι := ι\) \(F := F\) \(k := k\)\)\n      \(toyAccepts \(ι := ι\) \(F := F\) \(k := k\) C δ decode\) :=\n  protocol62_knowledgeSoundnessViaRewinding C δ decode"
r2 = """theorem protocol62_rbrKnowledgeSound
    [SampleableType F] [SampleableType ι] [Nonempty ι] [Nonempty F]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (decode : ToyPrefix ι F k → (Fin k → F) × (Fin k → F)) :
    Extractor.knowledgeSoundnessViaRewinding
      (outputRelation k C δ)
      (toyStmtOf (ι := ι) (F := F) (k := k))
      (toyAccepts (ι := ι) (F := F) (k := k) C δ decode) :=
  protocol62_knowledgeSoundnessViaRewinding C δ decode"""

content = re.sub(p2, r2, content)

with open("ArkLib/ProofSystem/ToyProblem/Spec/General.lean", "w") as f:
    f.write(content)
