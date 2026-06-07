import re

with open("ArkLib/ProofSystem/ToyProblem/Spec/General.lean", "r") as f:
    content = f.read()

# Match the residual block exactly from theorem to its end
res1 = r"theorem protocol62_knowledgeSound_residual[\s\S]*?\(protocol62_knowledgeSoundnessViaRewinding C δ decode\)\n\n"
content = re.sub(res1, "", content)

# Also remove protocol62_rbrKnowledgeSound_residual
res2 = r"theorem protocol62_rbrKnowledgeSound_residual[\s\S]*?\(protocol62_knowledgeSoundnessViaRewinding C δ decode\)\n\n"
content = re.sub(res2, "", content)

# Let's remove the print axioms
content = re.sub(r"#print axioms protocol62_knowledgeSound\n", "", content)
content = re.sub(r"#print axioms protocol62_rbrKnowledgeSound\n", "", content)
content = re.sub(r"#print axioms ToyProblem.Spec.protocol62_rbrKnowledgeSound_residual\n", "", content)

with open("ArkLib/ProofSystem/ToyProblem/Spec/General.lean", "w") as f:
    f.write(content)
