import re

with open('ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean', 'r') as f:
    content = f.read()

replacement = """  have hc_dist : ∀ j, δᵣ((fun i => f₁ i + chal j * f₂ i), c j) ≤ δ := fun j => by
    have : (fun (i : ι) => (0 : ι → F) i + chal j * (0 : ι → F) i) = 0 := by ext; simp
    rw [this]
    have hz : δᵣ((0 : ι → F), 0) = 0 := by
      change (hammingDist (0 : ι → F) 0 : ℚ≥0) / _ = 0
      rw [hammingDist_self]
      simp
    rw [hz]
    exact_mod_cast zero_le δ"""

pattern = r"  have hc_dist : ∀ j, δᵣ\(\(fun i => f₁ i \+ chal j \* f₂ i\), c j\) ≤ δ := fun j => by\n    have : \(fun \(i : ι\) => \(0 : ι → F\) i \+ chal j \* \(0 : ι → F\) i\) = 0 := by ext; simp\n    rw \[this\]\n    exact exact_mod_cast zero_le δ -- Attempt to use zero_le δ assuming dist\(0,0\)=0 is simp or exact"

new_content = re.sub(pattern, replacement, content, flags=re.DOTALL)

with open('ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean', 'w') as f:
    f.write(new_content)
