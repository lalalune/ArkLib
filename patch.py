import re

with open('ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean', 'r') as f:
    content = f.read()

replacement = """theorem simplified_iop_soundness_listDecoding_lb {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (hδle : δ ≤ 1)
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c)
    (_hF : (Fintype.card F : ℝ) >
      ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat).choose 2) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → F),
      ((winningSet C δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) ≥
        (((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ)
            * Fintype.card F)
          / (Fintype.card F
              + ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat : ℝ) - 1) := by
  let N := (Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat
  have hF_nat : N.choose 2 < Fintype.card F := by exact_mod_cast _hF
  have h_le : N ≤ Fintype.card F := by
    have h1 : N ≤ N.choose 2 + 1 := by
      cases N with
      | zero => decide
      | succ n =>
        cases n with
        | zero => decide
        | succ m =>
          rw [Nat.choose_succ_succ, Nat.choose_one_right]
          omega
    omega
  have h_le2 : Fintype.card (Fin N) ≤ Fintype.card F := by
    rw [Fintype.card_fin N]
    exact h_le
  have ⟨chal, hchal_inj⟩ : ∃ chal : Fin N → F, Function.Injective chal := by
    have e_nonempty := Function.Embedding.nonempty_of_card_le (α := Fin N) (β := F) h_le2
    obtain ⟨e⟩ := e_nonempty
    exact ⟨e, e.injective⟩
  let f₁ : ι → F := 0
  let f₂ : ι → F := 0
  let c : Fin N → ι → F := fun _ => 0
  have hc_mem : ∀ j, c j ∈ C := fun _ => by
    obtain ⟨encode, hC, _⟩ := hEnc
    have h0 : encode 0 ∈ C := hC 0
    rwa [map_zero] at h0
  have hc_dist : ∀ j, δᵣ((fun i => f₁ i + chal j * f₂ i), c j) ≤ δ := fun j => by
    have : (fun (i : ι) => (0 : ι → F) i + chal j * (0 : ι → F) i) = 0 := by ext; simp
    rw [this]
    exact exact_mod_cast zero_le δ -- Attempt to use zero_le δ assuming dist(0,0)=0 is simp or exact
  refine ⟨(0 : Fin k → F), 0, 0, f₁, f₂, ?_⟩
  exact simplified_iop_listDecoding_lb_of_winningChallenges hδle hEnc
    chal hchal_inj c hc_mem hc_dist"""

pattern = r"theorem simplified_iop_soundness_listDecoding_lb \{k : ℕ\} \[Nonempty ι\].*?exact simplified_iop_listDecoding_lb_of_winningChallenges hδle hEnc\n    chal hchal_inj c hc_mem hc_dist"

new_content = re.sub(pattern, replacement, content, flags=re.DOTALL)

with open('ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean', 'w') as f:
    f.write(new_content)
