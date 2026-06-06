import ArkLib.ProofSystem.ToyProblem.SoundnessBounds
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Omega

open scoped NNReal

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]

lemma N_le_choose_two_add_one (N : ℕ) : N ≤ N.choose 2 + 1 := by
  induction N with
  | zero => decide
  | succ n ih =>
    cases n with
    | zero => decide
    | succ m =>
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      omega

lemma N_le_F_of_choose (N F_card : ℕ) (h : F_card > N.choose 2) : N ≤ F_card := by
  have h1 := N_le_choose_two_add_one N
  omega

theorem my_trivial_proof {k : ℕ} [Nonempty ι]
    (C : Set (ι → F)) (δ : ℝ≥0)
    (hδle : δ ≤ 1)
    (hEnc : ∃ encode : (Fin k → F) →ₗ[F] (ι → F),
      (∀ m, encode m ∈ C) ∧ ∀ c ∈ C, ∃ m, encode m = c)
    (_hF : (Fintype.card F : ℝ) >
      ((Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat).choose 2) :
    simplified_iop_soundness_listDecoding_lb_residual (k := k) C δ := by
  refine ⟨hδle, hEnc, 0, 0, ?_⟩
  let N := (Lambda (interleavedCodeSet (κ := Fin 2) C) (δ : ℝ)).toNat
  have hF_nat : N.choose 2 < Fintype.card F := by exact_mod_cast _hF
  have h_le : N ≤ Fintype.card F := N_le_F_of_choose N (Fintype.card F) hF_nat
  have ⟨chal, hchal_inj⟩ : ∃ chal : Fin N → F, Function.Injective chal :=
    Finite.exists_injective_of_card_le_card (by simpa using h_le)
  refine ⟨chal, hchal_inj, fun _ => 0, ?_, ?_⟩
  · intro j
    obtain ⟨encode, hC, _⟩ := hEnc
    have h0 : encode 0 ∈ C := hC 0
    rwa [map_zero] at h0
  · intro j
    have : (fun (i : ι) => (0 : ι → F) i + chal j * (0 : ι → F) i) = 0 := by ext; simp
    rw [this]
    change δᵣ(0, 0) ≤ δ
    sorry
