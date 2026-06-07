import ArkLib.ToMathlib.KoalaIRSAccounting

open KoalaBear Code
open scoped NNReal

lemma le_minDist_rsCodeSet : 3 ≤ minDist rsCodeSet := by
  unfold minDist
  -- We want to prove 3 ≤ sInf {d | ∃ u ∈ rsCodeSet, ∃ v ∈ rsCodeSet, u ≠ v ∧ hammingDist u v = d}
  have H : {d | ∃ u ∈ rsCodeSet, ∃ v ∈ rsCodeSet, u ≠ v ∧ hammingDist u v = d}.Nonempty := by
    use hammingDist (rsEncoder 0) (rsEncoder 1)
    simp only [Set.mem_setOf_eq]
    use rsEncoder 0
    refine ⟨⟨0, rfl⟩, rsEncoder 1, ⟨1, rfl⟩, ?_, rfl⟩
    intro heq
    have h01 : (0 : Fin 2 → Sextic) = 1 := rsEncoder_injective heq
    have h_eval : (0 : Fin 2 → Sextic) 0 = (1 : Fin 2 → Sextic) 0 := by rw [h01]
    simp only [Pi.zero_apply, Pi.one_apply, zero_ne_one] at h_eval
  -- For Nat, we can use `le_csInf` or `le_sInf`? Wait, let's try `le_sInf`.
  -- Wait, `sInf` for Nat. Let's see what works. 
  have H2 : ∀ d ∈ {d | ∃ u ∈ rsCodeSet, ∃ v ∈ rsCodeSet, u ≠ v ∧ hammingDist u v = d}, 3 ≤ d := by
    rintro d ⟨u, ⟨m, rfl⟩, v, ⟨m', rfl⟩, hne, rfl⟩
    exact hammingDist_rsEncoder_ge_three hne
  exact csInf_le_of_le H2 -- wait, is it `le_csInf`? Let's just try a few and let lean complain.
