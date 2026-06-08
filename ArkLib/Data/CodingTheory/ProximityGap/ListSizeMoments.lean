/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.InformationTheory.Hamming
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The moment method for list size (verified, self-contained) — direction A for #232

The Grand Challenges ask for the threshold `δ*` where the list size `|Λ(C, δ, f)|` (codewords within
relative distance `δ` of `f`) crosses `ε*·|F|`. The **moment method** reduces this to exact
combinatorics: averaging over a uniformly-random received word `f`, the first and second moments of
`|Λ|` are *exactly* computable, and for an MDS code (Reed–Solomon) they are closed forms in the
known weight enumerator. This file proves the foundational moment identities, `sorry`-free.

* `card_dist_le_eq_ballVol` — **translation invariance**: the number of words within Hamming distance
  `r` of any fixed `c` equals the ball volume `V(r) = |{g : d(0,g) ≤ r}|` (a translate of the ball at
  `0`). This is the symmetry that makes the average list size independent of which codeword.
* `first_moment` — `Σ_f |Λ(C, r, f)| = |C| · V(r)`, i.e. `E_f[|Λ|] = |C|·V(r)/qⁿ` *exactly*, for an
  arbitrary finite `C` (no linearity needed). The first moment crosses `ε*·|F|` at a definite radius;
  this is the (easy) averaged half of pinning `δ*`.

The second-moment companion (the prize-relevant `Σ_f |Λ|² = Σ_{c,c'∈C} (pair-ball volume)`, which for
a linear code collapses onto the weight enumerator) builds on the same translation symmetry.
-/

namespace ArkLib.CodingTheory.ListMoments

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [AddCommGroup F]

/-- **Hamming distance is translation invariant**: adding the same `v` to both arguments leaves the
distance unchanged. -/
lemma hammingDist_add_right (x y v : ι → F) :
    hammingDist (x + v) (y + v) = hammingDist x y := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.add_apply, ne_eq, add_left_inj]

/-- `hammingDist c (g + c) = hammingDist 0 g`: the ball around `c` is a translate of the ball at `0`. -/
lemma hammingDist_translate (c g : ι → F) :
    hammingDist c (g + c) = hammingDist (0 : ι → F) g := by
  have h := hammingDist_add_right (0 : ι → F) g c
  simpa using h

/-- The Hamming-ball volume `V(r) = |{g : d(0,g) ≤ r}|`. -/
def ballVol (ι : Type*) (F : Type*) [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F]
    [AddCommGroup F] (r : ℕ) : ℕ :=
  (Finset.univ.filter (fun f : ι → F => hammingDist (0 : ι → F) f ≤ r)).card

/-- **Translation invariance of ball volume.** The number of words within Hamming distance `r` of any
fixed center `c` equals `V(r)`. Proof: `g ↦ g + c` bijects the ball at `0` with the ball at `c`. -/
lemma card_dist_le_eq_ballVol (r : ℕ) (c : ι → F) :
    (Finset.univ.filter (fun f => hammingDist c f ≤ r)).card = ballVol ι F r := by
  unfold ballVol
  refine Finset.card_nbij' (fun f => f - c) (fun g => g + c) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    have : hammingDist c ((f - c) + c) = hammingDist (0 : ι → F) (f - c) := hammingDist_translate c _
    rw [sub_add_cancel] at this
    rwa [← this]
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    rwa [hammingDist_translate c g]
  · intro f _; exact sub_add_cancel f c
  · intro g _; exact add_sub_cancel_right g c

/-- The decoding list `Λ(C, r, f)`: codewords of `C` within Hamming distance `r` of `f`. -/
def lam (C : Finset (ι → F)) (r : ℕ) (f : ι → F) : Finset (ι → F) :=
  C.filter (fun c => hammingDist c f ≤ r)

/-- **First-moment identity.** Summed over all received words `f`, the total list size is exactly
`|C| · V(r)`. Dividing by `qⁿ`: `E_f[|Λ(C, r, f)|] = |C|·V(r)/qⁿ`. Holds for *any* finite `C`
(linearity is not needed for the first moment). -/
theorem first_moment (C : Finset (ι → F)) (r : ℕ) :
    ∑ f : ι → F, (lam C r f).card = C.card * ballVol ι F r := by
  simp only [lam, Finset.card_filter]
  rw [Finset.sum_comm]
  have hinner : ∀ c, (∑ f : ι → F, (if hammingDist c f ≤ r then (1 : ℕ) else 0)) = ballVol ι F r := by
    intro c
    rw [← Finset.card_filter]
    exact card_dist_le_eq_ballVol r c
  rw [Finset.sum_congr rfl (fun c _ => hinner c), Finset.sum_const, smul_eq_mul]

/-- **Translation of the pair-ball count.** The number of words within distance `r` of *both* `c` and
`c'` depends only on the difference `c' - c`: it equals the number of `g` within `r` of both `0` and
`c' - c`. -/
lemma pairBall_translate (c c' : ι → F) (r : ℕ) :
    (Finset.univ.filter (fun f => hammingDist c f ≤ r ∧ hammingDist c' f ≤ r)).card
      = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist (c' - c) g ≤ r)).card := by
  refine Finset.card_nbij' (fun f => f - c) (fun g => g + c) ?_ ?_ ?_ ?_
  · intro f hf
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    obtain ⟨h1, h2⟩ := hf
    refine ⟨?_, ?_⟩
    · have hh := hammingDist_translate c (f - c)
      rw [sub_add_cancel] at hh
      rw [← hh]; exact h1
    · have hh := hammingDist_add_right (c' - c) (f - c) c
      rw [sub_add_cancel, sub_add_cancel] at hh
      rw [← hh]; exact h2
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2⟩ := hg
    refine ⟨?_, ?_⟩
    · rw [hammingDist_translate c g]; exact h1
    · have hh := hammingDist_add_right (c' - c) g c
      rw [sub_add_cancel] at hh
      rw [hh]; exact h2
  · intro f _; exact sub_add_cancel f c
  · intro g _; exact add_sub_cancel_right g c

/-- **Second-moment expansion.** `Σ_f |Λ(C,r,f)|²` counts, over ordered pairs of codewords, the words
within distance `r` of both. -/
theorem second_moment_pairs (C : Finset (ι → F)) (r : ℕ) :
    ∑ f : ι → F, (lam C r f).card ^ 2
      = ∑ c ∈ C, ∑ c' ∈ C,
          (Finset.univ.filter (fun f => hammingDist c f ≤ r ∧ hammingDist c' f ≤ r)).card := by
  have hsq : ∀ f : ι → F,
      (lam C r f).card ^ 2
        = ∑ c ∈ C, ∑ c' ∈ C, (if hammingDist c f ≤ r ∧ hammingDist c' f ≤ r then (1 : ℕ) else 0) := by
    intro f
    rw [lam, Finset.card_filter, pow_two, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun c _ => Finset.sum_congr rfl (fun c' _ => ?_))
    by_cases h1 : hammingDist c f ≤ r <;> by_cases h2 : hammingDist c' f ≤ r <;> simp [h1, h2]
  simp only [hsq]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  rw [← Finset.card_filter]

/-- **Second moment in difference-reduced form.** `Σ_f |Λ(C,r,f)|²` equals `Σ_{c,c'∈C}` of a count
that depends only on the difference `c' - c`. For a linear code this collapses onto the weight
enumerator: each difference `c' - c` is itself a codeword, and the count depends only on its weight,
so `Σ_f |Λ|² = |C| · Σ_w A_w · N(w,r)` (`A_w` the weight enumerator, `N(w,r)` the pair-ball count of a
weight-`w` vector). This is the exact second moment underlying direction A for pinning `δ*`. -/
theorem second_moment_translate (C : Finset (ι → F)) (r : ℕ) :
    ∑ f : ι → F, (lam C r f).card ^ 2
      = ∑ c ∈ C, ∑ c' ∈ C,
          (Finset.univ.filter
            (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist (c' - c) g ≤ r)).card := by
  rw [second_moment_pairs]
  exact Finset.sum_congr rfl
    (fun c _ => Finset.sum_congr rfl (fun c' _ => pairBall_translate c c' r))

/-- **Linear reindexing.** For `C` closed under addition and subtraction, summing any `g` over the
*differences* `c' - c` of ordered pairs equals `|C|` copies of the sum of `g` over `C`. (For each
`c`, the map `c' ↦ c' - c` bijects `C` with `C`.) -/
theorem sum_pairs_diff {β : Type*} [AddCommMonoid β] {C : Finset (ι → F)}
    (hadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C) (hsub : ∀ a ∈ C, ∀ b ∈ C, a - b ∈ C)
    (g : (ι → F) → β) :
    ∑ c ∈ C, ∑ c' ∈ C, g (c' - c) = C.card • ∑ v ∈ C, g v := by
  have key : ∀ c ∈ C, (∑ c' ∈ C, g (c' - c)) = ∑ v ∈ C, g v := by
    intro c hc
    refine Finset.sum_bij' (fun c' _ => c' - c) (fun v _ => v + c) ?_ ?_ ?_ ?_ ?_
    · intro c' hc'; exact hsub c' hc' c hc
    · intro v hv; exact hadd v hv c hc
    · intro c' _; exact sub_add_cancel c' c
    · intro v _; exact add_sub_cancel_right v c
    · intro c' _; rfl
  rw [Finset.sum_congr rfl key, Finset.sum_const]

/-- **Second moment for a linear code.** The `|C|²` pair sum collapses to `|C|` times a sum over
codewords: `Σ_f |Λ(C,r,f)|² = |C| · Σ_{v∈C} N(v,r)`, where `N(v,r) = #{g : d(0,g) ≤ r ∧ d(v,g) ≤ r}`.
Since each difference `v = c' - c` is itself a codeword, the second moment is governed entirely by the
codewords' weights (next: `N(v,r)` depends only on `wt(v)`, giving `Σ_w A_w · N(w,r)`). -/
theorem second_moment_linear {C : Finset (ι → F)}
    (hadd : ∀ a ∈ C, ∀ b ∈ C, a + b ∈ C) (hsub : ∀ a ∈ C, ∀ b ∈ C, a - b ∈ C) (r : ℕ) :
    ∑ f : ι → F, (lam C r f).card ^ 2
      = C.card • ∑ v ∈ C,
          (Finset.univ.filter (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card := by
  rw [second_moment_translate]
  exact sum_pairs_diff hadd hsub
    (fun v => (Finset.univ.filter (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card)

/-- **Hamming distance is invariant under permuting coordinates.** -/
lemma hammingDist_comp_perm (σ : Equiv.Perm ι) (a b : ι → F) :
    hammingDist (a ∘ σ) (b ∘ σ) = hammingDist a b := by
  unfold hammingDist
  refine Finset.card_nbij' (fun i => σ i) (fun j => σ.symm j) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply] at hi ⊢
    exact hi
  · intro j hj
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.comp_apply, Equiv.apply_symm_apply] at hj ⊢
    exact hj
  · intro i _; exact σ.symm_apply_apply i
  · intro j _; exact σ.apply_symm_apply j

/-- **Coordinate-permutation invariance of the pair-ball count `N`.** `N(v, r) = N(v ∘ σ, r)`: only
the *multiset* of values of `v` matters, not their positions. (Combined with per-coordinate scaling —
the monomial symmetry over a field — this gives that `N` depends only on the Hamming weight `wt(v)`,
collapsing `Σ_{v∈C} N(v,r)` onto the weight enumerator `Σ_w A_w · N(w,r)`.) -/
lemma pairBall_perm (σ : Equiv.Perm ι) (v : ι → F) (r : ℕ) :
    (Finset.univ.filter (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card
      = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist (v ∘ σ) g ≤ r)).card := by
  refine Finset.card_nbij' (fun g => g ∘ σ) (fun h => h ∘ σ.symm) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2⟩ := hg
    have h0 : hammingDist (0 : ι → F) (g ∘ σ) = hammingDist (0 : ι → F) g :=
      hammingDist_comp_perm σ 0 g
    exact ⟨h0 ▸ h1, (hammingDist_comp_perm σ v g) ▸ h2⟩
  · intro h hh
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    obtain ⟨h1, h2⟩ := hh
    have h0 : hammingDist (0 : ι → F) (h ∘ σ.symm) = hammingDist (0 : ι → F) h :=
      hammingDist_comp_perm σ.symm 0 h
    have hv : hammingDist v (h ∘ σ.symm) = hammingDist (v ∘ σ) h := by
      have hvs : (v ∘ σ) ∘ σ.symm = v := by ext i; simp
      have := hammingDist_comp_perm σ.symm (v ∘ σ) h
      rwa [hvs] at this
    exact ⟨h0 ▸ h1, hv ▸ h2⟩
  · intro g _; funext i; simp
  · intro h _; funext i; simp

/-! ## Scaling invariance and weight-only dependence (over a field)

The pair-ball count `N` is invariant under **permuting** coordinates (`pairBall_perm`) and under
**coordinate-wise scaling** by nonzero field elements (`pairBall_scale`). Together these say `N(v,r)`
depends only on the multiset `{nonzero}` pattern up to scaling — i.e. **only on the Hamming weight**
`wt(v)` (`pairBall_weight`). This is the symmetry that collapses `Σ_{v∈C} N(v,r)` onto the weight
enumerator `Σ_w A_w · N(w,r)`, completing the reduction of the second moment to `A_w` for any linear
code (direction A for #232). -/

section Field

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Fintype F] [DecidableEq F] [Field F]

/-- **Hamming distance is invariant under coordinate-wise scaling by units.** Multiplying both
arguments coordinate-wise by `u` with every `u i ≠ 0` leaves the distance unchanged (a field has no
zero divisors, so `u i · a i = u i · b i ↔ a i = b i`). -/
lemma hammingDist_mul_left {u : ι → F} (hu : ∀ i, u i ≠ 0) (a b : ι → F) :
    hammingDist (fun i => u i * a i) (fun i => u i * b i) = hammingDist a b := by
  unfold hammingDist
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
  constructor
  · intro h hab; exact h (by rw [hab])
  · intro h hab; exact h (mul_left_cancel₀ (hu i) hab)

/-- **Scaling invariance of the pair-ball count `N`.** `N(v, r) = N(u·v, r)` for any `u` with all
coordinates nonzero: `g ↦ u·g` bijects, preserving both `d(0,·)` and `d(v,·)`. -/
lemma pairBall_scale {u : ι → F} (hu : ∀ i, u i ≠ 0) (v : ι → F) (r : ℕ) :
    (Finset.univ.filter (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card
      = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist (fun i => u i * v i) g ≤ r)).card := by
  have huinv : ∀ i, (u i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hu i)
  refine Finset.card_nbij' (fun g i => u i * g i) (fun h i => (u i)⁻¹ * h i) ?_ ?_ ?_ ?_
  · intro g hg
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hg ⊢
    obtain ⟨h1, h2⟩ := hg
    have e0 : hammingDist (fun i => u i * (0 : ι → F) i) (fun i => u i * g i)
        = hammingDist (0 : ι → F) g := hammingDist_mul_left hu 0 g
    have ev : hammingDist (fun i => u i * v i) (fun i => u i * g i)
        = hammingDist v g := hammingDist_mul_left hu v g
    simp only [Pi.zero_apply, mul_zero] at e0
    exact ⟨e0 ▸ h1, ev ▸ h2⟩
  · intro h hh
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hh ⊢
    obtain ⟨h1, h2⟩ := hh
    have e0 : hammingDist (fun i => (u i)⁻¹ * (0 : ι → F) i) (fun i => (u i)⁻¹ * h i)
        = hammingDist (0 : ι → F) h := hammingDist_mul_left huinv 0 h
    have ev : hammingDist (fun i => (u i)⁻¹ * ((fun j => u j * v j) i)) (fun i => (u i)⁻¹ * h i)
        = hammingDist (fun i => u i * v i) h := hammingDist_mul_left huinv (fun i => u i * v i) h
    simp only [Pi.zero_apply, mul_zero] at e0
    have hvv : (fun i => (u i)⁻¹ * ((fun j => u j * v j) i)) = v := by
      funext i; simp only; rw [← mul_assoc, inv_mul_cancel₀ (hu i), one_mul]
    rw [hvv] at ev
    exact ⟨e0 ▸ h1, ev ▸ h2⟩
  · intro g _; funext i; simp only; rw [← mul_assoc, inv_mul_cancel₀ (hu i), one_mul]
  · intro h _; funext i; simp only; rw [← mul_assoc, mul_inv_cancel₀ (hu i), one_mul]

/-- **`N` depends only on the Hamming weight.** Over a field, any two vectors of equal weight are
related by a coordinate permutation (matching their supports) followed by a coordinate scaling
(matching their nonzero values), and `N` is invariant under both. Hence `N(v,r) = N(v',r)` whenever
`wt(v) = wt(v')`. This is the symmetry that collapses `Σ_{v∈C} N(v,r)` onto the weight enumerator
`Σ_w A_w · N(w,r)`, completing the reduction of the linear-code second moment to `A_w` (direction A
for #232). -/
theorem pairBall_weight {v v' : ι → F} (hw : hammingNorm v = hammingNorm v') (r : ℕ) :
    (Finset.univ.filter (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card
      = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v' g ≤ r)).card := by
  classical
  set A : Finset ι := Finset.univ.filter (fun i => v i ≠ 0) with hA
  set B : Finset ι := Finset.univ.filter (fun i => v' i ≠ 0) with hB
  have hcard : B.card = A.card := by
    have hAn : A.card = hammingNorm v := rfl
    have hBn : B.card = hammingNorm v' := rfl
    rw [hAn, hBn, hw]
  -- support-matching permutation: maps `supp v'` onto `supp v` and complement to complement
  set e : {x // x ∈ B} ≃ {x // x ∈ A} := Finset.equivOfCardEq hcard with he
  set σ : Equiv.Perm ι := e.extendSubtype with hσ
  have hP1 : ∀ i, v' i ≠ 0 → v (σ i) ≠ 0 := by
    intro i hi
    have hiB : i ∈ B := by rw [hB, Finset.mem_filter]; exact ⟨Finset.mem_univ i, hi⟩
    have hmem : σ i ∈ A := e.extendSubtype_mem i hiB
    rw [hA, Finset.mem_filter] at hmem
    exact hmem.2
  have hP2 : ∀ i, v' i = 0 → v (σ i) = 0 := by
    intro i hi
    have hiB : i ∉ B := by rw [hB, Finset.mem_filter]; push_neg; intro _; exact hi
    have hnotA : σ i ∉ A := e.extendSubtype_not_mem i hiB
    rw [hA, Finset.mem_filter] at hnotA
    push_neg at hnotA
    exact hnotA (Finset.mem_univ _)
  -- the scaling that turns `v ∘ σ` into `v'`
  set u : ι → F := fun i => if v' i = 0 then 1 else v' i * (v (σ i))⁻¹ with hu_def
  have hu : ∀ i, u i ≠ 0 := by
    intro i
    rw [hu_def]
    split
    · exact one_ne_zero
    · rename_i hne
      exact mul_ne_zero hne (inv_ne_zero (hP1 i hne))
  have hv' : (fun i => u i * (v ∘ σ) i) = v' := by
    funext i
    simp only [hu_def, Function.comp_apply]
    split
    · rename_i h0
      rw [hP2 i h0, mul_zero, h0]
    · rename_i hne
      rw [mul_assoc, inv_mul_cancel₀ (hP1 i hne), mul_one]
  calc (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v g ≤ r)).card
      = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist (v ∘ σ) g ≤ r)).card :=
        pairBall_perm σ v r
    _ = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r
            ∧ hammingDist (fun i => u i * (v ∘ σ) i) g ≤ r)).card :=
        pairBall_scale hu (v ∘ σ) r
    _ = (Finset.univ.filter
          (fun g => hammingDist (0 : ι → F) g ≤ r ∧ hammingDist v' g ≤ r)).card := by
        rw [hv']

end Field

end ArkLib.CodingTheory.ListMoments
