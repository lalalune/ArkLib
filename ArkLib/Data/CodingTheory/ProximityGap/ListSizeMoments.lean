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

end ArkLib.CodingTheory.ListMoments
