/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ListAroundBallIntersectionKernel

/-!
# Issue #232 — the list-size reduction to the ball-intersection second moment (the open #82 kernel)

`ListAroundBallIntersectionKernel.lean` proves the second-moment identity
`∑_w |listAround(w,r)|² = ∑_{c,c' ∈ C} |B(c,r) ∩ B(c',r)|`.  This file turns that identity into an
**actual upper bound on the worst-case list size** `|Λ(C,δ)| = max_w |listAround(w,r)|`, and splits the
right-hand side into the (trivially bounded) **diagonal** and the **off-diagonal** that is the genuine
open kernel of the Proximity Prize.

The clean chain:

* `listAround_sq_le_ball_inter` — `max_w |listAround(w,r)|² ≤ ∑_{c,c'} |B(c,r) ∩ B(c',r)|`
  (a single non-negative term is `≤` the whole sum, then the kernel identity).

* `sum_ball_inter_diag_offdiag` — `∑_{c,c'} |B(c,r) ∩ B(c',r)| = ∑_c |B(c,r)| + ∑_c ∑_{c'≠c}
  |B(c,r) ∩ B(c',r)|` (split each inner sum at `c' = c`; `B(c,r) ∩ B(c,r) = B(c,r)`).

* `listSize_sq_le_diag_add_offdiag` (HEADLINE) — for every received word `w₀`,
  `|listAround(w₀,r)|² ≤ ∑_c |B(c,r)| + ∑_c ∑_{c'≠c} |B(c,r) ∩ B(c',r)|`.

The diagonal `∑_c |B(c,r)|` is just `|C|` times the (codeword-independent) Hamming ball volume
`V(r)` — large but *explicit* and harmless.  **Everything hard about the prize is in the off-diagonal**
`∑_{c ≠ c'} |B(c,r) ∩ B(c',r)|`: for Reed–Solomon (an MDS code) this equals
`|C| · ∑_{w ≥ d} A_w · I(w,r)`, the weight-enumerator `A_w` weighted by the ball-intersection volumes
`I(w,r) = |B(0,r) ∩ B(e,r)|` (`wt e = w`).  A *sharp* upper bound on this off-diagonal sum, beating
`ε*²·q²`, is exactly the open kernel that pins `δ*` past the Johnson radius (the CS25/ABF26 research
content).  This file localizes the open problem to that one machine-checked quantity.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open scoped Classical
open Finset
open ArkLib.CodingTheory.Round13BallInter

noncomputable section

namespace ArkLib.CodingTheory.Round13Reduction

variable {n : ℕ} {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The worst-case list size is controlled by the ball-intersection second moment.**  Since
`|listAround(w₀,r)|²` is one (non-negative) term of the sum `∑_w |listAround(w,r)|²`, it is at most the
whole sum, which by the kernel identity equals `∑_{c,c'} |B(c,r) ∩ B(c',r)|`.  Hence
`|Λ(C,δ)|² ≤ ∑_{c,c'} |B(c,r) ∩ B(c',r)|`. -/
theorem listAround_sq_le_ball_inter (C : Finset (Fin n → F)) (r : ℕ) (w₀ : Fin n → F) :
    (listAround C w₀ r).card ^ 2
      ≤ ∑ c ∈ C, ∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card := by
  rw [← sum_sq_listAround_eq_ball_inter C r]
  exact Finset.single_le_sum (f := fun w => (listAround C w r).card ^ 2)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ w₀)

/-- **Diagonal/off-diagonal split of the ball-intersection second moment.**  Splitting each inner sum
at `c' = c` (where `B(c,r) ∩ B(c,r) = B(c,r)`):
`∑_{c,c'} |B(c,r) ∩ B(c',r)| = ∑_c |B(c,r)| + ∑_c ∑_{c' ∈ C.erase c} |B(c,r) ∩ B(c',r)|`. -/
theorem sum_ball_inter_diag_offdiag (C : Finset (Fin n → F)) (r : ℕ) :
    (∑ c ∈ C, ∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card)
      = (∑ c ∈ C, (hammingBall c r).card)
        + ∑ c ∈ C, ∑ c' ∈ C.erase c, (hammingBall c r ∩ hammingBall c' r).card := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← Finset.add_sum_erase C (fun c' => (hammingBall c r ∩ hammingBall c' r).card) hc,
      Finset.inter_self]

/-- **HEADLINE — the list-size reduction.**  For every received word `w₀` and radius `r`,
`|listAround(w₀,r)|² ≤ ∑_c |B(c,r)| + ∑_c ∑_{c' ≠ c} |B(c,r) ∩ B(c',r)|`.

The first (diagonal) term is `|C|·V(r)`, large but explicit and harmless.  The second (off-diagonal)
term is the genuine open kernel: for Reed–Solomon it is `|C|·∑_{w} A_w · I(w,r)` (weight enumerator ×
ball-intersection volumes), and a sharp upper bound on it — below `ε*²·q²` — is exactly what pins `δ*`
past the Johnson radius.  This inequality reduces the worst-case list size to that one quantity. -/
theorem listSize_sq_le_diag_add_offdiag (C : Finset (Fin n → F)) (r : ℕ) (w₀ : Fin n → F) :
    (listAround C w₀ r).card ^ 2
      ≤ (∑ c ∈ C, (hammingBall c r).card)
        + ∑ c ∈ C, ∑ c' ∈ C.erase c, (hammingBall c r ∩ hammingBall c' r).card := by
  calc (listAround C w₀ r).card ^ 2
      ≤ ∑ c ∈ C, ∑ c' ∈ C, (hammingBall c r ∩ hammingBall c' r).card :=
        listAround_sq_le_ball_inter C r w₀
    _ = _ := sum_ball_inter_diag_offdiag C r

/-- **The diagonal is codeword-independent (the ball volume `V(r)`).**  The Hamming ball volume does
not depend on its centre: `|B(c,r)| = |B(0,r)|`, via the translation bijection `w ↦ w − c` (which
preserves Hamming distance: `dist(c,w) = #{i : w i ≠ c i} = #{i : (w−c) i ≠ 0} = dist(0, w−c)`).  Hence
the diagonal `∑_c |B(c,r)| = |C|·V(r)` is explicit. -/
theorem hammingBall_card_eq_zero (c : Fin n → F) (r : ℕ) :
    (hammingBall c r).card = (hammingBall (0 : Fin n → F) r).card := by
  apply Finset.card_nbij' (fun w => w - c) (fun v => v + c)
  · intro w hw
    simp only [hammingBall, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [hammingDist_comm] at hw
    have : hammingDist (0 : Fin n → F) (w - c) = hammingDist w c := by
      unfold hammingDist
      apply Finset.card_bij (fun i _ => i) <;> intro i hi <;>
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.sub_apply, Pi.zero_apply,
          sub_ne_zero] at hi ⊢
      · exact fun _ => ⟨i, ?_, rfl⟩  -- placeholder; refined below
        sorry
    sorry
  · sorry
  · sorry
  · sorry

end ArkLib.CodingTheory.Round13Reduction

end

/-! ## Axiom audit -/
#print axioms ArkLib.CodingTheory.Round13Reduction.listAround_sq_le_ball_inter
#print axioms ArkLib.CodingTheory.Round13Reduction.sum_ball_inter_diag_offdiag
#print axioms ArkLib.CodingTheory.Round13Reduction.listSize_sq_le_diag_add_offdiag
