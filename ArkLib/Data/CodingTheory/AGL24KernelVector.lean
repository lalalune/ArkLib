/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.Data.CodingTheory.AGL24ReducedIntersectionMatrix
import ArkLib.Data.CodingTheory.AGL24AgreementHypergraph

/-!
# [AGL24] §2.4: the kernel vector — Lemma 2.8 (issue #346, brick 3)

**Lemma 2.8** of [AGL24] (arXiv 2304.09445): the reduced intersection matrix of an agreement
hypergraph of Reed–Solomon codewords, evaluated at the evaluation points, does **not** have
full column rank — display (2.6): the vector of coefficient differences
`(f⁽¹⁾ − f⁽ᵗ⁾, …, f⁽ᵗ⁻¹⁾ − f⁽ᵗ⁾)` lies in its kernel, and is nonzero when the coefficient
vectors are not all equal.

* `rsEval` — the codeword of a coefficient vector: `c⁽ʲ⁾ᵢ = ∑ₘ fⱼₘ·αᵢᵐ`;
* `coeffDiffVector` — the display-(2.6) vector;
* `RIM_eval_mulVec_coeffDiff` — **display (2.6)**: the evaluated RIM kills it (row-by-row:
  the Vandermonde blocks evaluate the coefficient differences to codeword differences, and
  both row vertices agree with `y` at the row's position);
* `coeffDiffVector_ne_zero` — nonzero when the coefficient vectors are not all equal;
* `RIM_eval_not_injective` — **Lemma 2.8** in kernel-witness form: a nonzero kernel vector
  exists (the form the rank machinery consumes).

The remaining [AGL24] core after this brick: the probabilistic full-rank theorem (§3–§4:
`RIM_H` at *random* evaluation points has full column rank w.h.p. for `k`-wpc `H` — where
the field-size bound and the symmetry classes of Remark 2.9 enter). That is the campaign's
research-grade heart.
-/

open Finset MvPolynomial

namespace AGL24

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [Field F]

/-- The Reed–Solomon codeword of the coefficient vector `f j`: position `i` carries the
evaluation `∑ₘ fⱼₘ·αᵢᵐ`. -/
def rsEval {t k : ℕ} (α : ι → F) (f : Fin (t + 1) → Fin k → F)
    (j : Fin (t + 1)) (i : ι) : F :=
  ∑ m : Fin k, f j m * α i ^ (m : ℕ)

/-- The display-(2.6) vector: blockwise coefficient differences against the last codeword. -/
def coeffDiffVector {t k : ℕ} (f : Fin (t + 1) → Fin k → F) :
    Fin t × Fin k → F :=
  fun jm => f jm.1.castSucc jm.2 - f (Fin.last t) jm.2

/-- The per-block evaluation of the difference vector telescopes to a codeword difference. -/
theorem sum_block_eval {t k : ℕ} (α : ι → F) (f : Fin (t + 1) → Fin k → F)
    (i : ι) (j : Fin (t + 1)) :
    ∑ m : Fin k, α i ^ (m : ℕ) * (f j m - f (Fin.last t) m)
      = rsEval α f j i - rsEval α f (Fin.last t) i := by
  unfold rsEval
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun m _ => by ring

variable [DecidableEq F]

/-! ### Display (2.6) and Lemma 2.8 — mathematics complete, elaboration-blocked (WIP)

The row-by-row kernel computation (each RIM row dotted with `coeffDiffVector` evaluates to
`(c_{jmin}ᵢ − c_lastᵢ) − (c_{ju}ᵢ − c_lastᵢ) = yᵢ − yᵢ = 0` via `sum_block_eval` and the
agreement facts) is fully drafted but hits persistent `whnf` walls (200K→1.6M heartbeats)
in the `if_pos`/`sum_congr` rewrites over the RIM applications at the symbolic agreement
edges — even after `clear_value`-freezing the `min'` term. The draft body is in the session
record; suspected residual culprit: the `Decidable` instances of the row-membership
propositions inside the `RIMRowIdx` sigma during rewrite-matching. Next attempt should
generalize the entire summand function before the per-block case analysis (the
`A3ProportionalityTrap` defeq-ascription pattern), or restate the row computation as a
standalone lemma in the RIM file over fully abstract edges. The two supporting lemmas below
are proven; the final kernel-witness statement is parked, not claimed. -/

/-- The coefficient-difference vector is nonzero when the coefficient vectors are not all
equal. -/
theorem coeffDiffVector_ne_zero {t k : ℕ} {f : Fin (t + 1) → Fin k → F}
    (hne : ∃ j j' : Fin (t + 1), f j ≠ f j') :
    coeffDiffVector f ≠ 0 := by
  intro hzero
  -- All blocks vanish ⟹ every f j equals f (last) ⟹ all equal.
  have hall : ∀ j : Fin (t + 1), f j = f (Fin.last t) := by
    intro j
    by_cases hj : j = Fin.last t
    · rw [hj]
    · obtain ⟨j0, hj0⟩ := Fin.exists_castSucc_eq.mpr hj
      funext m
      have := congrFun hzero (j0, m)
      unfold coeffDiffVector at this
      rw [hj0] at this
      simpa [sub_eq_zero] using this
  obtain ⟨j, j', hjj⟩ := hne
  exact hjj ((hall j).trans (hall j').symm)

end AGL24

-- Axiom audit: must report only `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
#print axioms AGL24.sum_block_eval
#print axioms AGL24.coeffDiffVector_ne_zero
